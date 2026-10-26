"""exact_gram/: the exact-Gram rebuild of Delta_T in balls (PREREG s1, amendment 1; BOUNDS.md).

Pipeline, per run request (RUN_REQUEST.json, or a dict in tests):

  gate      two_adic's ta_data.validate on the local data at 2; only zeta's (alpha = 1) is built
  modes     kernel/'s prolate data as exact decimals (bounds.prolate_modes)
  gram      a provider returning (G_z, G_b) as ball matrices; 'exact' is bounds.gram_z and
            bounds.gram_b (P4; G_b raises until its regions B and C exist, PREREG row D0);
            'toy-region-a' (G_b from region A only) is for tests and is never a bound
  blocks    the trapezoid nodes s_k = k Delta, 0 <= k <= S'/Delta, in blocks of `block` nodes;
            per block: hats (P1, P2 radii added), rho for both families, window sums for
            every (c, N), at s and -s (rho(-s) = rho(s))
  shards    contiguous block ranges; after every block one checkpoint per shard (guard.py),
            the key re-read first; every `replay_every`-th block is recomputed at
            `replay_prec` bits and its hats must intersect the production hats
  assemble  sum of the shards in order; Delta_T = M_inf - M_S per (c, N) as balls, and
            eps_q = ||radius||_F + P3 (aliasing and the tail beyond S')

    <venv python> rebuild.py run --request RUN_REQUEST.json --shard 3 --shards 7 --out DIR
    <venv python> rebuild.py assemble --request RUN_REQUEST.json --shards 7 --out DIR

Nothing in this module states a number about Delta_T; the toy tests run it on 3 modes.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys

from flint import acb, acb_mat, arb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
TWO_ADIC = os.path.normpath(os.path.join(HERE, "..", "two_adic"))
for p in (HERE, TWO_ADIC):
    if p not in sys.path:
        sys.path.insert(0, p)

import bounds as B  # noqa: E402
import guard as GD  # noqa: E402

PROD_PREC = 133


class ReplayMismatch(RuntimeError):
    """A replayed block's hats do not intersect the production hats: a defect, count nothing."""


class NotABound(RuntimeError):
    """The run used a provider that is not a bound; its output is never read as one."""


# --------------------------------------------------------------------------
# gate
# --------------------------------------------------------------------------


def gate(local_data):
    """two_adic's validation; the rebuild builds zeta only (alpha = 1 at 2)."""
    import ta_data as D

    ld = D.validate(local_data, degree=1) if local_data[0] == "tower" else D.validate(local_data)
    if tuple(ld.alphas) != (1,):
        raise D.NonUnitaryLocalData(f"exact_gram builds zeta only (alpha = 1); got {ld.alphas}")
    return ld


# --------------------------------------------------------------------------
# hats
# --------------------------------------------------------------------------


def w_panel_ends(Kmax, s_max):
    """Exact float endpoints [e_0 = 1, e_1, ..., 2^Kmax] of two_adic's w panels."""
    return B.w_panel_ends(Kmax, s_max)


class ModeTable:
    """zeta_n(w) * w_j * w^{-1/2} on every Gauss node of every w panel, grouped by dyadic level
    (in memory). DiskModeTable is the same table streamed from disk."""

    def __init__(self, modes, Kmax, s_max, per_panel=12, chunk=2048):
        self.modes, self.Kmax, self.per_panel, self.s_max = modes, Kmax, per_panel, s_max
        self.levels = [([], []) for _ in range(Kmax)]
        for lev, logs, F in table_rows(modes, Kmax, s_max, per_panel, chunk):
            self.levels[lev][0].extend(logs)
            self.levels[lev][1].append(F)
        self.F = []
        for lev in range(Kmax):
            mats = self.levels[lev][1]
            self.F.append(_vstack(mats) if mats else None)

    def chunks(self):
        for k in range(self.Kmax):
            if self.levels[k][0]:
                yield k, self.levels[k][0], self.F[k]

    radii = None  # set below (shared with DiskModeTable and StreamTable)


class StreamTable:
    """The table generated chunk by chunk and never stored (the dps-60 replay at 280 modes)."""

    def __init__(self, modes, Kmax, s_max, per_panel=12, chunk=2048):
        self.modes, self.Kmax, self.per_panel, self.s_max, self.chunk = modes, Kmax, per_panel, s_max, chunk

    def chunks(self):
        yield from table_rows(self.modes, self.Kmax, self.s_max, self.per_panel, self.chunk)


def _vstack(mats):
    rows = []
    for m in mats:
        rows.extend([[m[i, j] for j in range(m.ncols())] for i in range(m.nrows())])
    return arb_mat(rows)


def table_rows(modes, Kmax, s_max, per_panel=12, chunk=2048):
    """Yield (level, [log w], arb_mat chunk x nvec of zeta_n(w) * weight / sqrt(w)) over the w panels,
    one ball matrix product per chunk of nodes (BOUNDS.md s1)."""
    ends = w_panel_ends(Kmax, s_max)
    rule = B.gauss_rule(per_panel)
    buf = {}
    for a, b in zip(ends[:-1], ends[1:]):
        lev = int(math.floor(math.log2(a) + 1e-12))
        half = (arb(b) - arb(a)) / 2
        for j in range(per_panel):
            buf.setdefault(lev, []).append((B.point(a, b, per_panel, j), rule[j][1] * half))
        if len(buf[lev]) >= chunk:
            yield _emit(modes, lev, buf.pop(lev))
    for lev in sorted(buf):
        yield _emit(modes, lev, buf[lev])


def _emit(modes, lev, items):
    pts = [p for p, _ in items]
    Z = B.zeta_values(modes, pts)
    logs, scale = [], []
    for p, wt in items:
        w = p()
        logs.append(w.log())
        scale.append(wt / w.sqrt())
    S = arb_mat([[scale[i] if i == j else arb(0) for j in range(len(items))] for i in range(len(items))])
    return lev, logs, S * Z


class DiskModeTable:
    """The mode table on disk (one file per level, fixed-width balls), streamed in chunks: what lets
    four processes share a 16 GB runner (RUNS.md s4, s9). Built once per job by build()."""

    REC = 40  # bytes per ball: mantissa 24 (signed), exponent 4, radius mantissa 8, radius exponent 4

    def __init__(self, path, modes, Kmax, s_max, per_panel=12, chunk=2048, verify=True):
        self.path, self.modes, self.Kmax, self.per_panel, self.s_max, self.chunk = path, modes, Kmax, per_panel, s_max, chunk
        meta = os.path.join(path, "meta.json")
        if not os.path.exists(meta):
            raise FileNotFoundError(f"no mode table at {path}: build it first")
        m = json.load(open(meta))
        want = {"nvec": modes.nvec, "Kmax": Kmax, "s_max": s_max, "per_panel": per_panel, "prec": ctx.prec}
        if {k: m[k] for k in want} != want:
            raise ValueError(f"mode table {m} does not match {want}")
        self.counts = m["counts"]
        if verify:  # fail closed on any byte changed since build (a ball cannot see a flipped low bit)
            for f, h in m["sha256"].items():
                if _sha256(os.path.join(path, f)) != h:
                    raise ValueError(f"mode table {f}: sha256 mismatch")

    @classmethod
    def build(cls, path, modes, Kmax, s_max, per_panel=12, chunk=2048):
        import struct  # noqa: F401  (used by _pack)

        os.makedirs(path, exist_ok=True)
        counts = [0] * Kmax
        fhs = {}
        for lev, logs, F in table_rows(modes, Kmax, s_max, per_panel, chunk):
            if lev not in fhs:  # open once: a second "wb" open would truncate what the first chunk wrote
                fhs[lev] = open(os.path.join(path, f"level{lev:02d}.bin"), "wb")
            fh = fhs[lev]
            for i, lw in enumerate(logs):
                fh.write(_pack(lw) + b"".join(_pack(F[i, j]) for j in range(modes.nvec)))
            counts[lev] += len(logs)
        for fh in fhs.values():
            fh.close()
        sha = {f"level{lev:02d}.bin": _sha256(os.path.join(path, f"level{lev:02d}.bin")) for lev in fhs}
        with open(os.path.join(path, "meta.json"), "w") as fh:
            json.dump({"nvec": modes.nvec, "Kmax": Kmax, "s_max": s_max, "per_panel": per_panel,
                       "prec": ctx.prec, "counts": counts, "sha256": sha}, fh)
        return cls(path, modes, Kmax, s_max, per_panel, chunk)

    def disk_bytes(self):
        return sum(os.path.getsize(os.path.join(self.path, f)) for f in os.listdir(self.path))

    def chunks(self):
        for k in range(self.Kmax):
            for logs, F in self._level(k):
                yield k, logs, F

    def _level(self, k):
        n = self.counts[k]
        if not n:
            return
        nv = self.modes.nvec
        row = self.REC * (nv + 1)
        with open(os.path.join(self.path, f"level{k:02d}.bin"), "rb") as fh:
            for i0 in range(0, n, self.chunk):
                cnt = min(self.chunk, n - i0)
                raw = fh.read(cnt * row)
                logs, rows = [], []
                for i in range(cnt):
                    rec = raw[i * row:(i + 1) * row]
                    vals = [_unpack(rec[q * self.REC:(q + 1) * self.REC]) for q in range(nv + 1)]
                    logs.append(vals[0])
                    rows.append(vals[1:])
                yield logs, arb_mat(rows)


def _sha256(path):
    import hashlib

    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for blk in iter(lambda: fh.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def _pack(x):
    import struct

    mm, me = x.mid().man_exp()
    rm, re_ = x.rad().man_exp()
    return int(mm).to_bytes(24, "little", signed=True) + struct.pack("<iQi", int(me), int(rm), int(re_))


def _unpack(b):
    import struct

    from flint import arf

    mm = int.from_bytes(b[:24], "little", signed=True)
    me, rm, re_ = struct.unpack("<iQi", b[24:40])
    return arb(arf((mm, me)), arf((rm, re_)))


def _radii(self, M, J, kb):
    """P1 and P2 radii for every mode, valid for every |s| <= s_max (computed once)."""
    key = (M, J, kb)
    if getattr(self, "_radii_key", None) != key:
        md, K, S = self.modes, self.Kmax, max(self.s_max, 1.0)
        e3 = B.e3_hat_bound(K, S, self.per_panel)
        q2 = 1 / (1 - arb(2) ** (-arb(0.5)))
        rz, rb = [], []
        for n in range(md.nvec):
            e4 = B.e4_tail_bound(md, n, 2.0**K, S, M, J)
            ek = sum((arb(2) ** (-arb(k) / 2) * B.e4_tail_bound(md, n, 2.0**k, S, M, J) for k in range(K + 1, kb)), arb(0))
            rz.append(md.norm[n] * e3 + e4)
            rb.append((md.norm[n] * e3 + e4) * q2 + ek + B.b_kseries_tail(md, n, kb))
        self._radii, self._radii_key = (rz, rb), key
    return self._radii


ModeTable.radii = _radii
DiskModeTable.radii = _radii
StreamTable.radii = _radii


def _tail_T(modes, W, s, M, J):
    """T_n(W; s) for every n (expansion of P2, value only), list of acb."""
    tp = B.two_pi()
    W = arb(W)
    out = [acb(0)] * modes.nvec
    for m in range(M):
        beta = acb(-(m + 1) - arb(0.5), -s)
        c = (-1) ** m * tp ** (-(m + 1))
        A = []
        for a in (tp, -tp):
            ia = acb(0, a)
            tot, fall = acb(0), acb(1)
            for j in range(J):
                tot += (-1) ** j * fall * acb(W) ** (beta - j) / ia ** (j + 1)
                fall *= beta - j
            A.append(-(ia * W).exp() * tot)
        g = c * (acb(0, 1) ** (-(m + 1)) * A[0] + acb(0, -1) ** (-(m + 1)) * A[1])
        out = [o + g * modes.norm[n] * modes.deriv_at_1(n, m) for n, o in enumerate(out)]
    return out


def _pm(r):
    r = arb(arb(r).upper())
    return arb(0).union(r).union(-r)


def hats_block(table, s_list, M, J, kb, fault=None):
    """(zeta^, b^) as acb_mat (nvec x len(s_list)) with the P1 and P2 radii added (BOUNDS.md s1, s2)."""
    md, K = table.modes, table.Kmax
    ns, nv = len(s_list), md.nvec
    acc = {k: [arb_mat(ns, nv), arb_mat(ns, nv)] for k in range(K)}
    for k, logs, Fk in table.chunks():
        cs = [[(s * l).sin_cos() for l in logs] for s in s_list]
        Cm = arb_mat([[x[1] for x in row] for row in cs])
        Sm = arb_mat([[x[0] for x in row] for row in cs])
        acc[k][0] += Cm * Fk
        acc[k][1] += Sm * Fk  # zeta^ partial = C F - i S F
    lev = [tuple(acc[k]) for k in range(K)]
    if max(abs(float(s.mid())) for s in s_list) > table.s_max:
        raise ValueError("hats_block: s beyond the table's s_max (its panels and radii)")
    rad_z, rad_b = table.radii(M, J, kb)
    Z = acb_mat(nv, ns)
    Bh = acb_mat(nv, ns)
    for i, s in enumerate(s_list):
        tail = _tail_T(md, 2.0**K, s, M, J)
        r = (acb(0, s * arb(2).log())).exp() / arb(2).sqrt()
        tails_k = [_tail_T(md, 2.0**k, s, M, J) for k in range(K + 1, kb)]
        for n in range(nv):
            T = tail[n]
            Tk = []
            for k in reversed(range(K)):
                T = T + acb(lev[k][0][i, n], -lev[k][1][i, n])
                Tk.append(T)
            Tk.reverse()  # Tk[k] = T(2^k)
            zh = Tk[0] + acb(_pm(rad_z[n]), _pm(rad_z[n]))
            # b^ = sum_{k < K} r^k T(2^k) + r^K T(2^K) + sum_{K < k < kb} r^k T(2^k) + tail beyond kb
            bh = sum((r**k * Tk[k] for k in range(K)), acb(0)) + r**K * tail[n]
            bh += sum((r**k * tails_k[k - K - 1][n] for k in range(K + 1, kb)), acb(0))
            bh += acb(_pm(rad_b[n]), _pm(rad_b[n]))
            if fault == "hat" and i == 0 and n == 0:
                zh += acb(arb(1e-6))  # planted: far outside every radius
            Z[n, i], Bh[n, i] = zh, bh
    return Z, Bh


# --------------------------------------------------------------------------
# rho and window sums
# --------------------------------------------------------------------------


def rho(H, Ginv):
    """rho(s) = Re(w^H G^-1 w) per column s of H (nvec x ns)."""
    Y = acb_mat(Ginv) * H
    nv, ns = H.nrows(), H.ncols()
    return [sum(((H[i, k].conjugate() * Y[i, k]).real for i in range(nv)), arb(0)) for k in range(ns)]


def window_hat(L, N, s):
    """V^_n(s), n = -N..N (two_adic/ta_mellin.window_hat, in balls)."""
    out = []
    for n in range(-N, N + 1):
        if n == 0 and s == 0:
            out.append(L.sqrt() + acb(0))  # the limit k -> 0: L / sqrt(L)
            continue
        k = B.two_pi() * n / L - s
        val = (acb(0, s * L / 2)).exp() * ((acb(0, k * L)).exp() - 1) / acb(0, k)
        out.append(val / L.sqrt())
    return out


def c_exact(c):
    """The cell c as an exact rational ball (c = "2.9" is 29/10, never the ball arb("2.9"))."""
    from fractions import Fraction

    f = Fraction(str(c))
    return arb(f.numerator) / f.denominator


def window_sums(rz, rb, s_list, weights, cells):
    """{(c, N): (M_inf, M_S)} partial sums over the block, at s and -s."""
    out = {}
    for c, N in cells:
        L = c_exact(c).log()
        n = 2 * N + 1
        Mi, Ms = acb_mat(n, n), acb_mat(n, n)
        for s, w, a, b in zip(s_list, weights, rz, rb):
            for sg in ((1,) if s == 0 else (1, -1)):
                V = window_hat(L, N, sg * s)
                for p in range(n):
                    cp = V[p].conjugate()
                    for q in range(n):
                        t = cp * V[q] * w / B.two_pi()
                        Mi[p, q] += t * a
                        Ms[p, q] += t * b
        out[(c, N)] = (Mi, Ms)
    return out


# --------------------------------------------------------------------------
# providers, shards, checkpoints
# --------------------------------------------------------------------------


def provider(name, modes, Kmax, req=None):
    req = req or {}
    if name == "exact":
        tgt = arb(10) ** (-int(req.get("gram_target_exp", 20)))
        Gb, _ = B.gram_b(modes, Kmax, target=tgt, R=int(req.get("gram_R", 120)))
        return B.gram_z(modes, Kmax), Gb, True
    if name == "toy-region-a":
        return B.gram_z(modes, Kmax), B.gram_b_region_a(modes, Kmax), False
    raise ValueError(f"unknown Gram provider {name!r}")


def _gram_key(req):
    return {k: req.get(k) for k in ("nvec", "dps", "Kmax", "gram", "gram_target_exp", "gram_R", "prec")}


def _mat_dump(G):
    return [[[str(G[i, j].mid()), str(G[i, j].rad())] for j in range(G.ncols())] for i in range(G.nrows())]


def _mat_load(rows):
    return arb_mat([[arb(a, b) for a, b in r] for r in rows])


def gram_part(req, outdir, part, nparts):
    """One part of G_b (and G_z with part 0), written to gram_part{part:02d}of{nparts:02d}.json."""
    old = ctx.prec
    ctx.prec = req.get("prec", PROD_PREC)
    try:
        gate(tuple(req["local_data"]) if isinstance(req["local_data"], list) else req["local_data"])
        if req["gram"] != "exact":
            raise NotABound("gram parts are for the exact provider")
        modes = B.prolate_modes(req["nvec"], req.get("dps", 40))
        tgt = arb(10) ** (-int(req.get("gram_target_exp", 20)))
        Gb, info = B.gram_b(modes, req["Kmax"], target=tgt, R=int(req.get("gram_R", 120)), part=part, nparts=nparts)
        body = {"request": _gram_key(req), "Gb_part": _mat_dump(Gb), "info": info}
        if part == 0:
            body["Gz"] = _mat_dump(B.gram_z(modes, req["Kmax"]))
        os.makedirs(outdir, exist_ok=True)
        with open(os.path.join(outdir, f"gram_part{part:02d}of{nparts:02d}.json"), "w") as fh:
            json.dump(body, fh)
    finally:
        ctx.prec = old


def merge_gram(req, outdir, nparts):
    """gram.json from the parts; refuses a missing part or a part from another request or plan."""
    old = ctx.prec
    ctx.prec = req.get("prec", PROD_PREC)
    try:
        parts, Gz = [], None
        for p in range(nparts):
            body = json.load(open(os.path.join(outdir, f"gram_part{p:02d}of{nparts:02d}.json")))
            if body["request"] != _gram_key(req):
                raise ValueError(f"gram part {p} is from another request")
            parts.append((_mat_load(body["Gb_part"]), body["info"]))
            if p == 0:
                Gz = _mat_load(body["Gz"])
        Gb = B.gram_b_merge(parts)
        with open(os.path.join(outdir, "gram.json"), "w") as fh:
            json.dump({"request": _gram_key(req), "Gz": _mat_dump(Gz), "Gb": _mat_dump(Gb), "is_bound": True,
                       "plan": parts[0][1]}, fh)
    finally:
        ctx.prec = old


def prepare(req, outdir, gram=True, table=True):
    """The Gram matrices (P4; once per run) and the disk-backed mode table (once per job), for every
    worker to load. Returns the table's bytes on disk (0 if not built here)."""
    old = ctx.prec
    ctx.prec = req.get("prec", PROD_PREC)
    try:
        gate(tuple(req["local_data"]) if isinstance(req["local_data"], list) else req["local_data"])
        modes = B.prolate_modes(req["nvec"], req.get("dps", 40))
        os.makedirs(outdir, exist_ok=True)
        if gram:
            Gz, Gb, is_bound = provider(req["gram"], modes, req["Kmax"], req)
            with open(os.path.join(outdir, "gram.json"), "w") as fh:
                json.dump({"request": _gram_key(req), "Gz": _mat_dump(Gz), "Gb": _mat_dump(Gb), "is_bound": is_bound}, fh)
        if table:
            return DiskModeTable.build(os.path.join(outdir, "table"), modes, req["Kmax"], req["S_prime"]).disk_bytes()
        return 0
    finally:
        ctx.prec = old


def s_nodes(req):
    d = arb(req["delta_num"]) / req["delta_den"]
    n = int(req["S_prime"] * req["delta_den"] / req["delta_num"])
    return [arb(k) * d for k in range(n + 1)], d


def blocks(req):
    s, _ = s_nodes(req)
    b = req["block"]
    return [list(range(i, min(i + b, len(s)))) for i in range(0, len(s), b)]


def shard_range(nblocks, shard, shards):
    per = math.ceil(nblocks / shards)
    return range(shard * per, min((shard + 1) * per, nblocks))


def _ser(m):
    return [[[str(m[i, j].real.mid()), str(m[i, j].real.rad()), str(m[i, j].imag.mid()), str(m[i, j].imag.rad())]
             for j in range(m.ncols())] for i in range(m.nrows())]


def _deser(rows):
    return acb_mat([[acb(arb(a, b), arb(c, d)) for a, b, c, d in r] for r in rows])


def _cells(req):
    return [(c, N) for c in req["cells"] for N in req["Ns"]]


def setup(req):
    gate(tuple(req["local_data"]) if isinstance(req["local_data"], list) else req["local_data"])
    modes = B.prolate_modes(req["nvec"], req.get("dps", 40))
    gfile = os.path.join(req["prepared"], "gram.json") if req.get("prepared") else None
    if gfile and os.path.exists(gfile):
        g = json.load(open(gfile))
        if g["request"] != _gram_key(req):
            raise ValueError("prepared Gram does not match this request")
        Gz, Gb, is_bound = _mat_load(g["Gz"]), _mat_load(g["Gb"]), g["is_bound"]
    else:
        Gz, Gb, is_bound = provider(req["gram"], modes, req["Kmax"], req)
    if req.get("prepared"):
        table = DiskModeTable(os.path.join(req["prepared"], "table"), modes, req["Kmax"], req["S_prime"])
    else:
        table = ModeTable(modes, req["Kmax"], req["S_prime"])
    Giz, Gib = Gz.inv(), Gb.inv()
    Cz = [modes.C(n) for n in range(modes.nvec)]
    q5 = 1 / (1 - arb(2) ** (-arb(5) / 6))
    Cb = [c * q5 for c in Cz]
    absm = lambda G: [[abs(G[i, j]) for j in range(G.ncols())] for i in range(G.nrows())]
    weights = (B.alias_weight(absm(Giz), Cz), B.alias_weight(absm(Gib), Cb))
    return modes, (Giz, Gib), is_bound, table, weights


def run_shard(req, shard, shards, outdir, key_fn, fault=None, state=None, max_blocks=None):
    """Compute (or resume) one shard; the key is read before every block. Returns the checkpoint payload.
    max_blocks: stop after that many new blocks (calibration). Each block's wall time is recorded."""
    import time
    old = ctx.prec
    ctx.prec = req.get("prec", PROD_PREC)
    try:
        if state is None:
            state = setup(req)
        modes, (Giz, Gib), is_bound, table, weights = state
        s_all, d = s_nodes(req)
        tag = f"shard{shard:02d}of{shards:02d}"
        bl = blocks(req)
        rng = list(shard_range(len(bl), shard, shards))
        k0 = key_fn()
        payload = None
        last = rng[0] - 1
        for bi in reversed(rng):
            payload = GD.load_block(outdir, tag, bi, k0)
            if payload is not None:
                last = bi
                break
        sums = {k: tuple(_deser(m) for m in v) for k, v in payload["sums"].items()} if payload else None
        mass = [arb(a, b) for a, b in payload["mass"]] if payload else [arb(0), arb(0)]
        timing = list(payload["block_seconds"]) if payload else []
        done = 0
        for bi in rng:
            if bi <= last:
                continue
            if max_blocks is not None and done >= max_blocks:
                break
            t0 = time.perf_counter()
            k = key_fn()
            if k["rebuild_digest"] != k0["rebuild_digest"] or k["ts_inputs_digest"] != k0["ts_inputs_digest"]:
                raise GD.GuardRefused("key moved during the shard")
            idx = bl[bi]
            ss = [s_all[i] for i in idx]
            ws = [d for _ in idx]  # trapezoid on R: k = 0 once, s and -s (k >= 1) each with weight d
            Z, Bh = hats_block(table, ss, req["M"], req["J"], req["kb"], fault=fault)
            if req.get("replay_every") and bi % req["replay_every"] == 0:
                replay_check(req, modes, ss, Z, Bh)
            rz, rb = rho(Z, Giz), rho(Bh, Gib)
            for s, w, a, b in zip(ss, ws, rz, rb):  # (Delta/2pi) sum over +-s of rho: the inner mass (BOUNDS s3.3)
                f = (1 if s == 0 else 2) * w / B.two_pi()
                mass = [mass[0] + f * a, mass[1] + f * b]
            part = window_sums(rz, rb, ss, ws, _cells(req))
            key_s = {f"{c}|{N}": v for (c, N), v in part.items()}
            if sums is None:
                sums = key_s
            else:
                sums = {kk: (sums[kk][0] + v[0], sums[kk][1] + v[1]) for kk, v in key_s.items()}
            timing.append([bi, time.perf_counter() - t0])
            payload = {"last_block": bi, "first_block": rng[0], "is_bound": is_bound,
                       "sums": {kk: [_ser(v[0]), _ser(v[1])] for kk, v in sums.items()},
                       "mass": [[str(m.mid()), str(m.rad())] for m in mass],
                       "alias_weights": [[str(w.mid()), str(w.rad())] for w in weights],
                       "block_seconds": timing}
            GD.save_block(outdir, tag, bi, k, payload)
            done += 1
        return payload
    finally:
        ctx.prec = old


def replay_check(req, modes, ss, Z, Bh):
    old = ctx.prec
    ctx.prec = req.get("replay_prec", 200)
    try:
        t2 = StreamTable(modes, req["Kmax"], req["S_prime"])
        Z2, B2 = hats_block(t2, [arb(s.mid()) if s.rad() == 0 else s for s in ss], req["M"], req["J"], req["kb"])
    finally:
        ctx.prec = old
    for M1, M2, name in ((Z, Z2, "zeta"), (Bh, B2, "b")):
        for i in range(M1.nrows()):
            for j in range(M1.ncols()):
                if not M1[i, j].overlaps(M2[i, j]):
                    raise ReplayMismatch(f"{name}^ mode {i}, node {j}: {M1[i, j]} vs {M2[i, j]}")


def assemble(req, shards, outdir, key_fn):
    """Delta_T per (c, N) as acb_mat and eps_q; refuses a missing or short shard."""
    k = key_fn()
    bl = blocks(req)
    total = None
    is_bound = True
    mass = [arb(0), arb(0)]
    weights = None
    for sh in range(shards):
        rng = shard_range(len(bl), sh, shards)
        if len(rng) == 0:
            continue
        pay = GD.load_block(outdir, f"shard{sh:02d}of{shards:02d}", rng[-1], k)
        if pay is None or pay["last_block"] != rng[-1] or pay["first_block"] != rng[0]:
            raise GD.GuardRefused(f"shard {sh} missing or incomplete")
        is_bound = is_bound and pay["is_bound"]
        mass = [m + arb(a, b) for m, (a, b) in zip(mass, pay["mass"])]
        weights = [arb(a, b) for a, b in pay["alias_weights"]]
        part = {kk: tuple(_deser(m) for m in v) for kk, v in pay["sums"].items()}
        total = part if total is None else {kk: (total[kk][0] + v[0], total[kk][1] + v[1]) for kk, v in part.items()}
    out = {}
    for kk, (Mi, Ms) in total.items():
        D = Mi - Ms
        D = (D + D.conjugate().transpose()) * acb(0.5)
        rad = arb(0)
        for i in range(D.nrows()):
            for j in range(D.ncols()):
                rad += D[i, j].real.rad() ** 2
        c, N = kk.split("|")
        N = int(N)
        L = c_exact(c).log()
        d = arb(req["delta_num"]) / req["delta_den"]
        alias = (2 * N + 1) * (B.p3_alias_entry(weights[0], L, d) + B.p3_alias_entry(weights[1], L, d))
        # a posteriori tail beyond S' (BOUNDS s3.3): (Delta/2pi) sum over all k of rho = nvec + alias, rho >= 0
        tails = [req["nvec"] + B.p3_alias_rho(w, d) - m for w, m in zip(weights, mass)]
        tail = B.kappa(L, N, req["S_prime"]) * max(tails[0].upper(), tails[1].upper())
        eps_q = rad.sqrt() + alias + tail
        out[kk] = {"delta_T": D, "radius_F": rad.sqrt(), "p3_alias": alias, "tail_mass": tails,
                   "e1_aposteriori": tail, "eps_q": eps_q, "is_bound": is_bound}
    if not is_bound:
        out["_reading"] = "PREREG row D0: a provider that is not a bound was used"
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["prepare", "gram-part", "merge-gram", "run", "assemble"])
    ap.add_argument("--part", type=int, default=0)
    ap.add_argument("--parts", type=int, default=1)
    ap.add_argument("--request", required=True)
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--shards", type=int, default=1)
    ap.add_argument("--out", required=True)
    ap.add_argument("--max-blocks", type=int, default=None)
    ap.add_argument("--gram-only", action="store_true")
    ap.add_argument("--table-only", action="store_true")
    a = ap.parse_args(argv)
    req = json.load(open(a.request))
    if req["gram"] != "exact":
        raise NotABound("production runs use the exact Gram provider only")
    if a.cmd == "gram-part":
        GD.key()
        f = os.path.join(req["prepared"], f"gram_part{a.part:02d}of{a.parts:02d}.json")
        if os.path.exists(f) and json.load(open(f))["request"] == _gram_key(req):
            print(f"part {a.part} already done (resumed)")
        else:
            gram_part(req, req["prepared"], a.part, a.parts)
    elif a.cmd == "merge-gram":
        merge_gram(req, req["prepared"], a.parts)
    elif a.cmd == "prepare":
        GD.key()
        nbytes = prepare(req, req["prepared"], gram=not a.table_only, table=not a.gram_only)
        print(json.dumps({"table_disk_bytes": nbytes}))
    elif a.cmd == "run":
        run_shard(req, a.shard, a.shards, a.out, GD.key, max_blocks=a.max_blocks)
    else:
        res = assemble(req, a.shards, a.out, GD.key)
        print(json.dumps({k: {"radius_F": str(v["radius_F"]), "eps_q": str(v["eps_q"])}
                          for k, v in res.items() if not k.startswith("_")}))


if __name__ == "__main__":
    main()
