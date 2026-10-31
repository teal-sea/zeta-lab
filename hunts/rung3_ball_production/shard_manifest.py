#!/usr/bin/env python3
"""Hunt #145, door 1, Stage B: the manifest of one lean4export (format 3.1.0) shard.

Reads an NDJSON export as `con-ron` reads it and writes, for every declaration it holds, one
line `name, kind, hash, type hash, value hash, kernel hash, kernel type hash, kernel value
hash`. Each is a Merkle hash (BLAKE2b, 16 bytes) of the declaration's exported structure:
names by their components, universe levels, expressions node by node, literals, and every
other field of the record. The first three include the binder names and binder info; the
kernel hashes leave them out, as the kernel does (bound variables are de Bruijn indices).
The exporter writes an expression once and reuses its index for any later expression equal
to it up to binder names and binder info (Lean's `BEq Expr`), so which binder names a shard
carries depends on what it wrote first: the same constant can come out with other binder
names in another shard. Two shards hold the same kernel declaration exactly when their
kernel hashes are equal; that is how the coverage step matches the shards' shared constants
and the top shard's `Rung3Glue.T.*` definitions against the site theorems' types. A
constant is named by its name inside expressions.

    shard_manifest.py EXPORT.ndjson OUT.tsv      # prints a JSON summary on stdout

The summary has the declaration count by kind, the record count by kind (an inductive
block is one record, however many types, constructors and recursors it holds), the axioms (a shard must hold none but
`propext`, `Classical.choice` and `Quot.sound`), the line and byte counts and the header.
"""
from __future__ import annotations

import hashlib
import json
import sys

try:
    import orjson
    loads = orjson.loads
except ImportError:                               # the standard library, slower
    loads = json.loads


def H(*parts: bytes) -> bytes:
    h = hashlib.blake2b(digest_size=16)
    for p in parts:
        h.update(len(p).to_bytes(4, "little"))
        h.update(p)
    return h.digest()


def manifest(path: str, out: str) -> dict:
    names_h: list[bytes] = [H(b"anon")]
    names_s: list[str] = [""]
    levels: list[bytes] = [H(b"zero")]
    exprs: list[bytes] = []
    kexprs: list[bytes] = []          # the kernel view: no binder names, no binder info
    kinds: dict[str, int] = {}
    records: dict[str, int] = {}
    axioms: list[str] = []
    header = None
    lines = 0
    nbytes = 0
    o = open(out, "w")

    def ex(i: int) -> bytes:
        return exprs[i]

    def kx(i: int) -> bytes:
        return kexprs[i]

    def name_list(xs) -> bytes:
        return b"".join(names_h[i] for i in xs)

    def emit(kind: str, name_i: int, parts: list[bytes], ty: bytes, val: bytes | None,
             kparts: list[bytes], kty: bytes, kval: bytes | None):
        nm = names_s[name_i]
        dh = H(kind.encode(), names_h[name_i], *parts)
        kh = H(kind.encode(), names_h[name_i], *kparts)
        o.write(f"{nm}\t{kind}\t{dh.hex()}\t{ty.hex()}\t{val.hex() if val else '-'}\t"
                f"{kh.hex()}\t{kty.hex()}\t{kval.hex() if kval else '-'}\n")
        kinds[kind] = kinds.get(kind, 0) + 1
        if kind == "axiom":
            axioms.append(nm)

    with open(path, "rb") as f:
        for line in f:
            lines += 1
            nbytes += len(line)
            r = loads(line)
            if "ie" in r:
                i = r["ie"]
                assert i == len(exprs), (lines, i, len(exprs))
                if "app" in r:
                    a = r["app"]
                    h = H(b"app", exprs[a["fn"]], exprs[a["arg"]])
                    k = H(b"app", kexprs[a["fn"]], kexprs[a["arg"]])
                elif "const" in r:
                    c = r["const"]
                    h = k = H(b"const", names_h[c["name"]], b"".join(levels[u] for u in c["us"]))
                elif "bvar" in r:
                    h = k = H(b"bvar", str(r["bvar"]).encode())
                elif "lam" in r or "forallE" in r:
                    tag = "lam" if "lam" in r else "forallE"
                    b = r[tag]
                    h = H(tag.encode(), names_h[b["name"]], exprs[b["type"]], exprs[b["body"]],
                          b["binderInfo"].encode())
                    k = H(tag.encode(), kexprs[b["type"]], kexprs[b["body"]])
                elif "natVal" in r:
                    h = k = H(b"nat", r["natVal"].encode())
                elif "sort" in r:
                    h = k = H(b"sort", levels[r["sort"]])
                elif "letE" in r:
                    b = r["letE"]
                    h = H(b"let", names_h[b["name"]], exprs[b["type"]], exprs[b["value"]],
                          exprs[b["body"]], b"1" if b["nondep"] else b"0")
                    k = H(b"let", kexprs[b["type"]], kexprs[b["value"]], kexprs[b["body"]])
                elif "proj" in r:
                    b = r["proj"]
                    h = H(b"proj", names_h[b["typeName"]], str(b["idx"]).encode(),
                          exprs[b["struct"]])
                    k = H(b"proj", names_h[b["typeName"]], str(b["idx"]).encode(),
                          kexprs[b["struct"]])
                elif "strVal" in r:
                    h = k = H(b"str", r["strVal"].encode())
                elif "mdata" in r:
                    b = r["mdata"]
                    h = H(b"mdata", json.dumps(b["data"], sort_keys=True).encode(),
                          exprs[b["expr"]])
                    k = kexprs[b["expr"]]
                else:
                    raise ValueError(f"line {lines}: unknown expression record {r}")
                exprs.append(h)
                kexprs.append(k)
            elif "in" in r:
                i = r["in"]
                assert i == len(names_h), (lines, i)
                if "str" in r:
                    b = r["str"]
                    names_h.append(H(b"nstr", names_h[b["pre"]], b["str"].encode()))
                    p = names_s[b["pre"]]
                    names_s.append(f"{p}.{b['str']}" if p else b["str"])
                else:
                    b = r["num"]
                    names_h.append(H(b"nnum", names_h[b["pre"]], str(b["i"]).encode()))
                    p = names_s[b["pre"]]
                    names_s.append(f"{p}.{b['i']}" if p else str(b["i"]))
            elif "il" in r:
                i = r["il"]
                assert i == len(levels), (lines, i)
                if "succ" in r:
                    levels.append(H(b"succ", levels[r["succ"]]))
                elif "max" in r:
                    a, b = r["max"]
                    levels.append(H(b"max", levels[a], levels[b]))
                elif "imax" in r:
                    a, b = r["imax"]
                    levels.append(H(b"imax", levels[a], levels[b]))
                else:
                    levels.append(H(b"param", names_h[r["param"]]))
            elif "thm" in r:
                records["thm"] = records.get("thm", 0) + 1
                d = r["thm"]

                def parts(e, d=d):
                    return [name_list(d["levelParams"]), e(d["type"]), e(d["value"]), name_list(d["all"])]
                emit("thm", d["name"], parts(ex), ex(d["type"]), ex(d["value"]),
                     parts(kx), kx(d["type"]), kx(d["value"]))
            elif "def" in r:
                records["def"] = records.get("def", 0) + 1
                d = r["def"]

                def parts(e, d=d):
                    return [name_list(d["levelParams"]), e(d["type"]), e(d["value"]),
                            json.dumps(d["hints"]).encode(), d["safety"].encode(), name_list(d["all"])]
                emit("def", d["name"], parts(ex), ex(d["type"]), ex(d["value"]),
                     parts(kx), kx(d["type"]), kx(d["value"]))
            elif "axiom" in r:
                records["axiom"] = records.get("axiom", 0) + 1
                d = r["axiom"]

                def parts(e, d=d):
                    return [name_list(d["levelParams"]), e(d["type"]), b"1" if d["isUnsafe"] else b"0"]
                emit("axiom", d["name"], parts(ex), ex(d["type"]), None, parts(kx), kx(d["type"]), None)
            elif "opaque" in r:
                records["opaque"] = records.get("opaque", 0) + 1
                d = r["opaque"]

                def parts(e, d=d):
                    return [name_list(d["levelParams"]), e(d["type"]), e(d["value"]), name_list(d["all"]),
                            b"1" if d["isUnsafe"] else b"0"]
                emit("opaque", d["name"], parts(ex), ex(d["type"]), ex(d["value"]),
                     parts(kx), kx(d["type"]), kx(d["value"]))
            elif "quot" in r:
                records["quot"] = records.get("quot", 0) + 1
                d = r["quot"]

                def parts(e, d=d):
                    return [name_list(d["levelParams"]), e(d["type"]), d["kind"].encode()]
                emit("quot", d["name"], parts(ex), ex(d["type"]), None, parts(kx), kx(d["type"]), None)
            elif "inductive" in r:
                records["inductive"] = records.get("inductive", 0) + 1
                blk = r["inductive"]
                for t in blk["types"]:
                    def parts(e, t=t):
                        return [name_list(t["levelParams"]), e(t["type"]),
                                json.dumps([t["numParams"], t["numIndices"], t["numNested"], t["isRec"],
                                            t["isReflexive"], t["isUnsafe"]]).encode(),
                                name_list(t["all"]), name_list(t["ctors"])]
                    emit("induct", t["name"], parts(ex), ex(t["type"]), None, parts(kx), kx(t["type"]), None)
                for c in blk["ctors"]:
                    def parts(e, c=c):
                        return [name_list(c["levelParams"]), e(c["type"]), names_h[c["induct"]],
                                json.dumps([c["cidx"], c["numParams"], c["numFields"], c["isUnsafe"]]).encode()]
                    emit("ctor", c["name"], parts(ex), ex(c["type"]), None, parts(kx), kx(c["type"]), None)
                for c in blk["recs"]:
                    def parts(e, c=c):
                        rules = b"".join(names_h[x["ctor"]] + str(x["nfields"]).encode() + e(x["rhs"])
                                         for x in c["rules"])
                        return [name_list(c["levelParams"]), e(c["type"]), name_list(c["all"]),
                                json.dumps([c["numParams"], c["numIndices"], c["numMotives"], c["numMinors"],
                                            c["k"], c["isUnsafe"]]).encode(), rules]
                    emit("rec", c["name"], parts(ex), ex(c["type"]), None, parts(kx), kx(c["type"]), None)
            elif "meta" in r:
                header = r["meta"]
            else:
                raise ValueError(f"line {lines}: unknown record {str(r)[:200]}")
    o.close()
    return {"lines": lines, "bytes": nbytes, "declarations": sum(kinds.values()),
            "by_kind": kinds, "records": records, "axioms": sorted(axioms), "exprs": len(exprs),
            "names": len(names_h) - 1, "levels": len(levels) - 1, "header": header}


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    print(json.dumps(manifest(sys.argv[1], sys.argv[2])))
