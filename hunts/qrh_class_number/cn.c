/* cn.c: every negative fundamental discriminant D with lo <= |D| <= hi and
 * h(D) <= H, with its exact class number.
 *
 * Usage:  cn lo hi H out.txt [seg]
 *
 * Output lines "n h" (n = |D|), then a final line "# stats ..." with counts.
 *
 * Method (RESULTS.md section 5).  For a fundamental D = -n every form of
 * discriminant D is primitive, so h(D) is the number of reduced forms
 * (a, b, c): |b| <= a <= c, b >= 0 if |b| = a or a = c.  For a < sqrt(n)/2
 * the number of reduced forms with first coefficient a equals
 *     r(a) = #{ b mod 2a : b^2 = D mod 4a },
 * multiplicative with r(p^k) = 1 + chi_D(p) for p not dividing D, r(p) = 1
 * and r(p^k) = 0 (k >= 2) for p | D.  Hence the lower bound
 *     h(D) >= 1 + sum_{p prime, 4p^2 < n} (1 + chi_D(p)),
 * which is applied as a sieve (streamed over all n in a segment, then per
 * survivor).  Survivors get the exact count of reduced forms, stopping as
 * soon as the count exceeds H.  Everything is integer arithmetic.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

typedef uint64_t u64;
typedef int64_t i64;
typedef uint32_t u32;

static u32 *primes; static u32 nprimes;
static u32 *spf; static u32 spf_lim;

static u64 isqrt64(u64 n) {
    u64 r = (u64)sqrtl((long double)n);
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

static void make_primes(u32 lim) {
    char *c = calloc(lim + 1, 1);
    nprimes = 0;
    primes = malloc(sizeof(u32) * (lim / 2 + 10));
    for (u32 i = 2; i <= lim; i++) {
        if (!c[i]) {
            primes[nprimes++] = i;
            for (u64 j = (u64)i * i; j <= lim; j += i) c[j] = 1;
        }
    }
    free(c);
}

static void make_spf(u32 lim) {
    spf_lim = lim;
    spf = calloc(lim + 1, sizeof(u32));
    for (u32 i = 2; i <= lim; i++) if (!spf[i]) {
        for (u64 j = i; j <= lim; j += i) if (!spf[j]) spf[j] = i;
    }
}

/* Jacobi symbol (a / m), m odd positive. */
static int jacobi(u64 a, u64 m) {
    int t = 1;
    a %= m;
    while (a) {
        while (!(a & 1)) {
            a >>= 1;
            u64 r = m & 7;
            if (r == 3 || r == 5) t = -t;
        }
        u64 tmp = a; a = m; m = tmp;
        if ((a & 3) == 3 && (m & 3) == 3) t = -t;
        a %= m;
    }
    return m == 1 ? t : 0;
}

/* Kronecker symbol chi_D(p) for D = -n fundamental, p prime. */
static int chi(u64 n, u32 p) {
    if (p == 2) {
        if (!(n & 1)) return 0;
        return ((n & 7) == 7) ? 1 : -1;      /* D = -n = 1 mod 8 iff n = 7 mod 8 */
    }
    u64 r = n % p;
    if (r == 0) return 0;
    return jacobi(p - r, p);                  /* (-n / p) */
}

/* ------------------------------------------------ exact class numbers */

/* Reference version: brute force over b for the top range of a.
 * Kept as an internal cross-check (CN_CHECK=1 compares it with exact_h). */
static int *chi_cache; static u32 *chi_stamp; static u32 stamp_now;

static inline int chi_c(u64 n, u32 p) {
    if (chi_stamp[p] != stamp_now) { chi_stamp[p] = stamp_now; chi_cache[p] = chi(n, p); }
    return chi_cache[p];
}

static u64 r_of(u64 n, u32 a) {
    u64 r = 1;
    while (a > 1) {
        u32 p = spf[a], k = 0;
        while (a % p == 0) { a /= p; k++; }
        int c = chi_c(n, p);
        if (c < 0) return 0;
        if (c == 0) { if (k >= 2) return 0; }
        else r *= 2;
    }
    return r;
}

static long exact_h_slow(u64 n, long H) {
    stamp_now++;
    long h = 0;
    u64 a;
    for (a = 1; 4 * a * a < n; a++) {
        h += (long)r_of(n, (u32)a);
        if (h > H) return H + 1;
    }
    for (; 3 * a * a <= n; a++) {
        if (r_of(n, (u32)a) == 0) continue;
        u64 m = 4 * a;
        u64 b = n & 1;                       /* b = n mod 2 */
        u64 v = (b * b + n) % m;
        for (; b <= a; b += 2) {
            if (v == 0) {
                u64 c = (b * b + n) / m;
                if (c >= a) h += (b == 0 || b == a) ? 1 : (c > a ? 2 : 1);
            }
            v += 4 * b + 4;
            while (v >= m) v -= m;
        }
        if (h > H) return H + 1;
    }
    return h;
}

/* Fast version: r(a) by a multiplicative sieve over a <= sqrt(n/3); for
 * 4a^2 >= n the roots of b^2 = D mod 4a are built by Tonelli-Shanks,
 * Hensel lifting and the Chinese remainder theorem. */
static int8_t *legtab_base; static u64 *legtab_off; static u32 legtab_np;
static u32 *pidx;          /* pidx[p] = index of prime p */
static u32 *cof;          /* cof[a] = a / spf[a] */
static int8_t *chiv;      /* chi_D(p) for the current n */
static uint8_t *rv;       /* r(a) for the current n */

static inline int chi_fast(u64 n, u32 k, u32 p) {
    if (p == 2) return chi(n, 2);
    if (k < legtab_np) {
        u64 r = n % p;
        return legtab_base[legtab_off[k] + (r ? p - r : 0)];
    }
    return chi(n, p);
}

static inline u64 mulmod(u64 a, u64 b, u64 m) {   /* m < 2^32 here */
    return ((a % m) * (b % m)) % m;
}
static u64 powmod(u64 b, u64 e, u64 m) {
    u64 r = 1 % m; b %= m;
    while (e) { if (e & 1) r = mulmod(r, b, m); b = mulmod(b, b, m); e >>= 1; }
    return r;
}
static i64 inv_mod(i64 a, i64 m) {
    i64 g0 = m, g1 = ((a % m) + m) % m, x0 = 0, x1 = 1;
    while (g1) { i64 q = g0 / g1, t = g0 - q * g1; g0 = g1; g1 = t;
                 t = x0 - q * x1; x0 = x1; x1 = t; }
    if (g0 != 1) { fprintf(stderr, "inv_mod: not invertible\n"); exit(3); }
    return ((x0 % m) + m) % m;
}
/* square root of a quadratic residue x mod an odd prime p (Tonelli-Shanks) */
static u64 sqrt_mod_p(u64 x, u64 p) {
    x %= p;
    if (x == 0) return 0;
    if ((p & 3) == 3) return powmod(x, (p + 1) / 4, p);
    u64 q = p - 1; int s = 0;
    while (!(q & 1)) { q >>= 1; s++; }
    u64 z = 2;
    while (powmod(z, (p - 1) / 2, p) != p - 1) z++;
    u64 m = s, c = powmod(z, q, p), t = powmod(x, q, p), r = powmod(x, (q + 1) / 2, p);
    while (t != 1) {
        u64 i = 0, tt = t;
        while (tt != 1) { tt = mulmod(tt, tt, p); i++; }
        u64 b = c;
        for (u64 j = 0; j + 1 < m - i; j++) b = mulmod(b, b, p);
        m = i; c = mulmod(b, b, p); t = mulmod(t, c, p); r = mulmod(r, b, p);
    }
    return r;
}

static u32 *sq_stamp, *sq_val, sq_now;   /* per-n cache of sqrt(D) mod p */

/* count reduced forms (a, b, c) of discriminant -n with this a, 4a^2 >= n */
static long range2(u64 n, u64 a) {
    u64 res[256], tmp[256]; int nr = 0;
    u64 rest = a; int e = 0;
    while (!(rest & 1)) { rest >>= 1; e++; }
    /* 2-part: b mod 2^(e+1) with b^2 = -n mod 2^(e+2) */
    u64 M = 1ull << (e + 1), M4 = M << 1;
    u64 Dm = (M4 - n % M4) % M4;
    for (u64 b = 0; b < M; b++) if ((b * b) % M4 == Dm) res[nr++] = b;
    if (nr == 0) return 0;
    while (rest > 1) {
        u32 p = spf[rest]; u64 pk = 1; int k = 0;
        while (rest % p == 0) { rest /= p; pk *= p; k++; }
        u64 x = (pk - n % pk) % pk;          /* D mod p^k */
        u64 roots[2]; int nroots;
        if (x % p == 0) {                    /* ramified: only k = 1 can occur here */
            if (k > 1) return 0;
            roots[0] = 0; nroots = 1;
        } else {
            u64 s0;
            if (sq_stamp[p] == sq_now) s0 = sq_val[p];
            else { s0 = sqrt_mod_p(x % p, p); sq_stamp[p] = sq_now; sq_val[p] = (u32)s0; }
            if (mulmod(s0, s0, p) != x % p) return 0;   /* inert */
            u64 sk = s0, mod = p;
            for (int j = 1; j < k; j++) {
                mod *= p;
                /* Newton step mod p^(j+1) */
                u64 f = (mulmod(sk, sk, mod) + mod - x % mod) % mod;
                u64 inv = (u64)inv_mod((i64)((2 * sk) % mod), (i64)mod);
                sk = (sk + mod - mulmod(f, inv, mod)) % mod;
            }
            if (mulmod(sk, sk, pk) != x) { fprintf(stderr, "hensel failed\n"); exit(3); }
            roots[0] = sk; roots[1] = (pk - sk) % pk; nroots = 2;
        }
        /* CRT: combine res (mod M) with roots (mod pk) */
        u64 Minv = (u64)inv_mod((i64)(M % pk), (i64)pk);
        int nt = 0;
        for (int i = 0; i < nr; i++) for (int j = 0; j < nroots; j++) {
            u64 d = (roots[j] + pk - res[i] % pk) % pk;
            tmp[nt++] = res[i] + M * mulmod(d, Minv, pk);
        }
        M *= pk; nr = nt;
        for (int i = 0; i < nr; i++) res[i] = tmp[i];
    }
    if (M != 2 * a) { fprintf(stderr, "range2: modulus mismatch\n"); exit(3); }
    long cnt = 0;
    for (int i = 0; i < nr; i++) {
        i64 b = (i64)res[i];
        if (b > (i64)a) b -= (i64)(2 * a);    /* b in (-a, a] */
        u64 bb = (u64)(b * b);
        if ((bb + n) % (4 * a)) { fprintf(stderr, "range2: bad root\n"); exit(3); }
        u64 c = (bb + n) / (4 * a);
        if (c > a || (c == a && b >= 0)) cnt++;
    }
    return cnt;
}

static long exact_h(u64 n, long H) {
    u64 A = isqrt64(n / 3);
    sq_now++;
    long h = 0;
    u32 kp = 0;               /* index of the next prime whose chi is needed */
    rv[1] = 1;
    for (u64 a = 1; a <= A; a++) {
        if (a > 1) {
            u32 p = spf[a], a1 = cof[a];
            if (a1 == 1) {    /* a is prime: chi_D(a) is first needed here */
                while (primes[kp] < a) kp++;
                chiv[a] = (int8_t)chi_fast(n, kp, (u32)a);
            }
            int c = chiv[p];
            if (a1 > 1 && spf[a1] == p) rv[a] = (c == 0) ? 0 : rv[a1];
            else rv[a] = (c < 0) ? 0 : (uint8_t)(rv[a1] * (c == 0 ? 1 : 2));
        }
        if (!rv[a]) continue;
        if (4 * a * a < n) h += rv[a];
        else h += range2(n, a);
        if (h > H) return H + 1;
    }
    return h;
}

/* ---------------------------------------------------------------- sieve */

typedef struct { u64 start; u64 step; u64 len; uint16_t *cnt; uint8_t *fund; } prog_t;

/* Pattern of r(a)(n) for n = start + step*i, i = 0..per-1; returns the
 * period per (0 if r(a) vanishes identically on this progression). */
static u32 build_pattern(u32 a, u64 start, u64 step, int t, uint16_t *pat) {
    u32 ps[16]; int ks[16], np = 0; u32 rest = a; u32 per = 1;
    while (rest > 1) {
        u32 p = spf[rest]; int k = 0;
        while (rest % p == 0) { rest /= p; k++; }
        ps[np] = p; ks[np] = k; np++;
        if (p == 2) { if (t != 0) { if (k >= 2) return 0; } else per *= 2; }
        else per *= p;
    }
    for (u32 j = 0; j < per; j++) {
        u64 n = start + step * j;
        u32 r = 1;
        for (int q = 0; q < np && r; q++) {
            u32 p = ps[q]; int c;
            if (p == 2) c = chi(n, 2);
            else { u64 rr = n % p; c = rr ? legtab_base[legtab_off[pidx[p]] + p - rr] : 0; }
            if (c == 0) r = (ks[q] == 1) ? r : 0;
            else r = (c < 0) ? 0 : 2 * r;
        }
        pat[j] = (uint16_t)r;
    }
    return per;
}

static void add_periodic(uint16_t *c, u64 len, const uint16_t *pat, u32 per) {
    u64 i = 0;
    for (; i + per <= len; i += per) {
        uint16_t *cc = c + i;
        for (u32 j = 0; j < per; j++) cc[j] += pat[j];
    }
    for (u32 j = 0; i + j < len; j++) c[i + j] += pat[j];
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cn lo hi H out [seg [acap]]\n"); return 2; }
    u64 lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    long H = strtol(argv[3], 0, 10);
    u64 SEG = argc > 5 ? strtoull(argv[5], 0, 10) : (u64)1 << 24;
    long long acap_arg = argc > 6 ? strtoll(argv[6], 0, 10) : -1;
    int acap_auto = acap_arg < 0;
    u64 acap = acap_auto ? 20000 : (u64)acap_arg;
    if (acap > 20000) { fprintf(stderr, "acap must be <= 20000\n"); return 2; }
    if (lo < 3) lo = 3;
    if (hi > 4000000000000ull) { fprintf(stderr, "hi too large for 32-bit moduli\n"); return 2; }
    if (H < 1 || H > 20000) { fprintf(stderr, "H must be in [1, 20000] (uint16 counts)\n"); return 2; }
    FILE *out = fopen(argv[4], "w");
    if (!out) { perror("out"); return 1; }

    u64 sq = isqrt64(hi) + 2;
    make_primes((u32)sq);
    make_spf((u32)(isqrt64(hi / 3) + 2));
    chi_cache = calloc(spf_lim + 1, sizeof(int));
    chi_stamp = calloc(spf_lim + 1, sizeof(u32));
    cof = calloc(spf_lim + 1, sizeof(u32));
    for (u32 a = 2; a <= spf_lim; a++) cof[a] = a / spf[a];
    chiv = calloc(spf_lim + 1, 1);
    rv = calloc(spf_lim + 1, 1);
    sq_stamp = calloc(spf_lim + 1, sizeof(u32));
    sq_val = calloc(spf_lim + 1, sizeof(u32));
    int check = getenv("CN_CHECK") != NULL;
    int check_stream = getenv("CN_CHECK_STREAM") != NULL;

    /* number of primes streamed over whole segments */
    u32 K = (u32)(1.3 * H + 40);
    if (K > nprimes) K = nprimes;
    uint16_t *pat = malloc(sizeof(uint16_t) * (2 * (primes[K - 1] > acap ? primes[K - 1] : acap) + 8));
    pidx = calloc(sq + 2, sizeof(u32));
    for (u32 k = 0; k < nprimes; k++) pidx[primes[k]] = k;
    {   /* Legendre tables for primes up to max(20000, p_K) */
        u32 legmax = primes[K - 1] > 20000 ? primes[K - 1] : 20000;
        u32 np = 0; u64 tot = 0;
        while (np < nprimes && primes[np] <= legmax) { tot += primes[np]; np++; }
        legtab_np = np;
        legtab_off = malloc(sizeof(u64) * (np + 1));
        legtab_base = calloc(tot + 1, 1);
        u64 off = 0;
        for (u32 k = 0; k < np; k++) {
            u32 p = primes[k]; legtab_off[k] = off;
            if (p > 2) {
                int8_t *L = legtab_base + off;
                for (u64 x = 1; x < p; x++) L[(x * x) % p] = 1;
                for (u32 r = 1; r < p; r++) if (!L[r]) L[r] = -1;
            }
            off += p;
        }
    }

    u64 n_fund = 0, n_stream_surv = 0, n_exact = 0, n_found = 0, n_stream_checked = 0;
    long *hist = calloc(H + 2, sizeof(long));
    u64 *maxn = calloc(H + 2, sizeof(u64));

    for (u64 s = lo; s <= hi; s += SEG) {
        u64 e = s + SEG - 1; if (e > hi) e = hi;
        /* three progressions: n = 3 mod 4, n = 4 mod 16, n = 8 mod 16 */
        prog_t P[3];
        u64 res[3] = {3, 4, 8}, mod[3] = {4, 16, 16};
        for (int t = 0; t < 3; t++) {
            u64 first = s + ((res[t] + mod[t] - s % mod[t]) % mod[t]);
            P[t].start = first; P[t].step = mod[t];
            P[t].len = first > e ? 0 : (e - first) / mod[t] + 1;
            P[t].cnt = malloc(sizeof(uint16_t) * (P[t].len + 1));
            P[t].fund = malloc(P[t].len + 1);
            for (u64 i = 0; i < P[t].len; i++) { P[t].cnt[i] = 1; P[t].fund[i] = 1; }
            /* odd-squarefree sieve: kill n divisible by p^2, p odd */
            for (u32 k = 1; k < nprimes; k++) {
                u64 p = primes[k], p2 = p * p;
                if (p2 > e) break;
                /* solve first + step*i = 0 mod p2 */
                u64 st = P[t].step % p2, f = P[t].start % p2;
                /* inverse of st mod p2 (st is a power of two, p odd) */
                i64 g0 = (i64)p2, g1 = (i64)st, x0 = 0, x1 = 1;
                while (g1) { i64 qq = g0 / g1, tt = g0 - qq * g1; g0 = g1; g1 = tt;
                             tt = x0 - qq * x1; x0 = x1; x1 = tt; }
                u64 inv = (u64)((x0 % (i64)p2 + (i64)p2) % (i64)p2);
                u64 i0 = (u64)(((__uint128_t)((p2 - f) % p2) * inv) % p2);
                for (u64 i = i0; i < P[t].len; i += p2) P[t].fund[i] = 0;
            }
            for (u64 i = 0; i < P[t].len; i++) if (P[t].fund[i]) n_fund++;
        }
        /* stream every a <= acap with 4a^2 < s (all a, composite included;
         * any set of distinct a < sqrt(n)/2 gives a lower bound), then the
         * primes beyond acap up to the K-th prime with 4p^2 < s */
        u64 amax = 1;
        /* auto mode (acap < 0): composites only where the first K primes do
         * not all satisfy 4p^2 < s, i.e. where primes alone cannot finish */
        u64 cap = acap_auto ? ((4ull * primes[K - 1] * primes[K - 1] < s) ? 1 : 4000) : acap;
        while (amax + 1 <= cap && 4 * (amax + 1) * (amax + 1) < s) amax++;
        u32 kmax = 0;
        while (kmax < nprimes && primes[kmax] <= amax) kmax++;     /* primes already covered */
        u32 kend = kmax;
        while (kend < K && 4ull * primes[kend] * primes[kend] < s) kend++;
        for (int t = 0; t < 3; t++) {
            uint16_t *c = P[t].cnt; u64 len = P[t].len;
            if (!len) continue;
            for (u64 a = 2; a <= amax; a++) {
                u32 per = build_pattern((u32)a, P[t].start, P[t].step, t, pat);
                if (!per) continue;
                add_periodic(c, len, pat, per);
            }
            for (u32 k = kmax; k < kend; k++) {
                u32 p = primes[k];
                u32 per = build_pattern(p, P[t].start, P[t].step, t, pat);
                if (per) add_periodic(c, len, pat, per);
            }
            if (check_stream) {
                /* recompute every streamed count with r_of (Jacobi symbols,
                 * no Legendre tables, no periodic patterns) */
                for (u64 i = 0; i < len; i++) {
                    if (!P[t].fund[i]) continue;
                    u64 n = P[t].start + P[t].step * i;
                    stamp_now++;
                    u64 expect = 1;
                    for (u64 a = 2; a <= amax; a++) expect += r_of(n, (u32)a);
                    for (u32 k = kmax; k < kend; k++) expect += r_of(n, primes[k]);
                    if (expect < 65536 && expect != c[i]) {
                        fprintf(stderr, "STREAM CHECK FAILED n=%llu streamed=%u expected=%llu\n",
                                (unsigned long long)n, (unsigned)c[i], (unsigned long long)expect);
                        return 5;
                    }
                    n_stream_checked++;
                }
            }
            /* survivors */
            for (u64 i = 0; i < len; i++) {
                if (!P[t].fund[i] || c[i] > H) continue;
                u64 n = P[t].start + P[t].step * i;
                long cnt = c[i];
                n_stream_surv++;
                /* continue the prime filter on this n */
                u32 k = kend;
                for (; k < nprimes && 4ull * primes[k] * primes[k] < n; k++) {
                    cnt += 1 + chi_fast(n, k, primes[k]);
                    if (cnt > H) break;
                }
                if (cnt > H) continue;
                n_exact++;
                long h = exact_h(n, H);
                if (check) {
                    long h2 = exact_h_slow(n, H);
                    if (h2 != h) { fprintf(stderr, "CHECK FAILED n=%llu fast=%ld slow=%ld\n",
                                           (unsigned long long)n, h, h2); return 4; }
                }
                if (h <= H) {
                    fprintf(out, "%llu %ld\n", (unsigned long long)n, h);
                    n_found++; hist[h]++;
                    if (n > maxn[h]) maxn[h] = n;
                }
            }
        }
        for (int t = 0; t < 3; t++) { free(P[t].cnt); free(P[t].fund); }
        if (e == hi) break;
    }
    fprintf(out, "# stats lo=%llu hi=%llu H=%ld fundamental=%llu stream_survivors=%llu exact=%llu found=%llu",
            (unsigned long long)lo, (unsigned long long)hi, H, (unsigned long long)n_fund,
            (unsigned long long)n_stream_surv, (unsigned long long)n_exact, (unsigned long long)n_found);
    if (check_stream) fprintf(out, " stream_checked=%llu", (unsigned long long)n_stream_checked);
    fprintf(out, "\n");
    fclose(out);
    return 0;
}
