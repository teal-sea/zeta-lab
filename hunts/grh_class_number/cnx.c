/* cnx.c: a blocked, saturating driver around the sibling hunt's reduced-form
 * sieve (hunts/qrh_class_number/cn.c), for class numbers up to H = 5000.
 *
 * Usage:  cnx H planfile
 *
 * Each plan line is "lo hi mode A0 out": every negative fundamental
 * discriminant D with lo <= |D| <= hi and h(D) <= H is written to `out` as
 * "n h" lines sorted by n = |D|, and counts go to `out.stats`.  A chunk whose
 * stats file exists is skipped, so a stopped run resumes where it was.
 *
 * cn.c is included unchanged (its main renamed), so build_pattern, chi,
 * r_of, exact_h and exact_h_slow are the sibling's own code.  New here:
 *
 *  - blocks of 2^19 integers, so the uint16 counters stay in the L2 cache,
 *    with one cached periodic pattern per (a, progression) and saturating
 *    adds: a counter holds min(true partial count, 65535), never a wrapped
 *    value;
 *  - mode 1 (full): after r(a) has been streamed for every a with
 *    4a^2 < s (s the block start), every reduced form (a, b, c) with a
 *    larger first coefficient and discriminant in the block is enumerated
 *    directly (n = 4ac - b^2, 0 <= |b| <= a <= c).  The counter is then the
 *    exact class number of every fundamental discriminant in the block;
 *  - mode 0 (filter): r(a) is streamed for every a <= A0 and for the primes
 *    in (A0, amax]; a discriminant whose partial count is <= H goes to
 *    cn.c's exact_h.  The partial count is a lower bound for h(D), so the
 *    filter can only lose a field by over-counting.
 *
 * Checks (environment): CNX_CHECK_FULL=1 compares every mode-1 class number
 * with exact_h; CNX_CHECK_STREAM=k recomputes the streamed count of every
 * k-th fundamental discriminant with r_of (Jacobi symbols, no patterns).
 * Everything is integer arithmetic.
 */
#define main cn_main
#include "../qrh_class_number/cn.c"
#undef main
#include <immintrin.h>
#include <time.h>

static u64 BLK = (u64)1 << 19;
#define MINRUN 4096u

static const u64 BASE[3] = {3, 4, 8}, STEP[3] = {4, 16, 16};
static u64 LEN[3];

typedef struct { uint8_t *p; u32 plen; uint8_t state; } pat_t;   /* state 0 new, 1 zero, 2 ready */
static pat_t *PAT[3];
static uint16_t *pat16;
static u64 pat_bytes;

static const pat_t *get_pat(u32 a, int t) {
    pat_t *P = &PAT[t][a];
    if (P->state) return P;
    u32 per = build_pattern(a, BASE[t], STEP[t], t, pat16);
    int nz = 0;
    for (u32 j = 0; j < per; j++) {
        if (pat16[j] > 255) { fprintf(stderr, "pattern value too large\n"); exit(3); }
        if (pat16[j]) nz = 1;
    }
    if (!per || !nz) { P->state = 1; return P; }
    u32 reps = per >= MINRUN ? 1 : (MINRUN + per - 1) / per;
    P->plen = per * reps;
    P->p = malloc(P->plen);
    if (!P->p) { fprintf(stderr, "out of memory (patterns)\n"); exit(3); }
    for (u32 r = 0; r < reps; r++)
        for (u32 j = 0; j < per; j++) P->p[(u64)r * per + j] = (uint8_t)pat16[j];
    P->state = 2;
    pat_bytes += P->plen;
    return P;
}

static inline void sat_add_run(uint16_t *c, const uint8_t *p, u64 n) {
    u64 i = 0;
#if defined(__AVX512BW__)
    for (; i + 32 <= n; i += 32) {
        __m512i x = _mm512_loadu_si512((const void *)(c + i));
        __m512i y = _mm512_cvtepu8_epi16(_mm256_loadu_si256((const __m256i *)(p + i)));
        _mm512_storeu_si512((void *)(c + i), _mm512_adds_epu16(x, y));
    }
#elif defined(__AVX2__)
    for (; i + 16 <= n; i += 16) {
        __m256i x = _mm256_loadu_si256((const __m256i *)(c + i));
        __m256i y = _mm256_cvtepu8_epi16(_mm_loadu_si128((const __m128i *)(p + i)));
        _mm256_storeu_si256((__m256i *)(c + i), _mm256_adds_epu16(x, y));
    }
#endif
    for (; i < n; i++) { u32 v = (u32)c[i] + p[i]; c[i] = (uint16_t)(v > 65535 ? 65535 : v); }
}

/* c[i] += r(a)(n_i) for the block whose first global index is j0 */
static void add_pat(uint16_t *c, u64 len, const pat_t *P, u64 j0) {
    u64 ph = j0 % P->plen, i = 0;
    while (i < len) {
        u64 run = P->plen - ph;
        if (run > len - i) run = len - i;
        sat_add_run(c + i, P->p + ph, run);
        i += run; ph = 0;
    }
}

static inline void sat_inc(uint16_t *x, u32 w) {
    u32 v = (u32)*x + w;
    *x = (uint16_t)(v > 65535 ? 65535 : v);
}

/* Every reduced form (a, b, c), a > amax, with discriminant -n, s <= n <= e:
 * |b| <= a <= c, b >= 0 if |b| = a or a = c.  Forms with b odd have
 * n = 3 mod 4 and go to X0 (index (n-3)/4 - s/4); forms with b even have
 * n = 4m and go to XE (index m - s/4).  The pair (a, +-b, c) counts twice
 * unless b = 0, b = a or c = a. */
static void enum_forms(u64 s, u64 e, u64 amax, uint16_t *X0, uint16_t *XE) {
    u64 ahi = isqrt64(e / 3), j00 = s / 4;
    for (u64 a = amax + 1; a <= ahi; a++) {
        u64 fa = 4 * a, a2 = 4 * a * a, bmin0 = 0;
        if (a2 > e) bmin0 = isqrt64(a2 - e - 1) + 1;          /* smallest b with b^2 >= 4a^2 - e */
        for (int par = 0; par < 2; par++) {
            if (!par && !(a & 3)) continue;                    /* 4 | a, b even: n = 0, 12 mod 16 */
            u64 b = bmin0 + ((bmin0 ^ (u64)par) & 1);
            if (b > a) continue;
            u64 nlo = s + b * b + fa - 1, nhi = e + b * b;
            u64 qlo = nlo / fa, rlo = nlo % fa, qhi = nhi / fa, rhi = nhi % fa;
            uint16_t *X = par ? X0 : XE;
            for (;;) {
                u64 clo = qlo < a ? a : qlo;
                if (clo <= qhi) {
                    u32 w = (b == 0 || b == a) ? 1 : 2;
                    u64 off = par ? (b * b + 3) / 4 : (b / 2) * (b / 2);
                    u64 idx = a * clo - off - j00, c = clo;
                    if (c == a) { sat_inc(X + idx, 1); idx += a; c++; }
                    for (; c <= qhi; c++, idx += a) sat_inc(X + idx, w);
                }
                if (b + 2 > a) break;
                u64 delta = 4 * b + 4;
                rlo += delta; while (rlo >= fa) { rlo -= fa; qlo++; }
                rhi += delta; while (rhi >= fa) { rhi -= fa; qhi++; }
                b += 2;
            }
        }
    }
}

static double now(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static u64 *sqres[3];      /* sqres[t][k]: j with BASE + STEP*j = 0 mod p_k^2 */

static void setup(u64 hi) {
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
    pidx = calloc(sq + 2, sizeof(u32));
    for (u32 k = 0; k < nprimes; k++) pidx[primes[k]] = k;
    {   /* Legendre tables for every prime that can divide a streamed a */
        u32 legmax = (u32)(isqrt64(hi) / 2 + 2);
        if (legmax < 20000) legmax = 20000;
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
    for (int t = 0; t < 3; t++) {
        PAT[t] = calloc(spf_lim + 2, sizeof(pat_t));
        sqres[t] = malloc(sizeof(u64) * (nprimes + 1));
        for (u32 k = 1; k < nprimes; k++) {
            u64 p = primes[k], p2 = p * p;
            i64 g0 = (i64)p2, g1 = (i64)(STEP[t] % p2), x0 = 0, x1 = 1;
            while (g1) { i64 qq = g0 / g1, tt = g0 - qq * g1; g0 = g1; g1 = tt;
                         tt = x0 - qq * x1; x0 = x1; x1 = tt; }
            u64 inv = (u64)((x0 % (i64)p2 + (i64)p2) % (i64)p2);
            sqres[t][k] = (u64)(((__uint128_t)((p2 - BASE[t] % p2) % p2) * inv) % p2);
        }
    }
    pat16 = malloc(sizeof(uint16_t) * (2 * (u64)spf_lim + 16));
}

typedef struct { u64 fund, surv, exact, found, checked_full, checked_stream; } stat_t;

static int run_chunk(u64 lo, u64 hi, long H, int full, u64 A0, const char *outpath) {
    char part[4096], stp[4096], stf[4096];
    snprintf(part, sizeof part, "%s.part", outpath);
    snprintf(stf, sizeof stf, "%s.stats", outpath);
    snprintf(stp, sizeof stp, "%s.stats.part", outpath);
    FILE *out = fopen(part, "w");
    if (!out) { perror(part); return 1; }
    static char obuf[1 << 20];
    setvbuf(out, obuf, _IOFBF, sizeof obuf);
    int check_full = getenv("CNX_CHECK_FULL") != NULL;
    long check_stream = getenv("CNX_CHECK_STREAM") ? atol(getenv("CNX_CHECK_STREAM")) : 0;
    double t_start = now();
    stat_t st = {0};
    long *hist = calloc(H + 2, sizeof(long));
    u64 *maxn = calloc(H + 2, sizeof(u64));
    uint16_t *cnt[3]; uint8_t *fund[3];
    for (int t = 0; t < 3; t++) { cnt[t] = malloc(sizeof(uint16_t) * (LEN[t] + 64)); fund[t] = malloc(LEN[t] + 64); }
    uint16_t *X0 = malloc(sizeof(uint16_t) * (LEN[0] + 64)), *XE = malloc(sizeof(uint16_t) * (LEN[0] + 64));
    if (lo < 3) lo = 3;

    for (u64 k = lo / BLK; k <= hi / BLK; k++) {
        u64 s = k * BLK, e = s + BLK - 1;
        u64 amax = s == 0 ? 0 : isqrt64((s - 1) / 4);            /* largest a with 4a^2 < s */
        u64 j0[3] = {k * LEN[0], k * LEN[1], k * LEN[2]};
        for (int t = 0; t < 3; t++) {
            /* fundamental discriminants: no odd p^2 | n */
            memset(fund[t], 1, LEN[t]);
            for (u32 q = 1; q < nprimes; q++) {
                u64 p2 = (u64)primes[q] * primes[q];
                if (p2 > e) break;
                u64 r = j0[t] % p2, f = sqres[t][q];
                u64 i = f >= r ? f - r : f + p2 - r;
                for (; i < LEN[t]; i += p2) fund[t][i] = 0;
            }
            /* the streamed lower bound: a = 1, then the periodic r(a) */
            uint16_t init = amax >= 1 ? 1 : 0;
            for (u64 i = 0; i < LEN[t]; i++) cnt[t][i] = init;
            u64 acomp = full ? amax : (A0 < amax ? A0 : amax);
            for (u64 a = 2; a <= acomp; a++) {
                const pat_t *P = get_pat((u32)a, t);
                if (P->state == 2) add_pat(cnt[t], LEN[t], P, j0[t]);
            }
            u32 kp0 = 0, kp1 = 0;
            if (!full) {
                while (kp0 < nprimes && primes[kp0] <= acomp) kp0++;
                kp1 = kp0;
                while (kp1 < nprimes && primes[kp1] <= amax) kp1++;
                for (u32 q = kp0; q < kp1; q++) {
                    const pat_t *P = get_pat(primes[q], t);
                    if (P->state == 2) add_pat(cnt[t], LEN[t], P, j0[t]);
                }
            }
            if (check_stream) {
                for (u64 i = 0; i < LEN[t]; i++) {
                    if (!fund[t][i]) continue;
                    u64 n = BASE[t] + STEP[t] * (j0[t] + i);
                    if (n < lo || n > hi || (n / STEP[t]) % (u64)check_stream) continue;
                    stamp_now++;
                    u64 expect = init;
                    for (u64 a = 2; a <= acomp; a++) expect += r_of(n, (u32)a);
                    for (u32 q = kp0; q < kp1; q++) expect += r_of(n, primes[q]);
                    if (expect > 65535) expect = 65535;
                    if (expect != cnt[t][i]) {
                        fprintf(stderr, "STREAM CHECK FAILED n=%llu streamed=%u expected=%llu\n",
                                (unsigned long long)n, (unsigned)cnt[t][i], (unsigned long long)expect);
                        return 5;
                    }
                    st.checked_stream++;
                }
            }
        }
        if (full) {
            memset(X0, 0, sizeof(uint16_t) * LEN[0]);
            memset(XE, 0, sizeof(uint16_t) * LEN[0]);
            enum_forms(s, e, amax, X0, XE);
        }
        /* emit in increasing n: the 16 integers s+16g .. s+16g+15 hold the
         * candidates +3 (t0), +4 (t1), +7 (t0), +8 (t2), +11 (t0), +15 (t0) */
        static const int ST[6] = {0, 1, 0, 2, 0, 0}, SR[6] = {0, 0, 1, 0, 2, 3}, SO[6] = {3, 4, 7, 8, 11, 15};
        for (u64 g = 0; g < LEN[1]; g++) {
            for (int z = 0; z < 6; z++) {
                int t = ST[z];
                u64 i = t == 0 ? 4 * g + SR[z] : g;
                if (!fund[t][i]) continue;
                u64 n = s + 16 * g + SO[z];
                if (n < lo || n > hi) continue;
                st.fund++;
                u32 v = cnt[t][i];
                if (full) {
                    v += t == 0 ? X0[i] : XE[4 * i + (u64)t];
                    if (v > 65535) v = 65535;
                }
                long h;
                if (full) {
                    h = v;
                    if (check_full) {
                        long h2 = exact_h(n, H);
                        if ((h <= H) ? (h2 != h) : (h2 != H + 1)) {
                            fprintf(stderr, "FULL CHECK FAILED n=%llu enumerated=%ld exact_h=%ld\n",
                                    (unsigned long long)n, h, h2);
                            return 4;
                        }
                        st.checked_full++;
                    }
                    if (h > H) continue;
                    st.surv++;
                } else {
                    if (v > (u32)H) continue;
                    st.surv++; st.exact++;
                    h = exact_h(n, H);
                    if (h > H) continue;
                }
                fprintf(out, "%llu %ld\n", (unsigned long long)n, h);
                st.found++; hist[h]++;
                if (n > maxn[h]) maxn[h] = n;
            }
        }
    }
    if (fclose(out)) { perror("close"); return 1; }
    FILE *sf = fopen(stp, "w");
    if (!sf) { perror(stp); return 1; }
    fprintf(sf, "# stats lo=%llu hi=%llu H=%ld mode=%d A0=%llu fundamental=%llu stream_survivors=%llu exact=%llu found=%llu checked_full=%llu checked_stream=%llu ms=%llu\n",
            (unsigned long long)lo, (unsigned long long)hi, H, full, (unsigned long long)A0,
            (unsigned long long)st.fund, (unsigned long long)st.surv, (unsigned long long)st.exact,
            (unsigned long long)st.found, (unsigned long long)st.checked_full,
            (unsigned long long)st.checked_stream, (unsigned long long)(1000 * (now() - t_start)));
    for (long h = 1; h <= H; h++)
        if (hist[h]) fprintf(sf, "%ld %ld %llu\n", h, hist[h], (unsigned long long)maxn[h]);
    if (fclose(sf)) { perror("close"); return 1; }
    if (rename(part, outpath) || rename(stp, stf)) { perror("rename"); return 1; }
    for (int t = 0; t < 3; t++) { free(cnt[t]); free(fund[t]); }
    free(X0); free(XE); free(hist); free(maxn);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: cnx H planfile\n"); return 2; }
    long H = strtol(argv[1], 0, 10);
    if (H < 1 || H > 20000) { fprintf(stderr, "H must be in [1, 20000]\n"); return 2; }
    if (getenv("CNX_BLK_LOG2")) BLK = (u64)1 << atoi(getenv("CNX_BLK_LOG2"));
    if (BLK < 65536 || (BLK & (BLK - 1))) { fprintf(stderr, "bad block size\n"); return 2; }
    LEN[0] = BLK / 4; LEN[1] = BLK / 16; LEN[2] = BLK / 16;
    FILE *pf = fopen(argv[2], "r");
    if (!pf) { perror(argv[2]); return 1; }
    enum { MAXC = 100000 };
    u64 *lo = malloc(sizeof(u64) * MAXC), *hi = malloc(sizeof(u64) * MAXC), *A0 = malloc(sizeof(u64) * MAXC);
    int *mode = malloc(sizeof(int) * MAXC), nc = 0;
    char (*path)[1024] = malloc((size_t)MAXC * 1024);
    unsigned long long l, h, a; int m; u64 himax = 0;
    while (nc < MAXC && fscanf(pf, "%llu %llu %d %llu %1023s", &l, &h, &m, &a, path[nc]) == 5) {
        lo[nc] = l; hi[nc] = h; mode[nc] = m; A0[nc] = a;
        if (h > himax) himax = h;
        nc++;
    }
    fclose(pf);
    if (!nc) { fprintf(stderr, "empty plan\n"); return 2; }
    if (himax > 4000000000000ull) { fprintf(stderr, "hi too large for 32-bit moduli\n"); return 2; }
    setup(himax + BLK);
    for (int c = 0; c < nc; c++) {
        char stf[2048];
        snprintf(stf, sizeof stf, "%s.stats", path[c]);
        FILE *tst = fopen(stf, "r");
        if (tst) { fclose(tst); continue; }
        double t0 = now();
        int rc = run_chunk(lo[c], hi[c], H, mode[c], A0[c], path[c]);
        if (rc) return rc;
        printf("chunk %llu..%llu mode=%d A0=%llu: %.1fs patterns=%.0fMB\n", (unsigned long long)lo[c],
               (unsigned long long)hi[c], mode[c], (unsigned long long)A0[c], now() - t0, pat_bytes / 1e6);
        fflush(stdout);
    }
    return 0;
}
