/* lsieve.c: an analytic candidate finder that shares nothing with cn.c / cnx.c.
 * For every negative fundamental discriminant -n, lo <= n <= hi, the truncated Euler product
 *   est(n) = sqrt(n)/pi * prod_{p <= P} (1 - chi_{-n}(p)/p)^{-1}
 * approximates h(-n) (class number formula, w = 2).  Records (n, est) with est <= T are written
 * as binary (uint64, float).  Not a bound: a detector.  usage: lsieve lo hi P T out.bin */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64; typedef uint32_t u32;
#define BLK ((u64)1 << 20)
static const u64 BASE[3] = {3, 4, 8}, STEP[3] = {4, 16, 16};
int main(int argc, char **argv) {
    if (argc < 6) return 2;
    u64 lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    u32 P = (u32)atoi(argv[3]); double T = atof(argv[4]);
    FILE *out = fopen(argv[5], "wb"); if (!out) return 1;
    u64 sq = (u64)sqrtl((long double)(hi + BLK)) + 2;
    char *comp = calloc(sq + 1, 1); u32 *pr = malloc(sizeof(u32) * (sq / 2 + 10)); u32 np = 0;
    for (u64 i = 2; i <= sq; i++) if (!comp[i]) { pr[np++] = (u32)i; for (u64 j = i * i; j <= sq; j += i) comp[j] = 1; }
    u64 LEN[3] = {BLK / 4, BLK / 16, BLK / 16};
    /* patterns: pat[t][k][j] = -log(1 - chi(p_k)/p_k) for n = BASE + STEP*j, j mod p_k */
    u32 nP = 0; while (nP < np && pr[nP] <= P) nP++;
    float **pat[3];
    for (int t = 0; t < 3; t++) {
        pat[t] = malloc(sizeof(float *) * nP);
        for (u32 k = 1; k < nP; k++) {
            u32 p = pr[k]; char *qr = calloc(p, 1);
            for (u64 x = 1; x < p; x++) qr[(x * x) % p] = 1;
            pat[t][k] = malloc(sizeof(float) * p);
            for (u32 j = 0; j < p; j++) {
                u64 n = BASE[t] + STEP[t] * j; u32 r = (u32)(n % p);
                if (r == 0) { pat[t][k][j] = 0; continue; }
                int chi = qr[p - r] ? 1 : -1;                 /* (-n / p) */
                pat[t][k][j] = (float)(-log(1.0 - (double)chi / p));
            }
            free(qr);
        }
    }
    float *est[3]; uint8_t *fund[3];
    for (int t = 0; t < 3; t++) { est[t] = malloc(sizeof(float) * LEN[t]); fund[t] = malloc(LEN[t]); }
    u64 nfund = 0, nout = 0;
    for (u64 kb = lo / BLK; kb <= hi / BLK; kb++) {
        u64 s = kb * BLK, e = s + BLK - 1;
        for (int t = 0; t < 3; t++) {
            u64 j0 = kb * LEN[t];
            memset(fund[t], 1, LEN[t]);
            for (u32 k = 1; k < np; k++) {
                u64 p2 = (u64)pr[k] * pr[k]; if (p2 > e) break;
                u64 inv4 = (3 * p2 + 1) / 4;                                  /* 4 * inv4 = 1 mod p2 */
                u64 inv = STEP[t] == 4 ? inv4 : (u64)(((__uint128_t)inv4 * inv4) % p2);
                u64 first = BASE[t] + STEP[t] * j0;                           /* n at index 0 */
                u64 i0 = (u64)(((__uint128_t)((p2 - first % p2) % p2) * inv) % p2);
                for (u64 i = i0; i < LEN[t]; i += p2) fund[t][i] = 0;
            }
            float *E = est[t];
            if (t == 0) for (u64 i = 0; i < LEN[t]; i++) E[i] = ((s + 3 + 4 * i) & 7) == 7 ? (float)log(2.0) : (float)log(2.0 / 3.0);
            else for (u64 i = 0; i < LEN[t]; i++) E[i] = 0;
            for (u32 k = 1; k < nP; k++) {
                u32 p = pr[k]; const float *pp = pat[t][k];
                u64 ph = j0 % p, i = 0;
                while (i < LEN[t]) {
                    u64 run = p - ph; if (run > LEN[t] - i) run = LEN[t] - i;
                    for (u64 q = 0; q < run; q++) E[i + q] += pp[ph + q];
                    i += run; ph = 0;
                }
            }
        }
        static const int ST[6] = {0, 1, 0, 2, 0, 0}, SR[6] = {0, 0, 1, 0, 2, 3}, SO[6] = {3, 4, 7, 8, 11, 15};
        for (u64 g = 0; g < LEN[1]; g++) for (int z = 0; z < 6; z++) {
            int t = ST[z]; u64 i = t == 0 ? 4 * g + SR[z] : g;
            if (!fund[t][i]) continue;
            u64 n = s + 16 * g + SO[z];
            if (n < lo || n > hi) continue;
            nfund++;
            double h = sqrt((double)n) / M_PI * exp((double)est[t][i]);
            if (h <= T) { float f = (float)h; fwrite(&n, 8, 1, out); fwrite(&f, 4, 1, out); nout++; }
        }
    }
    if (fclose(out)) return 1;
    printf("fundamental=%llu written=%llu\n", (unsigned long long)nfund, (unsigned long long)nout);
    return 0;
}
