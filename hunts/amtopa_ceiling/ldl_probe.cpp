// Isolates the regression in AMTOPA's convexity gate between the revision that
// produced their recorded certificate and the repository tip.
//
//   b3b7784 (named by their candidate.json as the source of the recorded run):
//       the curvature entries are THIN -- point(scalar), where scalar is a
//       rigorous lower bound on a_p * W''(d_p).  Sound, because the Hessian is
//       sum_p (a_p W''_p) J_p with J_p the all-ones block on [i,j), every J_p is
//       PSD, so lowering the scalar coefficients gives a PSD lower bound.
//
//   7253fdca (tip): the entries become mul(p.exact, {sec, +infinity}).  The
//       lower bound is unchanged; the upper becomes +inf.
//
// Both revisions then run the same interval LDL.  This file runs that LDL on an
// obviously positive-definite matrix in each of the two shapes.
//
//   g++ -std=c++17 -O2 -ffp-contract=off -o ldl_probe ldl_probe.cpp && ./ldl_probe
#include <algorithm>
#include <array>
#include <cmath>
#include <iostream>
#include <limits>

constexpr int Q = 6;
struct Interval { long double lo, hi; };

static long double ldown(long double x) {
    return std::nextafterl(x, -std::numeric_limits<long double>::infinity());
}
static long double lup(long double x) {
    return std::nextafterl(x, std::numeric_limits<long double>::infinity());
}
static Interval point(long double x) { return {x, x}; }
static Interval add(Interval a, Interval b) { return {ldown(a.lo + b.lo), lup(a.hi + b.hi)}; }
static Interval neg(Interval a) { return {-a.hi, -a.lo}; }
static Interval sub(Interval a, Interval b) { return add(a, neg(b)); }
static Interval mul(Interval a, Interval b) {
    const long double p[4] = {a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi};
    return {ldown(*std::min_element(p, p + 4)), lup(*std::max_element(p, p + 4))};
}
static Interval divp(Interval a, Interval b) {
    return mul(a, {ldown(1.0L / b.hi), lup(1.0L / b.lo)});
}

// verbatim from 7253fdca src/verify_local_tables.cpp
static bool interval_ldl_positive(std::array<std::array<Interval, Q>, Q> matrix) {
    for (int k = 0; k < Q; ++k) {
        if (!(matrix[k][k].lo > 0)) return false;
        const Interval pivot = matrix[k][k];
        for (int i = k + 1; i < Q; ++i) {
            const Interval lik = divp(matrix[i][k], pivot);
            for (int j = i; j < Q; ++j) {
                const Interval correction = mul(mul(lik, matrix[j][k]), point(1));
                matrix[j][i] = sub(matrix[j][i], correction);
                matrix[i][j] = matrix[j][i];
            }
        }
    }
    return true;
}

int main() {
    std::array<std::array<Interval, Q>, Q> thin{}, fat{};
    for (int r = 0; r < Q; ++r)
        for (int c = 0; c < Q; ++c) {
            const long double v = (r == c) ? 10.0L : 1.0L;   // diagonally dominant
            thin[r][c] = point(v);
            fat[r][c] = {v, std::numeric_limits<long double>::infinity()};
        }
    std::cout << "matrix: 10 on the diagonal, 1 off it -- positive definite by any test\n";
    std::cout << "  thin entries   (b3b7784 shape): interval_ldl_positive = "
              << (interval_ldl_positive(thin) ? "true" : "false") << "\n";
    std::cout << "  +inf upper     (7253fdca shape): interval_ldl_positive = "
              << (interval_ldl_positive(fat) ? "true" : "false") << "\n";
    return 0;
}
