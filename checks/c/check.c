/* check.c -- independent check of the arithmetic in the paper, in C99.
 *
 * Recomputes the sizes of the balls (by counting lattice points), the ball identity in
 * Z[Z/M] on pseudo-random small cases, the values kappa_n(v), the congruences modulo 841,
 * the case analysis modulo 29 and 71, the coefficients of the joint relation and the rank
 * of the two circulant systems over F_71.  Exits with status 1 if any check fails.
 *
 * Build: cc -O2 -o check check.c && ./check
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int failures = 0, passed = 0;

static void check(int cond, const char *what) {
  printf("%s%s\n", cond ? "ok    " : "FAIL  ", what);
  if (cond) passed++; else failures++;
}

static int64_t f(int64_t n, int64_t A) { return A * A * A + 3 * A * A + 2 * A - 6 * n * A; }
static int64_t md(int64_t a, int64_t p) { a %= p; return a < 0 ? a + p : a; }
static int64_t pw(int64_t b, int64_t e, int64_t p) {
  int64_t r = 1 % p; b = md(b, p);
  while (e > 0) { if (e & 1) r = r * b % p; b = b * b % p; e >>= 1; }
  return r;
}
static int64_t kappa(int64_t n, int64_t v, int64_t p) {
  return md(3 * (2 * n + 1) * (2 * n + 1) + 3 * (2 * n + 1) * (1 + pw(2, v, p)) + 2 * pw(3, v, p) - 6 * n, p);
}

/* number of a in Z^n with |a| <= r, by recursion on the first coordinate */
static int64_t ballcount(int n, int r) {
  if (n == 0) return 1;
  int64_t s = 0;
  for (int t = -r; t <= r; t++) s += ballcount(n - 1, r - abs(t));
  return s;
}

/* add 6 to lhs[sum a_j x_j mod M] for every a in the ball, by recursion */
static void ballsum(int n, int r, const int *x, int M, int acc, int64_t *lhs) {
  if (n == 0) { lhs[acc] += 6; return; }
  for (int t = -r; t <= r; t++)
    ballsum(n - 1, r - abs(t), x + 1, M, (int)md(acc + (int64_t)t * x[0], M), lhs);
}

static uint64_t lcg = 1970;
static int rnd(int k) { lcg = lcg * 6364136223846793005ULL + 1442695040888963407ULL; return (int)((lcg >> 33) % (uint64_t)k); }

static int rank_mod(int64_t m[][28], int rows, int cols, int64_t p) {
  int rank = 0;
  for (int c = 0; c < cols && rank < rows; c++) {
    int piv = -1;
    for (int r = rank; r < rows; r++) if (m[r][c]) { piv = r; break; }
    if (piv < 0) continue;
    for (int j = 0; j < cols; j++) { int64_t t = m[rank][j]; m[rank][j] = m[piv][j]; m[piv][j] = t; }
    int64_t inv = pw(m[rank][c], p - 2, p);
    for (int j = 0; j < cols; j++) m[rank][j] = m[rank][j] * inv % p;
    for (int r = 0; r < rows; r++) if (r != rank && m[r][c]) {
      int64_t k = m[r][c];
      for (int j = 0; j < cols; j++) m[r][j] = md(m[r][j] - k * m[rank][j], p);
    }
    rank++;
  }
  return rank;
}

int main(void) {
  char buf[256];

  /* sizes of the balls */
  int ok = 1;
  for (int n = 0; n <= 7; n++) ok &= (6 * ballcount(n, 3) == f(n, 2 * n + 1));
  check(ok, "|B^n(3)| = f_n(2n+1)/6 for n <= 7 by counting");
  int64_t B35 = f(35, 71) / 6, B805 = f(805, 1611) / 6;
  check(f(35, 71) % 6 == 0 && B35 == 59711 && B35 == 29 * 29 * 71, "|B^35(3)| = 59711 = 29^2 * 71");
  check(f(805, 1611) % 6 == 0 && B805 == 696845031 && B805 == 3LL * 29 * 29 * 179 * 1543 && B805 < (1LL << 30),
        "|B^805(3)| = 696845031 = 3 * 29^2 * 179 * 1543 < 2^30");
  int primes_ok = 1;
  int64_t pr[] = {29, 71, 179, 1543};
  for (int i = 0; i < 4; i++) for (int64_t d = 2; d * d <= pr[i]; d++) if (pr[i] % d == 0) primes_ok = 0;
  check(primes_ok, "29, 71, 179 and 1543 are prime");

  /* the ball identity in Z[Z/M] */
  for (int trial = 0; trial < 16; trial++) {
    int n = 1 + rnd(5), M = 2 + rnd(45), x[8];
    for (int j = 0; j < n; j++) x[j] = rnd(M);
    int64_t lhs[64] = {0}, T[4][64], P12[64] = {0}, C[64] = {0}, Sq[64] = {0}, rhs[64];
    ballsum(n, 3, x, M, 0, lhs);
    for (int i = 1; i <= 3; i++) {
      memset(T[i], 0, sizeof T[i]);
      T[i][0] += 1;
      for (int j = 0; j < n; j++) { T[i][md((int64_t)i * x[j], M)]++; T[i][md(-(int64_t)i * x[j], M)]++; }
    }
    for (int s = 0; s < M; s++) for (int t = 0; t < M; t++) {
      Sq[(s + t) % M] += T[1][s] * T[1][t];
      P12[(s + t) % M] += T[1][s] * T[2][t];
    }
    for (int s = 0; s < M; s++) for (int t = 0; t < M; t++) C[(s + t) % M] += Sq[s] * T[1][t];
    int same = 1;
    for (int s = 0; s < M; s++) {
      rhs[s] = C[s] + 3 * P12[s] + 2 * T[3][s] - 6 * (int64_t)n * T[1][s];
      if (rhs[s] != lhs[s]) same = 0;
    }
    snprintf(buf, sizeof buf, "ball identity in Z[Z/%d] with n = %d (trial %d)", M, n, trial + 1);
    check(same, buf);
  }

  /* Section 5: n = 805, p = 29 */
  int64_t want805[] = {24, 19, 23, 23, 24, 8, 25, 10, 15, 11, 11, 10, 26, 9};
  ok = 1;
  for (int i = 0; i < 14; i++) ok &= (kappa(805, 2 * (i + 1), 29) == want805[i]);
  check(ok, "Table 1, row kappa_805(v) mod 29");
  ok = 1;
  for (int v = 1; v <= 28; v++) ok &= (kappa(805, v, 29) == md(2 * pw(2, 5 * v, 29) + 19 * pw(2, v, 29) + 17, 29));
  check(ok, "kappa_805(v) = 2 z^5 + 19 z + 17, z = 2^v, mod 29");
  int64_t m805 = B805 / 29;
  check(m805 == 24029139 && m805 % 29 == 0, "m = 24029139 is divisible by 29");
  check(805 % 29 == 22 && 805 == 22 + 29 * 27, "805 = 22 + 29 * 27");
  check(md(6 * m805, 841) == 29 * 18 && (6 * m805 / 29) % 29 == 18, "6m = 29 * 4971546 and 4971546 = 18 mod 29");
  check(f(805, 45) == -120060 && md(f(805, 45), 841) == 29 * 7, "f_805(45) = -120060 = 29 * 7 mod 841");
  check(3 * 45 * 45 + 6 * 45 + 2 - 6 * 805 == 1517 && 1517 % 29 == 9, "f_805'(45) = 1517 = 9 mod 29");
  ok = 1;
  for (int64_t k = 0; k <= 28; k++) ok &= (md(f(805, 45 + 58 * k), 841) == md(29 * (7 + 18 * k), 841));
  check(ok, "f_805(45 + 58k) = 29 (7 + 18k) mod 841 for 0 <= k <= 28");
  int nsol = 0, sol[8];
  for (int64_t c = 0; c < 841; c++) if (md(f(805, 1 + 2 * c), 841) == md(6 * m805, 841)) { if (nsol < 8) sol[nsol] = (int)c; nsol++; }
  check(nsol == 3 && sol[0] == 101 && sol[1] == 744 && sol[2] == 834, "the solutions c in [0, 840] are 101, 744 and 834");
  ok = 1;
  for (int64_t c = 22; c <= 805; c += 29) ok &= (md(f(805, 1 + 2 * c), 841) != md(6 * m805, 841));
  check(ok, "no c <= 805 with c = 22 mod 29 satisfies 6m = f(1+2c) mod 841");

  /* Section 6.1: n = 35, p = 71 */
  ok = 1;
  for (int v = 1; v <= 70; v++) ok &= (kappa(35, v, 71) != 0 && kappa(35, v, 71) == md(2 * pw(3, v, 71) + 3, 71));
  check(ok, "kappa_35(v) = 2 * 3^v + 3 != 0 mod 71 for 1 <= v <= 70");
  check(kappa(35, 70, 71) == 5 && md(6 * 841, 71) == 5, "kappa_35(70) = 5 = 6m mod 71, so P_70 = -1 and D = 1");
  check(pw(3, 35, 71) == 1 && pw(70, 35, 71) == 70, "3 is a square, -1 is not, mod 71");

  /* Section 6.2: n = 35, p = 29 */
  int64_t want35[] = {17, 20, 27, 10, 1, 3, 5, 17, 14, 7, 24, 4, 2, 0};
  ok = 1;
  for (int i = 0; i < 14; i++) ok &= (kappa(35, 2 * (i + 1), 29) == want35[i]);
  check(ok, "Table 1, row kappa_35(v) mod 29");
  int ncase = 0, cs[8][2];
  for (int D = 0; D < 29; D++) for (int c = 0; c <= 35; c++)
    if (28 * D + 2 * c <= 70 && md(2 * c - 70 - D, 29) == 0) { cs[ncase][0] = D; cs[ncase][1] = c; ncase++; }
  check(ncase == 4 && cs[0][0] == 0 && cs[0][1] == 6 && cs[1][0] == 0 && cs[1][1] == 35 &&
        cs[2][0] == 1 && cs[2][1] == 21 && cs[3][0] == 2 && cs[3][1] == 7, "cases (D, c(0)) = (0,6), (0,35), (1,21), (2,7)");
  check(B35 / 29 == 2059 && md(6 * 2059, 841) == 580, "6m = 12354 = 580 mod 841");
  check(f(35, 13) == 0 && md(f(35, 71), 841) == 0, "case (a): f_35(13) = 0 and f_35(71) = 0 mod 841");

  /* Section 6.4: the joint relation */
  int64_t AA[2] = {42, 13}, ab[2][2] = {{16, 42}, {56, 13}};
  for (int i = 0; i < 2; i++) {
    int64_t A = AA[i], c0 = md(3 * A * A + 3 * A - 6 * 35, 71), c1 = md(6 * A, 71);
    snprintf(buf, sizeof buf, "A = %lld: 12 * (3A^2 + 3A - 210, 6A, 6) = (%lld, %lld, 1) mod 71",
             (long long)A, (long long)ab[i][0], (long long)ab[i][1]);
    check(md(12 * c0, 71) == ab[i][0] && md(12 * c1, 71) == ab[i][1] && md(12 * 6, 71) == 1, buf);
  }
  check(f(35, 42) != 0 && f(35, 13) == 0, "over Z: f_35(42) != 0 and f_35(13) = 0");

  /* Section 6.5: orbit of 15 and the circulant systems */
  int ord = 0;
  for (int k = 1; k <= 28; k++) if (pw(15, k, 29) == 1) { ord = k; break; }
  check(ord == 28 && pw(15, 14, 29) == 28 && pw(15, 5, 29) == 10 && (2 * 15) % 29 == 1 && (3 * 10) % 29 == 1,
        "15 = 2^-1 has order 28 mod 29, 15^14 = -1, 15^5 = 10 = 3^-1");
  for (int i = 0; i < 2; i++) {
    /* unknowns mu_0..mu_13; mu_{k+14} = -mu_k; equations for k = 0..27 */
    static int64_t m[28][28];
    memset(m, 0, sizeof m);
    int64_t coef[3] = {ab[i][0], ab[i][1], 1};
    int off[3] = {0, 1, 5};
    for (int k = 0; k < 28; k++)
      for (int t = 0; t < 3; t++) {
        int idx = (k + off[t]) % 28;
        int64_t sgn = idx < 14 ? 1 : -1;
        m[k][idx % 14] = md(m[k][idx % 14] + sgn * coef[t], 71);
      }
    snprintf(buf, sizeof buf, "(a, b) = (%lld, %lld): the system in mu_0, ..., mu_13 has rank 14 over F_71",
             (long long)ab[i][0], (long long)ab[i][1]);
    check(rank_mod(m, 28, 14, 71) == 14, buf);
  }

  printf("\n%d checks passed, %d failed\n", passed, failures);
  return failures ? 1 : 0;
}
