// check.cpp -- independent check of Sections 6.4 and 6.5 of the paper, in C++20.
//
// The joint projection is computed directly in the ring F_71[F_29][eps]/(eps^2) for explicit
// residues x_j, y_j with the distributions of cases (b) and (c); the coefficient of eps is
// compared with the relation a s(t) + b s(15 t) + s(10 t) = 0 of the paper (up to the factor 6).
// The projected identity is checked over Z[Z/29] and Z[Z/71] for the distributions of Remark 6.3,
// and the circulant step is checked by Euclid's algorithm over F_71: gcd(X^5 + bX + a, X^14 + 1)
// = 1, together with the division identities stated in the paper.  Exits with status 1 on failure.
//
// Build: c++ -O2 -std=c++20 -o check check.cpp && ./check
#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <tuple>
#include <cstdio>
#include <string>
#include <vector>

namespace {

int failures = 0, passed = 0;

void check(bool cond, const std::string &what) {
  std::printf("%s%s\n", cond ? "ok    " : "FAIL  ", what.c_str());
  (cond ? passed : failures)++;
}

using i64 = std::int64_t;
i64 md(i64 a, i64 p) { a %= p; return a < 0 ? a + p : a; }
i64 pw(i64 b, i64 e, i64 p) { i64 r = 1; b = md(b, p); for (; e; e >>= 1, b = b * b % p) if (e & 1) r = r * b % p; return r; }

// ---------------------------------------------------------------- group rings Z[Z/M]
using GR = std::vector<i64>;
GR conv(const GR &u, const GR &w, i64 M, i64 mod) {
  GR o(M, 0);
  for (i64 s = 0; s < M; s++) if (u[s]) for (i64 t = 0; t < M; t++) o[(s + t) % M] = mod ? md(o[(s + t) % M] + u[s] * w[t], mod) : o[(s + t) % M] + u[s] * w[t];
  return o;
}
GR Tgr(const std::vector<i64> &x, i64 i, i64 M) {
  GR t(M, 0); t[0] += 1;
  for (i64 xj : x) { t[md(i * xj, M)]++; t[md(-i * xj, M)]++; }
  return t;
}
GR rhs(const std::vector<i64> &x, i64 n, i64 M) {
  GR T1 = Tgr(x, 1, M), T2 = Tgr(x, 2, M), T3 = Tgr(x, 3, M);
  GR c = conv(conv(T1, T1, M, 0), T1, M, 0), p = conv(T1, T2, M, 0), o(M);
  for (i64 s = 0; s < M; s++) o[s] = c[s] + 3 * p[s] + 2 * T3[s] - 6 * n * T1[s];
  return o;
}

// ---------------------------------------------------------------- dual numbers over F_71[F_29]
struct Dual { GR u, e; };  // u + e * eps
Dual dmul(const Dual &a, const Dual &b) {
  GR uu = conv(a.u, b.u, 29, 71), ue = conv(a.u, b.e, 29, 71), eu = conv(a.e, b.u, 29, 71), e(29);
  for (int t = 0; t < 29; t++) e[t] = md(ue[t] + eu[t], 71);
  return {uu, e};
}
// T_i = [0] + sum_j (chi(i z_j) + chi(-i z_j)), chi(s, t) = [t](1 + s eps)
Dual Tdual(const std::vector<i64> &x, const std::vector<i64> &y, i64 i) {
  Dual T{GR(29, 0), GR(29, 0)};
  T.u[0] = 1;
  for (std::size_t j = 0; j < x.size(); j++) {
    i64 tp = md(i * y[j], 29), tm = md(-i * y[j], 29);
    T.u[tp] = md(T.u[tp] + 1, 71); T.e[tp] = md(T.e[tp] + i * x[j], 71);
    T.u[tm] = md(T.u[tm] + 1, 71); T.e[tm] = md(T.e[tm] - i * x[j], 71);
  }
  return T;
}

// ---------------------------------------------------------------- polynomials over F_71
using Poly = std::vector<i64>;  // low to high
Poly norm(Poly a) { for (auto &c : a) c = md(c, 71); while (a.size() > 1 && a.back() == 0) a.pop_back(); return a; }
Poly hi(std::initializer_list<i64> c) { Poly a(c.begin(), c.end()); return norm(Poly(a.rbegin(), a.rend())); }
Poly mul(const Poly &a, const Poly &b) {
  Poly o(a.size() + b.size() - 1, 0);
  for (std::size_t i = 0; i < a.size(); i++) for (std::size_t j = 0; j < b.size(); j++) o[i + j] = md(o[i + j] + a[i] * b[j], 71);
  return norm(o);
}
Poly add(const Poly &a, const Poly &b) {
  Poly o(std::max(a.size(), b.size()), 0);
  for (std::size_t i = 0; i < a.size(); i++) o[i] += a[i];
  for (std::size_t i = 0; i < b.size(); i++) o[i] += b[i];
  return norm(o);
}
Poly scale(i64 c, const Poly &a) { Poly o = a; for (auto &x : o) x *= c; return norm(o); }
void divmod(Poly a, const Poly &b, Poly &q, Poly &r) {
  a = norm(a);
  q.assign(a.size() >= b.size() ? a.size() - b.size() + 1 : 1, 0);
  i64 inv = pw(b.back(), 69, 71);
  while (a.size() >= b.size() && !(a.size() == 1 && a[0] == 0)) {
    std::size_t d = a.size() - b.size();
    i64 c = a.back() * inv % 71;
    q[d] = c;
    for (std::size_t i = 0; i < b.size(); i++) a[i + d] = md(a[i + d] - c * b[i], 71);
    a = norm(a);
    if (a.size() < b.size() || (a.size() == 1 && a[0] == 0)) break;
  }
  q = norm(q); r = a;
}
Poly gcd(Poly a, Poly b) {
  a = norm(a); b = norm(b);
  while (!(b.size() == 1 && b[0] == 0)) { Poly q, r; divmod(a, b, q, r); a = b; b = r; }
  return scale(pw(a.back(), 69, 71), a);
}

}  // namespace

int main() {
  const i64 n = 35;

  // ---------------------------------------- Remark 6.3: the projected identity for each prime
  std::vector<i64> yb, yc;  // case (b): 21 zeros, one residue on each pair; case (c): 7 zeros, two on each pair
  for (int k = 0; k < 21; k++) yb.push_back(0);
  for (i64 t = 1; t <= 14; t++) yb.push_back(t % 2 ? t : 29 - t);
  for (int k = 0; k < 7; k++) yc.push_back(0);
  for (i64 t = 1; t <= 14; t++) {
    if (t % 3 == 0) { yc.push_back(t); yc.push_back(29 - t); }
    else if (t % 3 == 1) { yc.push_back(t); yc.push_back(t); }
    else { yc.push_back(29 - t); yc.push_back(29 - t); }
  }
  check(yb.size() == 35 && yc.size() == 35, "the two distributions modulo 29 have 35 residues");
  GR Rc = rhs(yc, n, 29), Rb = rhs(yb, n, 29);
  bool all12354 = true;
  for (i64 v : Rc) all12354 &= (v == 12354);
  check(all12354 && 12354 == 6 * 2059, "case (c): the right side over Z[Z/29] is 12354 S = 6m S");
  check(Rb[0] != Rb[1], "case (b): the right side over Z[Z/29] is not a multiple of S");
  std::vector<i64> x71;
  for (i64 h = 1; h <= 35; h++) x71.push_back(h * h % 71);
  GR R71 = rhs(x71, n, 71);
  bool all5046 = true;
  for (i64 v : R71) all5046 &= (v == 5046);
  check(all5046 && 5046 == 6 * 841, "x_j = j^2 mod 71: the right side over Z[Z/71] is 5046 S = 6 * 841 S");

  // ---------------------------------------- Section 6.4: the eps part, computed in the dual numbers
  std::uint64_t seed = 1970;
  auto rnd = [&](i64 k) { seed = seed * 6364136223846793005ULL + 1442695040888963407ULL; return (i64)((seed >> 33) % (std::uint64_t)k); };
  struct Case { const std::vector<i64> *y; i64 A, a, b; const char *name; };
  for (Case cs : {Case{&yb, 42, 16, 42, "(b)"}, Case{&yc, 13, 56, 13, "(c)"}}) {
    bool rel_ok = true, zero_ok = true;
    for (int trial = 0; trial < 6; trial++) {
      std::vector<i64> x(35);
      for (auto &v : x) v = rnd(71);
      Dual T1 = Tdual(x, *cs.y, 1), T2 = Tdual(x, *cs.y, 2), T3 = Tdual(x, *cs.y, 3);
      Dual c = dmul(dmul(T1, T1), T1), p = dmul(T1, T2);
      GR eps(29);
      for (int t = 0; t < 29; t++) eps[t] = md(c.e[t] + 3 * p.e[t] + 2 * T3.e[t] - 6 * n * T1.e[t], 71);
      std::vector<i64> s(29, 0);
      for (int j = 0; j < 35; j++) { s[(*cs.y)[j]] = md(s[(*cs.y)[j]] + x[j], 71); s[md(-(*cs.y)[j], 29)] = md(s[md(-(*cs.y)[j], 29)] - x[j], 71); }
      for (int t = 0; t < 29; t++) {
        i64 rel = md(cs.a * s[t] + cs.b * s[t * 15 % 29] + s[t * 10 % 29], 71);
        rel_ok &= (eps[t] == md(6 * rel, 71));
      }
      // the left side: 6 * 29 * sum over (s,t) in F_71 x F_29 of [t](1 + s eps) has eps part 0
      i64 lhs = 0;
      for (i64 sv = 0; sv < 71; sv++) lhs = md(lhs + 6 * 29 * sv, 71);
      zero_ok &= (lhs == 0);
    }
    check(rel_ok, std::string("case ") + cs.name + ": the eps part of the right side is 6 (a s(t) + b s(15t) + s(10t)) at every t");
    check(zero_ok, std::string("case ") + cs.name + ": the eps part of the left side is 0");
  }

  // ---------------------------------------- Section 6.5: Euclid over F_71
  Poly X = hi({1, 0}), X14p1 = norm([] { Poly p(15, 0); p[0] = 1; p[14] = 1; return p; }());
  for (auto [a, b, unit] : {std::tuple<i64, i64, i64>{16, 42, -2}, std::tuple<i64, i64, i64>{56, 13, -18}}) {
    Poly Q = hi({1, 0, 0, 0, b, a}), lin = hi({b, a});
    Poly C = add(mul(lin, mul(lin, lin)), scale(-1, X));
    check(gcd(Q, X14p1) == Poly{1}, "(a, b) = (" + std::to_string(a) + ", " + std::to_string(b) + "): gcd(X^5 + bX + a, X^14 + 1) = 1 over F_71");
    Poly Ct = scale(unit, C), q1, r1, q2, r2;
    divmod(Q, Ct, q1, r1);
    if (a == 16) {
      check(Ct == hi({1, -9, 29, -27}), "case (b): -2C = X^3 - 9X^2 + 29X - 27");
      check(q1 == hi({1, 9, -19}) && r1 == mul(scale(21, X), hi({1, 6})), "case (b): Q = (X^2 + 9X - 19) C~ + 21 X (X + 6)");
      divmod(Ct, mul(X, hi({1, 6})), q2, r2);
      check(q2 == hi({1, -15}) && r2 == scale(-23, hi({1, -5})), "case (b): C~ = (X - 15) X (X + 6) - 23 (X - 5)");
    } else {
      check(Ct == hi({1, 2, -28, -26}), "case (c): -18C = X^3 + 2X^2 - 28X - 26");
      Poly sq = mul(hi({1, -14}), hi({1, -14}));
      check(q1 == hi({1, -2, 32}) && r1 == scale(-23, sq), "case (c): Q = (X^2 - 2X + 32) C~ - 23 (X - 14)^2");
      divmod(Ct, sq, q2, r2);
      check(q2 == hi({1, 30}) && r2 == scale(-23, hi({1, 16})), "case (c): C~ = (X + 30)(X - 14)^2 - 23 (X + 16)");
    }
    // C lies in the ideal generated by Q and X^14 + 1: X^15 = -X modulo X^14 + 1, and X^15 = -(a + bX)^3 modulo Q
    Poly x15 = Poly(16, 0); x15[15] = 1;
    Poly qa, ra, qb, rb;
    divmod(add(x15, X), X14p1, qa, ra);
    divmod(add(x15, mul(lin, mul(lin, lin))), Q, qb, rb);
    check(ra == Poly{0} && rb == Poly{0}, "(a, b) = (" + std::to_string(a) + ", " + std::to_string(b) + "): X^14 + 1 divides X^15 + X and Q divides X^15 + (a + bX)^3");
  }

  std::printf("\n%d checks passed, %d failed\n", passed, failures);
  return failures ? 1 : 0;
}
