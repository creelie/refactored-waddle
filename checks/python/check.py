"""Independent check of the arithmetic in the paper.

Every number used in Sections 2 to 6 is recomputed here from its definition:
the sizes of the balls, the ball identity on small groups, the coefficients
kappa_n(v), the case analysis modulo 29 and 71, the congruences modulo 841,
the coefficients of the joint relation, the polynomial identities over F_71
and the rank of the two circulant systems.  The script exits with status 1 on
the first failure.
"""

import itertools
import random
import sys

FAILURES = 0


def check(cond, what):
    global FAILURES
    print(("ok    " if cond else "FAIL  ") + what)
    if not cond:
        FAILURES += 1


def ball(n, r):
    """All a in Z^n with |a_1| + ... + |a_n| <= r."""
    if n == 0:
        return [()]
    out = []
    for t in range(-r, r + 1):
        for rest in ball(n - 1, r - abs(t)):
            out.append((t,) + rest)
    return out


def f(n, A):
    return A ** 3 + 3 * A ** 2 + 2 * A - 6 * n * A


def kappa(n, v, p):
    return (3 * (2 * n + 1) ** 2 + 3 * (2 * n + 1) * (1 + pow(2, v, p))
            + 2 * pow(3, v, p) - 6 * n) % p


def factor(N):
    out, d = [], 2
    while d * d <= N:
        while N % d == 0:
            out.append(d)
            N //= d
        d += 1
    if N > 1:
        out.append(N)
    return out


# --- Section 2: sizes of the balls --------------------------------------
for n in range(0, 7):
    check(len(ball(n, 3)) * 6 == f(n, 2 * n + 1),
          f"|B^{n}(3)| = f(2n+1)/6 by enumeration")
B35, B805 = f(35, 71) // 6, f(805, 1611) // 6
check(f(35, 71) % 6 == 0 and B35 == 59711, "|B^35(3)| = 59711")
check(f(805, 1611) % 6 == 0 and B805 == 696845031, "|B^805(3)| = 696845031")
check(factor(B35) == [29, 29, 71], "59711 = 29^2 * 71")
check(factor(B805) == [3, 29, 29, 179, 1543], "696845031 = 3 * 29^2 * 179 * 1543")
check(B805 < 2 ** 30, "|B^805(3)| < 2^30")

# --- Section 2: the ball identity in Z[Z/M] -----------------------------
rng = random.Random(1970)
for trial in range(12):
    n, M = rng.randint(1, 5), rng.randint(2, 40)
    x = [rng.randrange(M) for _ in range(n)]
    lhs = [0] * M
    for a in ball(n, 3):
        lhs[sum(ai * xi for ai, xi in zip(a, x)) % M] += 6

    def T(i):
        t = [0] * M
        t[0] += 1
        for xi in x:
            t[(i * xi) % M] += 1
            t[(-i * xi) % M] += 1
        return t

    def mul(u, w):
        out = [0] * M
        for s in range(M):
            if u[s]:
                for t in range(M):
                    out[(s + t) % M] += u[s] * w[t]
        return out

    T1, T2, T3 = T(1), T(2), T(3)
    rhs = mul(mul(T1, T1), T1)
    p12 = mul(T1, T2)
    rhs = [rhs[s] + 3 * p12[s] + 2 * T3[s] - 6 * n * T1[s] for s in range(M)]
    check(lhs == rhs, f"ball identity in Z[Z/{M}] with n = {n}, x = {x}")

# --- Lemma 3.4: the Lagrange step ---------------------------------------
for p in (5, 7, 29, 71):
    F = [rng.randrange(p) for _ in range(p)]
    ok = all(sum(F[g] * pow(g - h, p - 1, p) for g in range(p)) % p == (sum(F) - F[h]) % p
             for h in range(p))
    check(ok, f"sum_g F(g)(g-h)^(p-1) = M_0(F) - F(h) over F_{p}")
for p in (29, 71):
    check(all(sum(pow(h, v, p) for h in range(p)) % p == 0 for v in range(1, p - 1))
          and sum(pow(h, p - 1, p) for h in range(p)) % p == p - 1,
          f"power sums of F_{p}")

# --- Section 5: n = 805 -------------------------------------------------
n, p = 805, 29
m = B805 // 29
check(m == 24029139 and m % 29 == 0, "m = |G|/29 = 24029139 is divisible by 29")
k805 = [kappa(n, v, p) for v in range(2, 29, 2)]
check(k805 == [24, 19, 23, 23, 24, 8, 25, 10, 15, 11, 11, 10, 26, 9],
      f"kappa_805(v) mod 29 for v = 2, 4, ..., 28: {k805}")
check(all(kappa(n, v, p) == (2 * pow(2, 5 * v, p) + 19 * pow(2, v, p) + 17) % p
          for v in range(1, 29)), "kappa_805(v) = 2 z^5 + 19 z + 17 with z = 2^v")
check(n % 29 == 22, "805 = 22 mod 29")
check((6 * m) % 841 == 522 and 522 == 29 * 18, "6m = 522 = 29 * 18 mod 841")
check(f(n, 45) == -120060 and f(n, 45) % 841 == 203 == 29 * 7, "f(45) = -120060 = 29 * 7 mod 841")
fp = 3 * 45 ** 2 + 6 * 45 + 2 - 6 * n
check(fp == 1517 and fp % 29 == 9, "f'(45) = 1517 = 9 mod 29")
check((18 * 21) % 29 == 1 and (11 * 21) % 29 == 28, "18k = 11 mod 29 gives k = 28")
sols = [c for c in range(0, 841) if f(n, 1 + 2 * c) % 841 == (6 * m) % 841]
check(sols == [101, 744, 834], f"solutions c in [0, 840] of 6m = f(1+2c) mod 841: {sols}")
check([c for c in sols if c % 29 == 22] == [834] and 834 > 805,
      "the only solution with c = 22 mod 29 is 834 > 805")
check(all(f(n, 1 + 2 * c) % 841 != (6 * m) % 841 for c in range(22, 806, 29)),
      "no c <= 805 with c = 22 mod 29 satisfies the congruence")

# --- Section 6.1: n = 35 modulo 71 --------------------------------------
n = 35
k71 = [kappa(n, v, 71) for v in range(1, 71)]
check(all(k71[v - 1] == (2 * pow(3, v, 71) + 3) % 71 for v in range(1, 71)),
      "kappa_35(v) = 2 * 3^v + 3 mod 71")
check(all(k != 0 for k in k71), "kappa_35(v) != 0 mod 71 for 1 <= v <= 70")
check(pow(3, 35, 71) == 1 and pow(70, 35, 71) == 70 and (36 * 2) % 71 == 1,
      "3 is a square and -1 is not a square mod 71; 2^-1 = 36")
check(k71[69] == 5 and (6 * 841) % 71 == 5, "kappa_35(70) = 5 and 6m = 5 mod 71")
check((5 * (71 - 1)) % 71 == (-6 * 841) % 71, "P_70 = -1 mod 71, so D = 1")

# --- Section 6.2: n = 35 modulo 29 --------------------------------------
k29 = [kappa(n, v, 29) for v in range(2, 29, 2)]
check(k29 == [17, 20, 27, 10, 1, 3, 5, 17, 14, 7, 24, 4, 2, 0],
      f"kappa_35(v) mod 29 for v = 2, 4, ..., 28: {k29}")
check(all(kappa(n, v, 29) == (2 * pow(2, 5 * v, 29) + 10 * pow(2, v, 29) + 17) % 29
          for v in range(1, 29)), "kappa_35(v) = 2 z^5 + 10 z + 17 with z = 2^v")
cases = sorted((D, c) for D in range(29) for c in range(36)
               if 28 * D + 2 * c <= 70 and (2 * c - 2 * n - D) % 29 == 0)
check(cases == [(0, 6), (0, 35), (1, 21), (2, 7)], f"cases (D, c(0)): {cases}")
m = B35 // 29
check(m == 2059 == 29 * 71, "m = |G|/29 = 2059 = 29 * 71")
check((6 * m) % 841 == 580, "6m = 580 mod 841")
check(f(n, 13) == 0 and f(n, 71) % 841 == 0, "f(13) = 0 and f(71) = 0 mod 841")

# --- Section 6.4: the joint relation ------------------------------------
for D, c0, expect, scaled in ((1, 21, (25, 39, 6), (16, 42, 1)), (2, 7, (52, 7, 6), (56, 13, 1))):
    A = 1 + 2 * c0 - D
    coeffs = ((3 * A * A + 3 * A - 6 * n) % 71, (6 * A) % 71, 6)
    check(coeffs == expect, f"D = {D}: A = {A}, coefficients {coeffs}")
    check(tuple((12 * c) % 71 for c in coeffs) == scaled and (12 * 6) % 71 == 1,
          f"D = {D}: times 12 = 6^-1 they are {scaled}")
check(all(f(n, 1 + 2 * c0 - D) != 0 for D, c0 in ((1, 21),)) and f(n, 13) == 0,
      "over Z: f(42) != 0 (D = 1 fails), f(13) = 0 (D = 2 passes)")
# Xiao--Zhou's configuration modulo 29: T = 13 + 2S with S^2 = 29 S satisfies the identity
T0, TS = 13, 2
sq = (T0 * T0, 2 * T0 * TS + 29 * TS * TS)
cu = (sq[0] * T0, sq[0] * TS + sq[1] * T0 + 29 * sq[1] * TS)
rhs = (cu[0] + 3 * sq[0] + 2 * T0 - 6 * n * T0, cu[1] + 3 * sq[1] + 2 * TS - 6 * n * TS)
check(rhs == (0, 6 * 2059), "the distribution c(0) = 7, c(h) + c(-h) = 2 satisfies the identity over Z[Z/29]")
# the distribution of Lemma 6.1 (one x_j on each pair, here the squares) gives T_i = S over Z[Z/71]
sq71 = sorted({h * h % 71 for h in range(1, 71)})
check(len(sq71) == 35 and all((h in sq71) != ((71 - h) in sq71) for h in range(1, 71)),
      "the 35 squares mod 71 contain exactly one element of each pair {h, -h}")
check(71 ** 2 + 3 * 71 + 2 - 6 * n == 5046 == 6 * 841,
      "with T_i = S over Z[Z/71] the identity reads 5046 S = 6 * 841 S")

# --- Section 6.5: the circulant step ------------------------------------
check(pow(2, 7, 29) == 12 and (12 * 12) % 29 == 28, "2^7 = 12 and 12^2 = -1 mod 29")
orders = [k for k in range(1, 29) if pow(15, k, 29) == 1]
check(orders[0] == 28 and pow(15, 14, 29) == 28 and pow(15, 5, 29) == 10 and (2 * 15) % 29 == 1
      and (3 * 10) % 29 == 1, "15 = 2^-1 has order 28, 15^14 = -1, 15^5 = 10 = 3^-1")

P = 71


def norm(a):
    a = [c % P for c in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n_ = max(len(a), len(b))
    return norm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n_)])


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return norm(out)


def pscale(c, a):
    return norm([c * x for x in a])


def poly(*coeffs_high_to_low):
    return norm(list(reversed(coeffs_high_to_low)))


X = [0, 1]
for a, b, Ct, q1, r1, q2, r2, lam, final in (
        (16, 42, poly(1, -9, 29, -27), poly(1, 9, -19), pmul(pscale(21, X), poly(1, 6)),
         pmul(poly(1, -15), pmul(X, poly(1, 6))), pscale(-23, poly(1, -5)), 5, 55),
        (56, 13, poly(1, 2, -28, -26), poly(1, -2, 32), pscale(-23, pmul(poly(1, -14), poly(1, -14))),
         pmul(poly(1, 30), pmul(poly(1, -14), poly(1, -14))), pscale(-23, poly(1, 16)), -16, 48)):
    Q = poly(1, 0, 0, 0, b, a)
    lin = poly(b, a)
    C = padd(pmul(lin, pmul(lin, lin)), pscale(-1, X))
    unit = (-2) if a == 16 else (-18)
    check(pscale(unit, C) == Ct, f"(a, b) = ({a}, {b}): {unit} * C = C~ = {Ct}")
    check(padd(pmul(q1, Ct), r1) == Q, f"(a, b) = ({a}, {b}): Q = q1 C~ + r1")
    check(padd(q2, r2) == Ct, f"(a, b) = ({a}, {b}): C~ = q2 + r2")
    if a == 16:
        val = (lam * (lam + 6)) % P
    else:
        val = ((lam - 14) ** 2) % P
    check(val == final and final != 0, f"(a, b) = ({a}, {b}): sigma = {lam} gives the factor {val} != 0")
    # rank of the 28 x 28 circulant system a mu_k + b mu_{k+1} + mu_{k+5} = 0
    Mx = [[0] * 28 for _ in range(28)]
    for k in range(28):
        Mx[k][k] = (Mx[k][k] + a) % P
        Mx[k][(k + 1) % 28] = (Mx[k][(k + 1) % 28] + b) % P
        Mx[k][(k + 5) % 28] = (Mx[k][(k + 5) % 28] + 1) % P
    rank, rows = 0, [r[:] for r in Mx]
    for col in range(28):
        piv = next((r for r in range(rank, 28) if rows[r][col]), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], P - 2, P)
        rows[rank] = [(v * inv) % P for v in rows[rank]]
        for r in range(28):
            if r != rank and rows[r][col]:
                c = rows[r][col]
                rows[r] = [(v - c * w) % P for v, w in zip(rows[r], rows[rank])]
        rank += 1
    check(rank == 28, f"(a, b) = ({a}, {b}): the 28-periodic system has only the zero solution")

print()
if FAILURES:
    print(f"{FAILURES} check(s) failed")
    sys.exit(1)
print("all checks passed")
