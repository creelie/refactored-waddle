"""Equivalence of points of R under Gamma = {T = [[U, v], [0, eps]] : U in GL_d(Z), v in Z^d, eps = +-1},
acting by J -> T^T J T.  We search T with T^T J T = J2, i.e. J2[x] = J[Tx]; T maps Min(J2) onto +-Min(J)."""
from fractions import Fraction as F
from collections import Counter
from forms import det, min_vectors, blocks

def bil(J, x, y):
    n = len(J)
    return sum(J[i][j] * x[i] * y[j] for i in range(n) for j in range(n) if x[i] and y[j])

def signed(vs):
    out = []
    for v in vs:
        out.append(tuple(v))
        out.append(tuple(-a for a in v))
    return out

def invariant(J, mv=None):
    if mv is None:
        mv = min_vectors(J)
    Q, r, s = blocks(J)
    n = len(J)
    S = signed(mv)
    hist = Counter()
    for x in mv:
        for y in S:
            hist[(abs(x[-1]), abs(y[-1]), bil(J, x, y))] += 1
    return (det(Q), det(J), len(mv), sum(1 for v in mv if v[-1] == 0), tuple(sorted(hist.items())))

def _inv_int(B):
    """inverse of an integer matrix (list of columns -> matrix), as Fractions."""
    n = len(B)
    M = [[F(B[j][i]) for j in range(n)] + [F(1 if i == k else 0) for k in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        iv = 1 / M[c][c]
        M[c] = [x * iv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]

def _choose_basis(S2):
    """greedy: linearly independent vectors from S2 (prefer small determinant at the end)."""
    from forms import rank
    basis = []
    for v in S2:
        if rank(basis + [v]) > len(basis):
            basis.append(v)
            if len(basis) == len(S2[0]):
                break
    return basis

def isometries(J, J2, mv=None, mv2=None, first=True):
    """T with T^T J T = J2 (all of them if first=False)."""
    n = len(J)
    if mv is None:
        mv = min_vectors(J)
    if mv2 is None:
        mv2 = min_vectors(J2)
    if len(mv) != len(mv2):
        return []
    S = signed(mv)
    S2 = signed(mv2)
    basis = _choose_basis(S2)
    if len(basis) < n:
        raise ValueError("Min does not span")
    Binv = _inv_int(basis)
    G2 = [[bil(J2, a, b) for b in basis] for a in basis]
    found = []
    # candidate lists: same J-norm (all are 4), |l| equal
    cand = [[c for c in S if abs(c[-1]) == abs(b[-1])] for b in basis]

    def finish(C, eps):
        # T = C * B^{-1}; C columns are images
        T = [[sum(F(C[k][i]) * Binv[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        for row in T:
            for x in row:
                if x.denominator != 1:
                    return None
        T = [[int(x) for x in row] for row in T]
        if any(T[n - 1][j] != 0 for j in range(n - 1)) or abs(T[n - 1][n - 1]) != 1:
            return None
        U = [row[:n - 1] for row in T[:n - 1]]
        if abs(det([[F(x) for x in row] for row in U])) != 1:
            return None
        # check T^T J T == J2
        JT = [[sum(J[i][k] * T[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                if sum(T[k][i] * JT[k][j] for k in range(n)) != J2[i][j]:
                    return None
        return T

    def rec(i, C, eps):
        if i == n:
            T = finish(C, eps)
            if T is not None:
                found.append(T)
                return first
            return False
        b = basis[i]
        for c in cand[i]:
            if b[-1] != 0:
                e = 1 if c[-1] == b[-1] else -1
                if eps is not None and e != eps:
                    continue
            else:
                e = eps
            if bil(J, c, c) != G2[i][i]:
                continue
            if all(bil(J, c, C[j]) == G2[i][j] for j in range(i)):
                C.append(c)
                if rec(i + 1, C, e):
                    return True
                C.pop()
        return False

    rec(0, [], None)
    return found
