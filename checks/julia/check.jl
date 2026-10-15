# check.jl -- independent check of the arithmetic in the paper, in Julia (no packages).
#
# Recomputes the sizes of the balls, the ball identity in Z[Z/M] on small cases, Table 1,
# the congruences modulo 841 for n = 805, the case analysis for n = 35 modulo 71 and 29,
# the coefficients of the joint relation and the rank of the two circulant systems over F_71.
# Exits with status 1 if any check fails.
#
# Run: julia check.jl

const PASSED = Ref(0)
const FAILED = Ref(0)

function check(cond::Bool, what::AbstractString)
    println((cond ? "ok    " : "FAIL  ") * what)
    if cond
        PASSED[] += 1
    else
        FAILED[] += 1
    end
end

f(n::Int, A::Int) = A^3 + 3 * A^2 + 2 * A - 6 * n * A

kappa(n::Int, v::Int, p::Int) =
    mod(3 * (2n + 1)^2 + 3 * (2n + 1) * (1 + powermod(2, v, p)) + 2 * powermod(3, v, p) - 6n, p)

ballcount(n::Int, r::Int) = n == 0 ? 1 : sum(ballcount(n - 1, r - abs(t)) for t in -r:r)

# all a in Z^n with |a| <= r, as vectors
function ballpoints(n::Int, r::Int)
    n == 0 && return [Int[]]
    pts = Vector{Vector{Int}}()
    for t in -r:r, rest in ballpoints(n - 1, r - abs(t))
        push!(pts, vcat([t], rest))
    end
    return pts
end

# convolution in Z[Z/M]; index k + 1 holds the coefficient of [k]
function conv(u::Vector{Int}, w::Vector{Int}, M::Int)
    o = zeros(Int, M)
    for s in 0:M-1, t in 0:M-1
        o[mod(s + t, M) + 1] += u[s + 1] * w[t + 1]
    end
    return o
end

function Tgr(x::Vector{Int}, i::Int, M::Int)
    t = zeros(Int, M)
    t[1] += 1
    for xj in x
        t[mod(i * xj, M) + 1] += 1
        t[mod(-i * xj, M) + 1] += 1
    end
    return t
end

function rankmod(A::Matrix{Int}, p::Int)
    m = copy(A)
    rows, cols = size(m)
    rank = 0
    for c in 1:cols
        piv = 0
        for r in rank+1:rows
            if m[r, c] != 0
                piv = r
                break
            end
        end
        piv == 0 && continue
        rank += 1
        m[rank, :], m[piv, :] = m[piv, :], m[rank, :]
        iv = powermod(m[rank, c], p - 2, p)
        m[rank, :] = mod.(m[rank, :] .* iv, p)
        for r in 1:rows
            if r != rank && m[r, c] != 0
                k = m[r, c]
                m[r, :] = mod.(m[r, :] .- k .* m[rank, :], p)
            end
        end
    end
    return rank
end

# ---------------------------------------------------------------- sizes of the balls
check(all(6 * ballcount(n, 3) == f(n, 2n + 1) for n in 0:7), "|B^n(3)| = f_n(2n+1)/6 for n <= 7")
B35 = div(f(35, 71), 6)
B805 = div(f(805, 1611), 6)
check(mod(f(35, 71), 6) == 0 && B35 == 59711 == 29^2 * 71, "|B^35(3)| = 59711 = 29^2 * 71")
check(mod(f(805, 1611), 6) == 0 && B805 == 696845031 == 3 * 29^2 * 179 * 1543 && B805 < 2^30,
      "|B^805(3)| = 696845031 = 3 * 29^2 * 179 * 1543 < 2^30")

# ---------------------------------------------------------------- the ball identity in Z[Z/M]
for (n, M, x) in ((2, 7, [1, 3]), (3, 11, [2, 5, 7]), (4, 13, [1, 4, 6, 9]), (3, 25, [3, 8, 20]),
                  (5, 31, [1, 2, 5, 11, 30]), (4, 40, [0, 7, 13, 21]))
    lhs = zeros(Int, M)
    for a in ballpoints(n, 3)
        lhs[mod(sum(a .* x), M) + 1] += 6
    end
    T1, T2, T3 = Tgr(x, 1, M), Tgr(x, 2, M), Tgr(x, 3, M)
    rhs = conv(conv(T1, T1, M), T1, M) .+ 3 .* conv(T1, T2, M) .+ 2 .* T3 .- 6n .* T1
    check(lhs == rhs, "ball identity in Z[Z/$M] with n = $n, x = $x")
end

# ---------------------------------------------------------------- Section 5: n = 805
check([kappa(805, v, 29) for v in 2:2:28] == [24, 19, 23, 23, 24, 8, 25, 10, 15, 11, 11, 10, 26, 9],
      "Table 1, row kappa_805(v) mod 29")
m805 = div(B805, 29)
check(m805 == 24029139 && mod(m805, 29) == 0, "m = 24029139 is divisible by 29")
check(mod(6 * m805, 841) == 29 * 18, "6m = 29 * 18 mod 841")
check(f(805, 45) == -120060 && mod(f(805, 45), 841) == 29 * 7, "f_805(45) = -120060 = 29 * 7 mod 841")
sols = [c for c in 0:840 if mod(f(805, 1 + 2c), 841) == mod(6 * m805, 841)]
check(sols == [101, 744, 834], "the solutions c in [0, 840] are $sols")
check(all(mod(f(805, 1 + 2c), 841) != mod(6 * m805, 841) for c in 22:29:805),
      "no c <= 805 with c = 22 mod 29 satisfies 6m = f(1+2c) mod 841")

# ---------------------------------------------------------------- Section 6.1: n = 35, p = 71
k71 = [kappa(35, v, 71) for v in 1:70]
check(all(k71[v] == mod(2 * powermod(3, v, 71) + 3, 71) != 0 for v in 1:70),
      "kappa_35(v) = 2 * 3^v + 3 != 0 mod 71 for 1 <= v <= 70")
check(k71[70] == 5 && mod(6 * 841, 71) == 5, "kappa_35(70) = 5 = 6m mod 71")

# ---------------------------------------------------------------- Section 6.2: n = 35, p = 29
check([kappa(35, v, 29) for v in 2:2:28] == [17, 20, 27, 10, 1, 3, 5, 17, 14, 7, 24, 4, 2, 0],
      "Table 1, row kappa_35(v) mod 29")
cases = [(D, c) for D in 0:28 for c in 0:35 if 28D + 2c <= 70 && mod(2c - 70 - D, 29) == 0]
check(cases == [(0, 6), (0, 35), (1, 21), (2, 7)], "cases (D, c(0)) = $cases")
check(div(B35, 29) == 2059 && mod(6 * 2059, 841) == 580, "6m = 12354 = 580 mod 841")
check(f(35, 13) == 0 && mod(f(35, 71), 841) == 0, "case (a): f_35(13) = 0 and f_35(71) = 0 mod 841")

# ---------------------------------------------------------------- Section 6.4
for (A, a, b) in ((42, 16, 42), (13, 56, 13))
    c0 = mod(3A^2 + 3A - 210, 71)
    c1 = mod(6A, 71)
    check(mod(12 * c0, 71) == a && mod(12 * c1, 71) == b && mod(12 * 6, 71) == 1,
          "A = $A: 12 * (3A^2 + 3A - 210, 6A, 6) = ($a, $b, 1) mod 71")
end

# ---------------------------------------------------------------- Section 6.5
check(findfirst(k -> powermod(15, k, 29) == 1, 1:28) == 28 && powermod(15, 14, 29) == 28 &&
      powermod(15, 5, 29) == 10, "15 has order 28 mod 29, 15^14 = -1, 15^5 = 10")
for (a, b) in ((16, 42), (56, 13))
    # unknowns mu_0, ..., mu_13 with mu_{k+14} = -mu_k; one equation for each k = 0, ..., 27
    A = zeros(Int, 28, 14)
    for k in 0:27, (coef, off) in ((a, 0), (b, 1), (1, 5))
        idx = mod(k + off, 28)
        sgn = idx < 14 ? 1 : -1
        A[k + 1, mod(idx, 14) + 1] = mod(A[k + 1, mod(idx, 14) + 1] + sgn * coef, 71)
    end
    check(rankmod(A, 71) == 14, "(a, b) = ($a, $b): the system in mu_0, ..., mu_13 has rank 14 over F_71")
end

println()
println("$(PASSED[]) checks passed, $(FAILED[]) failed")
exit(FAILED[] == 0 ? 0 : 1)
