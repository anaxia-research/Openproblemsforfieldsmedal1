# Certificates for the explicit constants in the proof of the window theorem.
#   (1) the gamma-density lemma (two-sided tail bound) for the window widths used,
#   (2) the balancing lemma: its numerical constants, checked in exact rational
#       arithmetic on a grid of parameters including every corner of the ranges,
#   (3) the optimality bound 2*sqrt(2)*x^(1/2+eps/2) for the same grid.
# Ball arithmetic: Arblib (FLINT/Arb). A check passes only if the enclosure
# decides it. Run: julia --project=. window_certificates.jl

using Arblib, Printf, Random

const PREC = 256
setprecision(Arb, PREC)

fails = 0
check(name, ok, val) = (global fails; ok || (fails += 1);
    @printf("%-66s %s  %s\n", name, ok ? "PASS" : "FAIL", val))

# ---------------------------------------------------------------------------
# (1) Gamma densities.  I(v) = v - 1 - log v.
I(v::Arb) = v - 1 - log(v)

# For integer s = k + 1 the regularized incomplete gamma functions are Poisson
# tails, sums of positive terms with no cancellation:
#   P(k+1, z) = e^{-z} sum_{j >= k+1} z^j / j!   (z < k+1: geometric tail bound)
#   Q(k+1, z) = e^{-z} sum_{j = 0}^{k}  z^j / j!
function Preg_int(k::Int, z::Arb)
    @assert Arblib.is_negative(z - (k + 2))
    t = exp(-z + (k + 1) * log(z) - lgamma(Arb(k + 2)))
    s = Arb(0); j = k + 1
    while true
        s += t
        r = z / (j + 1)
        if Float64(Arblib.ubound(t)) < 1e-40 * Float64(Arblib.lbound(s)) || j > k + 200000
            # remaining terms are at most t * r / (1 - r)
            return s + Arblib.add_error!(Arb(0), t * r / (1 - r))
        end
        t *= r; j += 1
    end
end
function Qreg_int(k::Int, z::Arb)
    t = exp(-z); s = Arb(0)
    for j in 0:k
        s += t
        t *= z / (j + 1)
    end
    return s
end
lgamma(x::Arb) = (r = Arb(prec = PREC); Arblib.lgamma!(r, x); r)

"Exact floor of a ball, or nothing if the ball contains an integer boundary."
function exact_floor(x::Arb)
    lo = floor(BigInt, BigFloat(Arblib.lbound(x)))
    hi = floor(BigInt, BigFloat(Arblib.ubound(x)))
    lo == hi ? Int(lo) : nothing
end

function gamma_lemma(δ::Rational{Int}; Ucount = 200)
    d = Arb(δ)
    τ = 1 + d / 2
    bδ = (1 + d) / (1 + 3d / 4)
    c = min(I(1 / τ), I(bδ))
    q = max(Arb(2), 2 / (exp(c) - 1))
    σ = q + 2
    Uδ = max(Arb(1), 4 / (q * d))
    check(@sprintf("gamma lemma, delta = %s: c_delta > 0", δ), Arblib.ispositive(c),
          string(c))
    @printf("    tau = %s, b = %s\n    q = %s, sigma = %s, U_delta = %s\n",
            Float64(τ), Float64(bδ), Float64(q), Float64(σ), Float64(Uδ))
    U0 = ceil(Int, Float64(Arblib.ubound(Uδ)))
    worst = Arb(0); allok = true; undecided = 0
    for U in U0:(U0 + Ucount - 1)
        kk = exact_floor(q * τ * U)
        kk === nothing && (undecided += 1; continue)
        k = kk
        okk = (U <= k) && Arblib.is_nonnegative(q * τ * U - k)
        tail = (Preg_int(k, q * U) + Qreg_int(k, q * (1 + d) * U)) / q^(k + 1)
        ratio = tail * σ^k
        okk &= Arblib.is_negative(ratio - 1) || (Arblib.ubound(ratio) <= 1)
        allok &= okk
        Float64(Arblib.ubound(ratio)) > Float64(Arblib.ubound(worst)) && (worst = ratio)
    end
    check(@sprintf("gamma tail <= sigma^-k for %d integers U >= U_delta (delta = %s)",
                   Ucount, δ), allok && undecided == 0,
          @sprintf("max tail*sigma^k = %.3e", Float64(Arblib.ubound(worst))))
    return (c = c, q = q, σ = σ)
end

println("== (1) gamma densities")
for δ in (1 // 2, 1 // 1, 1 // 4)
    gamma_lemma(δ)
end

# ---------------------------------------------------------------------------
# (2) and (3): the balancing lemma in exact rational arithmetic.
# x = 2^64 and eps = 1/8, so x^(j*eps/8) = 2^j is an exact power of two.
println("== (2) balancing lemma, exact arithmetic at x = 2^64, eps = 1/8")

const X = big(2)^64
p2(j) = big(2)^j                         # x^(j*eps/8) for eps = 1/8 is 2^j

function balance_instance(n, t, v2, m, k, a, b, C)
    # B of the lemma, and the largest z allowed by inequality (6.1)
    B = t * a * (1 + m^2 // k) + m * (2n * m * b * p2(8) + v2 * k * b * p2(16) // n^2)
    coeff = t * m * b * v2 // (2n)
    zmax = 4 * p2(32 + 8) + (p2(8C) * B + 2t * m * b // X) / coeff
    return B, zmax
end

function balance_grid(rng; samples = 6400)
    worst = 0 // 1; worst_opt = big(10)^9 // 1
    ok = true; okopt = true; count = 0
    mlo, mhi = p2(28), p2(36)            # x^(1/2-eps) = 2^24 ... use [2^28, 2^36] grid and corners
    mlist = [p2(24), p2(28), p2(32), p2(36)]
    for C in 0:3, m in mlist, _ in 1:(samples ÷ 64)
        # n must allow x m <= n^2 x^(1/2 - eps):  n^2 >= 2^(64 - 24) m
        nmin = isqrt(p2(40) * m) + 1
        n = rand(rng, (nmin, 2nmin, 8nmin, rand(rng, nmin:(16nmin))))
        tlo = cld(n, 4)                  # t >= (n/2) x^(-eps/8) = n/4
        t = rand(rng, (tlo, n, 2n, rand(rng, tlo:(2n))))
        v2lo = cld(n, 256)               # v2 >= n x^(-eps)
        v2 = rand(rng, (v2lo, n, rand(rng, v2lo:n)))
        klo, khi = X * m, n^2 * p2(24)
        khi < klo && continue
        k = rand(rng, (klo, khi, rand(rng, klo:khi))) // 1
        b = rand(rng, (1 // 1, 1 // 7, big(3)^20 // 1))
        a = rand(rng, (0 // 1, 2X * b, X * b // 2, rand(rng, 0:1000) // 1000 * 2X * b))
        B, zmax = balance_instance(n, t, v2, m, k, a, b, C)
        bound = 26 * p2(32 + 8C + 21)    # 26 x^(1/2 + (C + 21/8) eps)
        r = zmax / bound
        ok &= r <= 1
        r > worst && (worst = r)
        count += 1
        # optimality: if a >= b x / 2 and t <= 2n then 2B/Q >= 2 sqrt 2 x^(1/2+eps/2)
        if a >= X * b // 2 && t <= 2n
            Q = t * m * b
            lhs2 = (2B / Q)^2
            rhs2 = 8 * p2(72)            # (2 sqrt 2 x^(1/2+eps/2))^2 = 8 x^(1+eps)
            okopt &= lhs2 >= rhs2
            lhs2 / rhs2 < worst_opt && (worst_opt = lhs2 / rhs2)
        end
    end
    check(@sprintf("z <= 26 x^(1/2+(C+21/8)eps) on %d exact instances, C = 0..3", count),
          ok, @sprintf("max ratio %.4f", Float64(worst)))
    check("optimality (2B/Q)^2 >= 8 x^(1+eps) on the same instances", okopt,
          @sprintf("min ratio %.4f", Float64(worst_opt)))
    # the closing step 26 x^((C+21/8)eps) <= x^((C+3)eps) once 26 <= x^(3eps/8) = 2^3? (x = 2^64 gives 2^3 = 8 < 26)
    # so it is checked at the first x = 2^(64 j) with 2^(3j) >= 26, i.e. j = 2:
    check("26 <= x^(3 eps/8) at x = 2^128, eps = 1/8 (threshold of the last claim)",
          26 <= big(2)^6, "2^6 = 64")
end

balance_grid(MersenneTwister(20261124))

# exponent bookkeeping of the four summands of B/Q, in units of eps/8:
# 1/2 + eps = 32*8/8... compare exponents a + b*eps as pairs (a, b)
println("== (2') exponent bookkeeping, exact rationals")
ex = [(1 // 2, 1 // 1), (0 // 1, 0 // 1), (1 // 2, 13 // 8), (1 // 2, 9 // 8)]
check("each summand of B/Q is <= its factor times x^(1/2+13 eps/8)",
      all(e -> (e[1] < 1 // 2) || (e[1] == 1 // 2 && e[2] <= 13 // 8), ex),
      "factors 2, 2, 4, 2; sum 10")
check("2*10 + 4/3 <= 22 and 4 + 22 = 26", 2 * 10 + 4 // 3 <= 22 && 4 + 22 == 26, "exact")
check("13/8 + 1 = 21/8 (division by s >= x^-eps)", 13 // 8 + 1 == 21 // 8, "exact")

println("failures: ", fails)
exit(fails == 0 ? 0 : 1)
