# J13, J14: the two numerical rows of Section 9; J15: the adjoint Casimir behind the slope of Section 5; J16: Section 5 step-scaling and Z/2 constants.
#   J13  thm:finite-rank-obstruction(d): two-dimensional SU(2), Tr R^T - 1 at seven couplings.
#   J14  thm:no-convexity(d),(e): Taylor coefficients and majorant of G, and the constants of the proof.
# Exact rationals where no transcendental function occurs; otherwise the interval type of intervals.jl.

Base.asinh(a::Iv) = mono(asinh)(a)
Base.sinh(a::Iv) = mono(sinh)(a)
Base.cosh(a::Iv) = (a.lo >= 0 || error("cosh used on [0,∞) only"); mono(cosh)(a))

# ---------------------------------------------------------------------------------------
# J13. I_ν(x) = Σ_k (x/2)^{2k+ν}/(k!(k+ν)!), all terms positive. Enclosure: partial sum up to K
# (lower end), plus the tail bound t_{K+1}/(1-q), q = (x/2)^2/((K+2)(K+2+ν)) ≤ 1/2 (upper end).
function besselI_iv(ν::Int, x::Int)
    h2 = iv(big(x)^2 // 4)                       # (x/2)^2, exact
    t = iv(big(x) // 2)^ν
    for j in 1:ν; t = t / j; end                 # t_0 = (x/2)^ν/ν!
    s = t; k = 0
    while true
        tn = t * h2 / ((k + 1) * (k + 1 + ν))    # t_{k+1}
        q = (big(x)^2 // 4) // ((k + 2) * (k + 2 + ν))
        if q <= 1 // 2 && tn.hi < s.lo * big(2.0)^(-300)
            tail = tn * 2                        # Σ_{j>k} t_j ≤ t_{k+1}/(1-q) ≤ 2 t_{k+1}
            return Iv(s.lo, (s + tail).hi)
        end
        s = s + tn; t = tn; k += 1
    end
end

function J13()
    println("\n== J13: two-dimensional SU(2), Tr R^T - 1 = Σ_{n≥1} α_n^{LT}, α_n = I_{n+1}/I_1 ==")
    worst = big(0)
    for β in (2, 8, 32, 128, 512, 2048, 8192)
        Lc = ceil(Int, sqrt(big(46) * β / 10))
        @assert (Lc - 1)^2 < big(46) * β / 10 <= Lc^2      # L = ⌈√(4.6 β)⌉, checked exactly
        m = Lc * Lc
        ncut = 40
        I1 = besselI_iv(1, β)
        S = iv(0)
        for n in 1:ncut
            α = besselI_iv(n + 1, β) / I1
            S = S + α^m
        end
        # tail n > ncut: by (eq:2d-ratio) r_k = I_{k+1}/I_k < e^{-arsinh((k+1/2)/x)}, so α_n = Π_{k=1}^n r_k
        # ≤ exp(-Σ_{k=1}^n arsinh((k+1/2)/β)); each further factor is ≤ q = exp(-m arsinh((ncut+3/2)/β)).
        A = iv(0)
        for k in 1:ncut+1; A = A + asinh(iv(big(2k + 1) // (2β))); end
        first = exp(-(m * A))                                   # bound on α_{ncut+1}^m
        q = exp(-(m * asinh(iv(big(2ncut + 3) // (2β)))))
        tail = first / (1 - q)
        tot = S + tail
        worst = max(worst, tot.hi)
        claim("J13", "β = $β, L = T = $Lc: Tr R^T - 1 ≤ 9.4626e-4", tot, :le, d"0.00094626")
    end
    println("      largest upper end: ", Float64(worst))
end

# ---------------------------------------------------------------------------------------
# J14. Truncated power series with exact rational coefficients (order ≤ NS).
const NS = 14
struct PS; c::Vector{Rational{BigInt}}; end
PS(a::Rational) = PS([a; zeros(Rational{BigInt}, NS)])
psadd(a::PS, b::PS) = PS(a.c .+ b.c)
pssc(k, a::PS) = PS(k .* a.c)
function psmul(a::PS, b::PS)
    c = zeros(Rational{BigInt}, NS + 1)
    for i in 0:NS, j in 0:NS-i; c[i+j+1] += a.c[i+1] * b.c[j+1]; end
    PS(c)
end
Base.:+(a::PS, b::PS) = psadd(a, b); Base.:-(a::PS, b::PS) = psadd(a, pssc(-1, b))
Base.:*(a::PS, b::PS) = psmul(a, b); Base.:*(k::Union{Integer,Rational}, a::PS) = pssc(k, a)
# elementary series in φ: f(λφ) for the entire functions used, with sign switches for the majorant
function ser(f::Symbol, λ::Rational{BigInt})
    c = zeros(Rational{BigInt}, NS + 1)
    for n in 0:NS
        fn = big(1) // factorial(big(n))
        c[n+1] = λ^n * fn * (f == :exp ? 1 :
                 f == :cos ? (iseven(n) ? (-1)^(n ÷ 2) : 0) :
                 f == :sin ? (isodd(n) ? (-1)^((n - 1) ÷ 2) : 0) :
                 f == :cosh ? (iseven(n) ? 1 : 0) :
                 f == :sinh ? (isodd(n) ? 1 : 0) : error())
    end
    PS(c)
end
one_ps() = PS(big(1) // 1)

# G(φ) of the proof of thm:no-convexity(d)(ii); majorant: cos→cosh, sin→sinh, e^{-x}→e^{x}, all signs +.
function Gseries(maj::Bool)
    C(λ) = ser(maj ? :cosh : :cos, big(λ) // 1)
    S(λ) = ser(maj ? :sinh : :sin, big(λ) // 1)
    sg = maj ? 1 : -1
    E = ser(:exp, (maj ? 1 : -1) * big(1) // 2); e8 = ser(:exp, (maj ? 1 : -1) * big(1) // 8)
    o = one_ps()
    br1 = 4o + sg * 2 * E + sg * 2 * (E * C(2)) + sg * 2 * (e8 * S(2)) + sg * 2 * (e8 * E * S(1 // 2)) + 2 * (e8 * E * S(3 // 2))
    br2 = sg * (e8 * (o + E * C(1 // 2))) + e8 * (C(2) + sg * (E * C(3 // 2))) + sg * (E * S(2))
    C(1) * br1 + 2 * (S(1) * br2)
end

function J14()
    println("\n== J14: no convexity, thm:no-convexity(d)(ii),(iv),(e) ==")
    G = Gseries(false); M = Gseries(true)
    g = G.c
    stated = [0, -4, big(5) // 4, big(79) // 192, -big(673) // 1536, big(21473) // 245760, big(9643) // 393216]
    check("J14", "Taylor coefficients g_0..g_6 of G equal the stated rationals", all(g[1:7] .== stated),
          "g_0..g_12 = " * join(string.(g[1:13]), ", "))
    # majorant value at 1: evaluate the closed form with intervals
    Cm(λ) = cosh(iv(λ)); Sm(λ) = sinh(iv(λ)); Em = exp(iv(big(1) // 2)); ee8 = exp(iv(big(1) // 8))
    Mval = Cm(1) * (4 + 2Em + 2Em * Cm(2) + 2 * ee8 * Sm(2) + 2 * ee8 * Em * Sm(big(1) // 2) + 2 * ee8 * Em * Sm(big(3) // 2)) +
           2Sm(1) * (ee8 * (1 + Em * Cm(big(1) // 2)) + ee8 * (Cm(2) + Em * Cm(big(3) // 2)) + Em * Sm(2))
    claim("J14", "majorant at 1 ≤ 100.39", Mval, :le, d"100.39")
    check("J14", "majorant coefficients are ≥ |g_k| (k ≤ $NS)", all(M.c .>= abs.(g)))
    head = sum(M.c[1:13])                            # orders 0..12
    tail = Mval - head
    claim("J14", "majorant Taylor tail beyond order 12 at 1 ≤ 0.0038", tail, :le, d"0.0038")
    # G(φ)/φ ≤ g_1 + g_2 φ + Σ_{k=3}^{12} |g_k| φ^{k-1} + 0.0038 φ^{12}, increasing beyond g_1; evaluate at φ = 1/10
    φ = big(1) // 10
    P = g[2] + g[3] * φ + sum(abs(g[k+1]) * φ^(k - 1) for k in 3:12) + d"0.0038" * φ^12
    claimq("J14", "G(φ)/φ ≤ -3.870 on (0, 1/10] (bound at φ = 1/10)", P, :le, -d"3.870")
    check("J14", "g_2 = 5/4 > 0 (so the bound is increasing in φ)", g[3] > 0)
    claim("J14", "(2π - 0.2)^2/8 ≥ 4.61", (2 * PI - d"0.2")^2 / 8, :ge, d"4.61")
    claim("J14", "10 e^{-0.1} ≤ 21/2.0001 (ρ ≤ 21 φ e^{-46} at φ ≤ 1/10)", 10 * exp(iv(-d"0.1")), :le, big(21) // d"2.0001")
    claim("J14", "1/√(5π) ≤ 0.2524 (1/Z_φ at φ ≤ 1/10)", 1 / sqrt(5 * PI), :le, d"0.2524")
    claimq("J14", "34.4·0.2524 + 17.2·0.2524 + 17.2 ≤ 31", d"34.4" * d"0.2524" + d"17.2" * d"0.2524" + d"17.2", :le, big(31) // 1)
    claim("J14", "336 e^{-46} + 31 e^{-20} ≤ 6.5e-8", 336 * exp(iv(-46)) + 31 * exp(iv(-20)), :le, d"0.000000065")
    claimq("J14", "(3.870 - 6.5e-8)/2 ≥ 1.93499", (d"3.870" - d"0.000000065") / 2, :ge, d"1.93499")
    claim("J14", "1.93499/(1 + 2.1 e^{-46}) ≥ 1.89", d"1.93499" / (1 + d"2.1" * exp(iv(-46))), :ge, d"1.89")
    claim("J14", "4π/9 ≥ 1.396", 4 * PI / 9, :ge, d"1.396")
    claimq("J14", "1.396·15 ≥ 20 and 1.396·0.72 ≥ 1 (so 1.396 k_* ≥ 20 + log ℓ₁ℓ₂)", min(d"1.396" * 15 - 20, d"1.396" * d"0.72" - 1), :ge, big(0) // 1)
    claim("J14", "2π(16 + 0.72 log 1500)/1500 ≤ 1/10", 2 * PI * (16 + d"0.72" * log(iv(1500))) / 1500, :le, big(1) // 10)
    claim("J14", "(π/2)(16 + 0.72 log 4) < 26.71", PI / 2 * (16 + d"0.72" * log(iv(4))), :lt, d"26.71")
    claim("J14", "(π/2)·1.44 < 2.27", PI / 2 * d"1.44", :lt, d"2.27")
end

# ---------------------------------------------------------------------------------------
# J15. Adjoint Casimir of su(N) for <X,Y> = -(1/N) Re Tr XY, as in the OpenAI construction:
# C_A = -(1/dim) Σ_{a,b} g^{ab} tr(ad_a ad_b) in the rational basis E_jk-E_kj, i(E_jk+E_kj), i(E_jj-E_j+1,j+1).
# Exact arithmetic over Q(i). C_A = 2N^2 gives the slope 11 C_A/(24π^2) = 11N^2/(12π^2).
function sun_basis(N)
    B = Matrix{Complex{Rational{BigInt}}}[]
    E(j, k) = (M = zeros(Complex{Rational{BigInt}}, N, N); M[j, k] = 1; M)
    for j in 1:N, k in j+1:N
        push!(B, E(j, k) - E(k, j)); push!(B, im * (E(j, k) + E(k, j)))
    end
    for j in 1:N-1; push!(B, im * (E(j, j) - E(j + 1, j + 1))); end
    B
end
function sun_casimir(N)
    B = sun_basis(N); d = length(B)
    ipr(X, Y) = -real(sum(X[i, j] * Y[j, i] for i in 1:N, j in 1:N)) // N
    G = [ipr(B[a], B[b]) for a in 1:d, b in 1:d]
    Gi = inv(G)
    coord(Z) = Gi * [ipr(B[a], Z) for a in 1:d]
    closed = true
    ad = Vector{Matrix{Rational{BigInt}}}(undef, d)
    for a in 1:d
        cols = Vector{Vector{Rational{BigInt}}}()
        for b in 1:d
            C = B[a] * B[b] - B[b] * B[a]; c = coord(C)
            closed &= sum(c[i] * B[i] for i in 1:d) == C
            push!(cols, c)
        end
        ad[a] = hcat(cols...)
    end
    tr2(M) = sum(M[i, i] for i in 1:size(M, 1))
    closed, -sum(Gi[a, b] * tr2(ad[a] * ad[b]) for a in 1:d, b in 1:d) // d
end

function J15()
    println("\n== J15: adjoint Casimir C_A = 2N^2 for <X,Y> = -(1/N) Re Tr XY ==")
    for N in 2:5
        closed, c = sun_casimir(N)
        check("J15", "su($N): basis closed under brackets and C_A = $(2N^2)", closed && c == 2N^2, "C_A = $c")
    end
end

# ---------------------------------------------------------------------------------------
# J16. Section 5: the ℤ/2 lemma constants, the asymptotic-freedom slopes, the step-scaling choice
# of the odd integer q along a sweep of couplings, and strict positivity of the defect
# (two-dimensional SU(2) analogue of prop:psi-positive).
function J16()
    println("\n== J16: Section 5 constants (lem:z2-violation, prop:step-scaling, prop:psi-positive) ==")
    E = exp(iv(-8))
    q = 400 * E
    Γ = 48 * 3^4 * E * q^17 / (1 - q)
    claim("J16", "Lemma 5.7: Γ ≤ 2.3e-15 at β' = 4, T = 3", Γ, :le, 23 // 10^16)
    claim("J16", "Lemma 5.7: log 8 - log(1 + 7Γ) > 2.07", log(iv(8)) - log(1 + 7 * Γ), :gt, 207 // 100)
    claim("J16", "κ_AF(SU(2)) = 11/(3π²) > 0.37151", iv(11) / (3 * PI^2), :gt, 37151 // 100000)
    claim("J16", "κ_AF(SU(2)) = 11/(3π²) < 0.371531", iv(11) / (3 * PI^2), :lt, 371531 // 1000000)
    claim("J16", "κ_AF(SU(3)) = 33/(4π²) > 0.835899", iv(33) / (4 * PI^2), :gt, 835899 // 1000000)
    claim("J16", "κ_AF(SU(3)) = 33/(4π²) < 0.835945", iv(33) / (4 * PI^2), :lt, 835945 // 1000000)
    claimq("J16", "seed tolerance 1/2225664 < 1/4097", 1 // 2225664, :lt, 1 // 4097)
    # Step-scaling sweep: κ = 11/(3π²) (interval), β₁ = 1/10, δ = 1/10, β_N = 5, 6, ..., 60.
    κ = iv(11) / (3 * PI^2)
    β1 = iv(1 // 10); δ = 1 // 10
    ok = true; nsw = 0
    for βN in 5:60
        x = exp((iv(βN) - β1) / κ)
        x.lo * (1 - exp(-(iv(δ) / κ)).hi) >= 4 || continue
        qq = floor(BigInt, x.lo); iseven(qq) && (qq -= 1)
        floor(BigInt, x.hi) - floor(BigInt, x.lo) <= 0 || (ok = false; continue)  # q determined
        βp = iv(βN) - κ * log(iv(qq))
        ok &= qq >= 3 && βp.lo >= 1 // 10 && βp.hi <= 1 // 5 && 342 * qq <= 342 * x.lo
        nsw += 1
    end
    check("J16", "step scaling: q odd ≥ 3, β' ∈ [1/10, 1/5], T0 = 342q ≤ 342x for $nsw couplings β_N ∈ [5, 60]", ok && nsw > 40, "")
    # prop:psi-positive, two-dimensional SU(2): ψ = 2 log(1+a) - log(1+Σ r^{2T}) with r_n = α_n^L,
    # α_n = I_{n+1}/I_1, L = T = 3; check ψ ≥ log((1+a)²/(1+a²)) > 0.
    for β in (1, 2, 4, 8)
        I1 = besselI_iv(1, β)
        a = iv(0); b = iv(0)
        for n in 1:60
            r = (besselI_iv(n + 1, β) / I1)^3
            a = a + r^3; b = b + r^6
        end
        ψ = 2 * log(1 + a) - log(1 + b)
        lower = log((1 + a)^2 / (1 + a^2))
        claim("J16", "2D SU(2), β = $β, L = T = 3: ψ > 0 (truncated at n = 60)", ψ, :gt, 0 // 1)
        check("J16", "2D SU(2), β = $β: ψ ≥ log((1+a)²/(1+a²))", ψ.lo >= lower.hi * (1 - big(2.0)^-100), "")
    end
end

function J17()
    println("\n== J17: prop:flux-saturation-N and rem:step-general ==")
    # Σ_p p^{-3} ≤ Σ_{p ≤ P} p^{-3} + 1/(2P²), exact rationals, P = 2000.
    P = 2000
    isp(n) = n >= 2 && all(n % d != 0 for d in 2:isqrt(n))
    S = sum(big(1) // big(p)^3 for p in 2:P if isp(p)) + big(1) // (2 * big(P)^2)
    claim("J17", "log(1/Σ_p p^{-3}) > 1.744 (primes ≤ 2000, tail ≤ 1/(2·2000²))", -log(iv(S)), :gt, 1744 // 1000)
    # J₃(N) by direct count against N³ ∏_{p|N}(1 - p^{-3}), and the bound for N = 2..40.
    ok = true
    for N in 2:40
        J = count(k -> gcd(gcd(k[1], k[2]), gcd(k[3], N)) == 1, Iterators.product(0:N-1, 0:N-1, 0:N-1))
        f = big(N)^3 * prod((1 - big(1) // big(p)^3) for p in 2:N if isp(p) && N % p == 0)
        ok &= (J == f) && (-log(iv(1 - big(J) // big(N)^3))).lo > 1744 // 1000
        isp(N) && (ok &= J == N^3 - 1)
    end
    check("J17", "J₃(N) = N³∏(1-p⁻³), = N³-1 for prime N, and log(N³/(N³-J₃)) > 1.744 for N = 2..40", ok, "")
    claim("J17", "κ_AF(SU(2)) log 3 > 0.408", iv(11) / (3 * PI^2) * log(iv(3)), :gt, 408 // 1000)
    claimq("J17", "2/9 < 0.408", 2 // 9, :lt, 408 // 1000)
    # two-loop exponent b₁/(2b₀²) = 51/121, independent of N
    # thm:box-disorder(d): constants at q = 1 and the concavity constant
    claim("J17", "1 - e^{-9.0107} > 0.99987", 1 - exp(iv(-90107 // 10000)), :gt, 99987 // 100000)
    claimq("J17", "56/0.99987 < 56.01", 56 // 1 * 100000 // 99987, :lt, 5601 // 100)
    claimq("J17", "224/0.99987 < 224.03", 224 // 1 * 100000 // 99987, :lt, 22403 // 100)
    claim("J17", "1 - e^{-1} > 0.632", 1 - exp(iv(-1)), :gt, 632 // 1000)
    ok2 = all((big(34) * N^2 // 3 // 256) / (2 * (big(11) * N // 48)^2) == 51 // 121 for N in 2:10)
    check("J17", "two-loop exponent b₁/(2b₀²) = 51/121 for SU(N), N = 2..10 (π powers cancel)", ok2, "")
end


function J18()
    println("\n== J18: thm:two-number, cor:gap-sb, prop:no-vortex-comparison ==")
    # 8k³/(k-1) - 54 = 2(2k-3)²(k+3)/(k-1): the minimum 54 over k > 1 is attained at k = 3/2.
    ok = all(8 * k^3 // (k - 1) - 54 == 2 * (2k - 3)^2 * (k + 3) // (k - 1) for k in (big(1) .+ (1:400) .// 100))
    check("J18", "8k³/(k-1) - 54 = 2(2k-3)²(k+3)/(k-1) on k = 1.01..5 (so min_{k>1} 8k³/(k-1) = 54 at k = 3/2)", ok, "")
    claimq("J18", "8(3/2)³/(1/2) = 54", 8 * (3 // 2)^3 / (1 // 2), :le, 54 // 1)
    claim("J18", "(32/63)^{1/2}/64 < 0.011136", sqrt(iv(32 // 63)) / 64, :lt, 11136 // 1000000)
    claim("J18", "(81·0.011136 + 3 log 8194)/log(63/32) < 41.24",
          (iv(81 * 11136 // 1000000) + 3 * log(iv(8194))) / log(iv(63 // 32)), :lt, 4124 // 100)
    claim("J18", "2(e^{2^{-13}} - 1) < 1/4095", 2 * (exp(iv(1 // 8192)) - 1), :lt, 1 // 4095)
end

function J19()
    println("\n== J19: prop:abelian-vortex, thm:crossed-criteria, cor:sb-scale-invariant, rem:volume-bounds ==")
    # prop:abelian-vortex
    claim("J19", "2 arsinh(√3)/√3 ≥ 1.5206", 2 * asinh(sqrt(iv(3))) / sqrt(iv(3)), :ge, d"1.5206")
    θq = iv(1) + 2 * sum(exp(-iv(big(n)^2 // 4)) for n in 1:60) + 2 * exp(-iv(big(61)^2 // 4)) / (1 - exp(-iv(big(61) // 4)))
    claim("J19", "ϑ(1/4) = Σ_m e^{-m²/4} < 3.5450", θq, :lt, d"3.5450")
    claim("J19", "3 log(1 + 3e^{-π²}) < 3·10^{-3}", 3 * log(1 + 3 * exp(-PI^2)), :lt, d"0.003")
    c = iv(d"1.5206"); a = exp(-c / sqrt(iv(3)))
    claim("J19", "2/(1-e^{-c})·[((1+e^{-c/√3})/(1-e^{-c/√3}))³ - 1] < 33.84 at c = 1.5206",
          2 / (1 - exp(-c)) * (((1 + a) / (1 - a))^3 - 1), :lt, d"33.84")
    claimq("J19", "8.8·8·2 = 140.8", d"8.8" * 16, :le, d"140.8")
    claim("J19", "140.8·2·7.9·10^{-4} ≤ log(5/4)", iv(d"140.8" * 2 * d"0.00079"), :le, d"0.22314")
    claim("J19", "log(5/4) > 0.22314", log(iv(5 // 4)), :gt, d"0.22314")
    claim("J19", "(96/140.8) log(5/4) < 0.1522", (96 / iv(d"140.8")) * log(iv(5 // 4)), :lt, d"0.1522")
    claim("J19", "3 log 3.5450 + 33.84 + 0.003 + 0.1522 + log 2 < 38.49",
          3 * log(iv(d"3.5450")) + iv(d"33.84" + d"0.003" + d"0.1522") + log(iv(2)), :lt, d"38.49")
    claimq("J19", "1/4 + 38.49 < 39", 1 // 4 + d"38.49", :lt, big(39) // 1)
    # thm:crossed-criteria: the threshold eta_C satisfies 82 eta_C < 1 (|C| ≥ 1)
    claim("J19", "82/(e·8194³) < 1", 82 / (exp(iv(1)) * iv(big(8194)^3)), :lt, big(1) // 1)
    claimq("J19", "8(3/2)³ = 27", 8 * (3 // 2)^3, :le, big(27) // 1)
    claimq("J19", "(108 - 27)/3 = 27 (thm:crossed-criteria (ii))", big(108 - 27) // 3, :le, big(27) // 1)
    # cor:sb-scale-invariant: K x^{3/4} - x/2 ≤ 27K⁴/32, equality at x = (3K/2)⁴ (checked at K = 1 on a grid via x = y⁴)
    ok = all(27 // 32 - (y^3 - y^4 // 2) == (y - 3 // 2)^2 * (4y^2 + 4y + 3) // 8 for y in (big(0) .+ (0:400) .// 100))
    check("J19", "27/32 - (y³ - y⁴/2) = (y - 3/2)²(4y² + 4y + 3)/8 on y = 0..4 (max of Kx^{3/4} - x/2 is 27K⁴/32)", ok, "")
    # rem:volume-bounds: 27/216 = 1/8 and 27/(216·512) = 1/4096
    claimq("J19", "27/(216·512) = 1/4096", big(27) // (216 * 512), :le, big(1) // 4096)
    claimq("J19", "27/216 - 1/2 = -3/8", big(27) // 216 - 1 // 2, :le, -3 // 8)
end

function J20()
    println("\n== J20: cor:sharp-crossed, lem:neutral-bootstrap, prop:flux-nonmonotone ==")
    # cor:sharp-crossed: 3c_* ≥ 1/4160 - 1/(2·4160²) = 8319/34611200 and c_* > 1/12500
    claimq("J20", "1/4160 - 1/(2·4160²) ≥ 8319/34611200", big(1) // 4160 - big(1) // (2 * big(4160)^2), :ge, big(8319) // 34611200)
    claimq("J20", "8319·12500 > 3·34611200", big(8319) * 12500 // 1, :gt, 3 * big(34611200) // 1)
    claimq("J20", "1/12500 ≥ 8·10^{-5} (so c_* > 8·10^{-5})", big(1) // 12500, :ge, big(8) // 100000)
    check("J20", "3/49167 = 1/16389", big(3) // 49167 == big(1) // 16389, "")
    check("J20", "2/16388 = 1/8194", big(2) // 16388 == big(1) // 8194, "")
    claim("J20", "log(1 + 1/16388) ≤ 1/16388", log(1 + iv(big(1) // 16388)), :le, big(1) // 16388)
    # lem:neutral-bootstrap: 8(3/1)³ = 216, 8(3/2)³ = 27, and 2^{j+1} ≤ 3^j for j ≥ 2
    claimq("J20", "8·3³ = 216", 8 * big(3)^3 // 1, :le, big(216) // 1)
    check("J20", "2^{j+1} ≤ 3^j for 2 ≤ j ≤ 200", all(big(2)^(j + 1) <= big(3)^j for j in 2:200), "")
    # prop:flux-nonmonotone (β' = 10, q = 400 e^{-20})
    check("J20", "6³·3 = 648, 6·648 = 3888, 6·6 = 36, 2·6² - 1 = 71, 20·36 = 720",
          6^3 * 3 == 648 && 6 * 648 == 3888 && 6 * 6 == 36 && 2 * 36 - 1 == 71 && 20 * 36 == 720, "")
    lq = log(iv(400)) - 20
    claim("J20", "log q = log 400 - 20 < -14.0085", lq, :lt, d"-14.0085")
    q = exp(lq)
    claim("J20", "log(48·6⁴) - 20 + 71 log q - log(1-q) < -1003.5 (log ρ_6)",
          log(iv(48 * 6^4)) - 20 + 71 * lq - log(1 - q), :lt, d"-1003.5")
    claim("J20", "3888 e^{-20}/(1-q) < 10^{-5}", 3888 * exp(-iv(20)) / (1 - q), :lt, d"0.00001")
    claim("J20", "log 18 - 720 - 10^{-5} > -717.12 (log ρ_3)", log(iv(18)) - 720 - iv(d"0.00001"), :gt, d"-717.12")
end

function J21()
    println("\n== J21: thm:overlap-criteria, rem:overlap-obstructions ==")
    # L_0 = 81 log 2 + log 8194, with 81 = 27·3 (27 y(t_1) and y ≤ y^0 + 3 log 2)
    check("J21", "27·3 = 81 and 3·81 = 243", 27 * 3 == 81 && 3 * 81 == 243, "")
    L0 = 81 * log(iv(2)) + log(iv(8194))
    claim("J21", "L_0 = 81 log 2 + log 8194 > 65.156", L0, :gt, d"65.156")
    claim("J21", "L_0 = 81 log 2 + log 8194 < 65.1561", L0, :lt, d"65.1561")
    claim("J21", "3L_0 = log(2^243·8194³) > 195.468", log(iv(big(2)^243 * big(8194)^3)), :gt, d"195.468")
    claim("J21", "3L_0 = log(2^243·8194³) < 195.4683", 3 * L0, :lt, d"195.4683")
    # 2⌊Nα⌋ ≥ (1+ε)Nt - 2 ≥ ⌊Nt⌋ when Nεt ≥ 2 (checked on a grid of rationals)
    ok = all(2 * floor(Int, N * (1 + e) * t // 2) >= floor(Int, N * t)
             for N in 1:60, e in (big(1) // 10, big(1) // 3, big(1) // 2), t in (big(1) // 2, big(1), big(3) // 2, big(7) // 3) if N * e * t >= 2)
    check("J21", "2⌊N(1+ε)t/2⌋ ≥ ⌊Nt⌋ whenever Nεt ≥ 2 (grid)", ok, "")
end

function J22()
    println("\n== J22: prop:abelian-neutral, rem:free-gluon-neutral, cor:hypercube-vortex, rem:vortex-routes ==")
    # prop:abelian-neutral(a): 8.8·VT = 70.4 T⁴ on the cube (V = 8T³), and 70.4·3.169·10^{-3} ≤ 0.2231 < log(5/4)
    claimq("J22", "8.8·8 = 70.4", d"8.8" * 8, :le, d"70.4")
    claimq("J22", "70.4·3.169·10^{-3} ≤ 0.2231", d"70.4" * d"0.003169", :le, d"0.2231")
    claim("J22", "log(5/4) > 0.2231", log(iv(5 // 4)), :gt, d"0.2231")
    claim("J22", "e^{0.2231} - 1 < 1/4 (so ε < 1/4)", exp(iv(d"0.2231")) - 1, :lt, 1 // 4)
    # rem:free-gluon-neutral: c_0 = 12(N_c² - 1)e^{-π}
    claim("J22", "12e^{-π} > 0.5185", 12 * exp(-PI), :gt, d"0.5185")
    claim("J22", "36e^{-π} > 1.5557 (SU(2))", 36 * exp(-PI), :gt, d"1.5557")
    # cor:hypercube-vortex: (1/4)e^{-6L_0} = (2^488·8194^6)^{-1} ∈ (4.134, 4.135)·10^{-171}, 6L_0 + log 4 ∈ (392.3227, 392.3228)
    check("J22", "6·81 + 2 = 488", 6 * 81 + 2 == 488, "")
    thr = big(1) // (big(2)^488 * big(8194)^6)
    claimq("J22", "(2^488·8194^6)^{-1} > 4.134·10^{-171}", thr, :gt, big(4134) // big(10)^174)
    claimq("J22", "(2^488·8194^6)^{-1} < 4.135·10^{-171}", thr, :lt, big(4135) // big(10)^174)
    L0 = 81 * log(iv(2)) + log(iv(8194))
    claim("J22", "6L_0 + log 4 > 392.3227", 6 * L0 + log(iv(4)), :gt, d"392.3227")
    claim("J22", "6L_0 + log 4 < 392.3228", 6 * L0 + log(iv(4)), :lt, d"392.3228")
    # rem:vortex-routes(iii): b_0^MK = (1 - 1/4)/(24 log 2) = 1/(32 log 2), κ_MK = 8 b_0^MK = 1/(4 log 2), κ = 11/(3π²)
    check("J22", "(1 - 1/4)/24 = 1/32 and 8/32 = 1/4", (1 - 1 // 4) // 24 == 1 // 32 && 8 // 32 == 1 // 4, "")
    b0mk = 1 / (32 * log(iv(2)))
    claim("J22", "1/(32 log 2) > 0.045084", b0mk, :gt, d"0.045084")
    claim("J22", "1/(32 log 2) < 0.045085", b0mk, :lt, d"0.045085")
    b0 = iv(11) / (24 * PI^2)
    claim("J22", "11/(24π²) > 0.046438", b0, :gt, d"0.046438")
    claim("J22", "11/(24π²) < 0.046439", b0, :lt, d"0.046439")
    kmk = 1 / (4 * log(iv(2)))
    claim("J22", "1/(4 log 2) > 0.360673", kmk, :gt, d"0.360673")
    claim("J22", "1/(4 log 2) < 0.360674", kmk, :lt, d"0.360674")
    ka = iv(11) / (3 * PI^2)
    claim("J22", "11/(3π²) > 0.371511", ka, :gt, d"0.371511")
    claim("J22", "11/(3π²) < 0.371512", ka, :lt, d"0.371512")
    ex = 2 - 2 * ka / kmk
    claim("J22", "2 - 2κ/κ_MK = 2 - 88 log 2/(3π²) > -0.060095", ex, :gt, d"-0.060095")
    claim("J22", "2 - 2κ/κ_MK = 2 - 88 log 2/(3π²) < -0.060094", ex, :lt, d"-0.060094")
end
