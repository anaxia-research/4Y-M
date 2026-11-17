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
