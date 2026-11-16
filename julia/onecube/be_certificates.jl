# Exact checks for the line-field computation of Section 9 (Bakry–Émery test fields).
#
#   julia julia/onecube/be_certificates.jl
#
# All arithmetic is exact (Rational{BigInt} quaternions); nothing here uses floating point
# except the printed decimal value of each exact quotient.
#
# (a) The period-cell operator M = DᵀD on the 48 active links of the cell {0,1}⁴ with the
#     line field of Table A1 has the eigenvalue 9 + √17: for the integer vector u below,
#     a = Mu − 9u and b = u satisfy M a = 9a + 17b and M b = a + 9b, so M(a + √17 b) = (9 + √17)(a + √17 b).
#     The alternating vector w of the same table has Rayleigh quotient 304/24.
# (b) The exact Rayleigh quotients of the two test fields of Appendix A (files
#     certificates/be_cert_plus.txt and be_cert_minus.txt): R₊ ≥ 1397/100 and R₋ ≥ 1394/100,
#     and the ratios max|X_e|²/Σ|X_e|² of the two fields.
#
# None of these checks proves the continuum limit, the one-cube bound or the mass gap.

const SIGTAB = Dict("0000"=>0, "0001"=>1, "1000"=>0, "1001"=>2, "0100"=>2, "0101"=>1,
                    "1100"=>3, "1101"=>3, "0010"=>3, "0011"=>3, "1010"=>1, "1011"=>2,
                    "0110"=>2, "0111"=>0, "1110"=>1, "1111"=>0)   # Table A1 (directions 0..3)

sig(x) = SIGTAB[join(string.(mod.(x, 2)))]
# Cell {0,1}⁴ in lexicographic order (last coordinate fastest).
const CELL = [(a, b, c, d) for a in 0:1 for b in 0:1 for c in 0:1 for d in 0:1]
const LINKS = [(x, m) for x in CELL for m in 0:3]
const ACT = [(x, m) for (x, m) in LINKS if sig(x) != m]
nb(x, m) = ntuple(i -> i == m + 1 ? mod(x[i] + 1, 2) : x[i], 4)
plaquettes() = [(x, m, n) for x in CELL for m in 0:3 for n in m+1:3]

# ---- (a) the period-cell operator -------------------------------------------------------
function check_central()
    ix = Dict(l => i for (i, l) in enumerate(ACT)); nl = length(ACT)
    D = Vector{Vector{Int}}()
    for (x, m, k) in plaquettes()
        row = zeros(Int, nl)
        for (y, d, s) in ((x, m, 1), (nb(x, m), k, 1), (nb(x, k), m, -1), (x, k, -1))
            haskey(ix, (y, d)) && (row[ix[(y, d)]] += s)
        end
        push!(D, row)
    end
    Dm = reduce(vcat, permutedims.(D)); M = Dm' * Dm
    u = [0,0,0,0,0,0,1,0,0,0,-1,0,0,0,-1,-1,0,1,0,0,1,1,0,-1,1,0,-1,0,0,1,-1,0,1,0,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0]
    a = M * u - 9u; b = u
    eig = (M * a == 9a + 17b) && (M * b == a + 9b) && any(!=(0), b)
    c = [1, -1, 0, 0]
    w = [c[m+1] * (-1)^sum(x) for (x, m) in ACT]
    num = w' * M * w; den = w' * w
    return (nact = nl, eig = eig, num = num, den = den)
end

# ---- (b) the exact Rayleigh quotients ---------------------------------------------------
const Q4 = NTuple{4,Rational{BigInt}}
qmul(p::Q4, q::Q4) = (p[1]*q[1] - p[2]*q[2] - p[3]*q[3] - p[4]*q[4],
                      p[1]*q[2] + p[2]*q[1] + p[3]*q[4] - p[4]*q[3],
                      p[1]*q[3] - p[2]*q[4] + p[3]*q[1] + p[4]*q[2],
                      p[1]*q[4] + p[2]*q[3] - p[3]*q[2] + p[4]*q[1])
qcj(q::Q4) = (q[1], -q[2], -q[3], -q[4])
qadd(qs::Q4...) = ntuple(i -> sum(q[i] for q in qs), 4)
qsc(k, q::Q4) = ntuple(i -> k * q[i], 4)
rt(q::Q4) = 2 * q[1]                       # Re Tr of the SU(2) matrix of the quaternion q
const ONE = (big(1)//1, big(0)//1, big(0)//1, big(0)//1)
const ZERO = (big(0)//1, big(0)//1, big(0)//1, big(0)//1)

function rayleigh(certfile::AbstractString, sgn::Int)
    lines = filter(!isempty, strip.(readlines(certfile)))
    @assert length(lines) == length(ACT) == 48
    Q = Dict{Any,Q4}(l => ONE for l in LINKS); X = Dict{Any,Q4}()
    for (l, ln) in zip(ACT, lines)
        lhs, rhs = split(ln, '|'); f = split(lhs)
        r = [big(parse(Int, t)) // 100 for t in f[2:4]]; s = sum(r .^ 2)
        u = ((1 - s) / (1 + s), (2 .* r ./ (1 + s))...)   # inverse stereographic projection
        Q[l] = f[1] == "S" ? u : (-u[1], u[2], u[3], u[4])
        X[l] = (big(0)//1, (big(parse(Int, t))//1 for t in split(rhs))...)
    end
    @assert all(sum(q .^ 2) == 1 for q in values(Q))      # exact unit quaternions
    tot = big(0)//1
    for (x, m, n) in plaquettes()
        e = ((x, m), (nb(x, m), n), (nb(x, n), m), (x, n))
        @assert count(((y, d),) -> sig(y) == d, e) == 1     # one frozen link per plaquette
        Q1, Q2, Q3, Q4_ = (Q[k] for k in e)
        X1, X2, X3, X4 = (get(X, k, ZERO) for k in e)
        W = qmul(qmul(Q1, Q2), qmul(qcj(Q3), qcj(Q4_)))
        Y1, Y2, Y3, Y4 = X1, qmul(qmul(Q1, X2), qcj(Q1)), qmul(qmul(Q4_, X3), qcj(Q4_)), X4
        A = qadd(qmul(Y1, Y1), qsc(2, qmul(Y1, Y2)), qmul(Y2, Y2))
        B = qadd(qmul(Y3, Y3), qsc(2, qmul(Y3, Y4)), qmul(Y4, Y4))
        tot += rt(qmul(A, W)) + rt(qmul(W, B)) - 2 * rt(qmul(qmul(qadd(Y1, Y2), W), qadd(Y3, Y4)))
    end
    nrm = sum(2 * (q[2]^2 + q[3]^2 + q[4]^2) for q in values(X))
    mx = maximum(2 * (q[2]^2 + q[3]^2 + q[4]^2) for q in values(X))
    return (R = sgn * tot / nrm, ratio = mx / nrm)
end

function run_be_certificates()
    println("\n== Section 9: exact line-field checks (Rational{BigInt}) ==")
    c = check_central()
    println("BE-a  ", c.eig ? "PASS" : "FAIL", "  active links $(c.nact); M(a+√17 b) = (9+√17)(a+√17 b) exactly")
    println("BE-a  ", c.num // c.den == 304 // 24 ? "PASS" : "FAIL", "  alternating vector: quotient $(c.num) / $(c.den)")
    dir = joinpath(@__DIR__, "certificates")
    (Rp, ρp) = rayleigh(joinpath(dir, "be_cert_plus.txt"), 1)
    (Rm, ρm) = rayleigh(joinpath(dir, "be_cert_minus.txt"), -1)
    println("BE-b  ", Rp >= 1397 // 100 ? "PASS" : "FAIL", "  R₊ = ", round(Float64(Rp); digits = 12), " ≥ 1397/100 (exact comparison)")
    println("BE-b  ", Rm >= 1394 // 100 ? "PASS" : "FAIL", "  R₋ = ", round(Float64(Rm); digits = 12), " ≥ 1394/100 (exact comparison)")
    okρ = ρp == 525483 // 16378696 && ρm == 543521 // 16161106 && 1728ρp < 56 && 1728ρm < 59
    println("BE-b  ", okρ ? "PASS" : "FAIL", "  max|X_e|²/Σ|X_e|² = $(ρp), $(ρm); 1728× these < 56, < 59")
    return c.eig && c.num // c.den == 304 // 24 && Rp >= 1397 // 100 && Rm >= 1394 // 100 && okρ
end

if abspath(PROGRAM_FILE) == @__FILE__
    ok = run_be_certificates()
    exit(ok ? 0 : 1)
end
