# Minimal interval arithmetic on BigFloat with directed rounding (MPFR).
# Every elementary function used here (exp, expm1, log, log1p, sqrt, π) is
# correctly rounded by MPFR, so evaluating the lower endpoint with RoundDown and
# the upper endpoint with RoundUp gives a rigorous enclosure.

setprecision(BigFloat, 256)

struct Iv
    lo::BigFloat
    hi::BigFloat
    function Iv(lo::BigFloat, hi::BigFloat)
        lo <= hi || error("empty interval")
        new(lo, hi)
    end
end

dn(f) = setrounding(f, BigFloat, RoundDown)
up(f) = setrounding(f, BigFloat, RoundUp)

Iv(x::Integer) = Iv(dn(() -> BigFloat(x)), up(() -> BigFloat(x)))
# Enclose both integers before dividing. Rounding numerator and denominator in
# the same direction does not enclose their quotient when either integer needs
# rounding (for example, (2^300 + 1)//(2^300 + 2) at 256-bit precision).
Iv(x::Rational) = Iv(numerator(x)) / Iv(denominator(x))
Iv(x::Iv) = x
const Num = Union{Integer,Rational,Iv}
iv(x) = Iv(x)

Base.:+(a::Iv, b::Iv) = Iv(dn(() -> a.lo + b.lo), up(() -> a.hi + b.hi))
Base.:-(a::Iv, b::Iv) = Iv(dn(() -> a.lo - b.hi), up(() -> a.hi - b.lo))
Base.:-(a::Iv) = Iv(-a.hi, -a.lo)
function Base.:*(a::Iv, b::Iv)
    ps_dn = dn(() -> [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi])
    ps_up = up(() -> [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi])
    Iv(minimum(ps_dn), maximum(ps_up))
end
function Base.inv(a::Iv)
    (a.lo > 0 || a.hi < 0) || error("division by interval containing 0")
    Iv(dn(() -> 1 / a.hi), up(() -> 1 / a.lo))
end
Base.:/(a::Iv, b::Iv) = a * inv(b)
for op in (:+, :-, :*, :/)
    @eval Base.$op(a::Iv, b::Union{Integer,Rational}) = $op(a, Iv(b))
    @eval Base.$op(a::Union{Integer,Rational}, b::Iv) = $op(Iv(a), b)
end
function Base.:^(a::Iv, n::Integer)
    n >= 0 || return inv(a^(-n))
    n == 0 && return Iv(1)
    if a.lo >= 0
        Iv(dn(() -> a.lo^n), up(() -> a.hi^n))
    else
        r = Iv(1); for _ in 1:n; r = r * a; end; r
    end
end
# monotone increasing functions
mono(f) = a -> Iv(dn(() -> f(a.lo)), up(() -> f(a.hi)))
Base.exp(a::Iv) = mono(exp)(a)
Base.expm1(a::Iv) = mono(expm1)(a)
Base.log(a::Iv) = (a.lo > 0 || error("log of nonpositive"); mono(log)(a))
Base.log1p(a::Iv) = mono(log1p)(a)
Base.sqrt(a::Iv) = (a.lo >= 0 || error("sqrt of negative"); mono(sqrt)(a))
Base.atanh(a::Iv) = mono(atanh)(a)
Base.tanh(a::Iv) = mono(tanh)(a)
Base.asinh(a::Iv) = mono(asinh)(a)
const PI = Iv(dn(() -> BigFloat(π)), up(() -> BigFloat(π)))
Base.max(a::Iv, b::Iv) = Iv(max(a.lo, b.lo), max(a.hi, b.hi))
Base.min(a::Iv, b::Iv) = Iv(min(a.lo, b.lo), min(a.hi, b.hi))
mid(a::Iv) = (a.lo + a.hi) / 2
Base.show(io::IO, a::Iv) = print(io, "[", round(Float64(a.lo), sigdigits=17), ", ", round(Float64(a.hi), sigdigits=17), "]")

# Decimal rationals: d"0.0223" is the exact rational 223/10000.
function decrat(s::AbstractString)
    s = strip(s)
    m = match(r"^([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$", s)
    m === nothing && error("bad decimal $s")
    sgn = m[1] == "-" ? -1 : 1
    ip = m[2] == "" ? "0" : m[2]
    fp = m[3] === nothing ? "" : m[3]
    ex = m[4] === nothing ? 0 : parse(Int, m[4])
    num = parse(BigInt, ip * fp) * sgn
    e = ex - length(fp)
    e >= 0 ? (num * big(10)^e) // 1 : num // big(10)^(-e)
end
macro d_str(s) decrat(s) end

# Outward rounding of an endpoint to a short decimal rational.
function short_up(x::BigFloat, ndig::Int)
    x == 0 && return 0 // 1
    e = floor(Int, log10(abs(Float64(x)))) - ndig + 1
    sc = big(10)^abs(e)
    q = Rational(x)
    e >= 0 ? (cld(numerator(q), denominator(q) * sc) * sc) // 1 :
             cld(numerator(q) * sc, denominator(q)) // sc
end
function short_dn(x::BigFloat, ndig::Int)
    x == 0 && return 0 // 1
    e = floor(Int, log10(abs(Float64(x)))) - ndig + 1
    sc = big(10)^abs(e)
    q = Rational(x)
    e >= 0 ? (fld(numerator(q), denominator(q) * sc) * sc) // 1 :
             fld(numerator(q) * sc, denominator(q)) // sc
end
