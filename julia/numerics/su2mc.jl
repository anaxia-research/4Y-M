# SU(2) Wilson lattice gauge theory on L^3 x Lt: heatbath + overrelaxation,
# glueball (spatial loops) and torelon (spatial Polyakov loop) time-slice sums at several APE smearing levels.
# Usage: julia -t 4 su2mc.jl beta L Lt ntherm nmeas nskip seed outfile
using Random, Printf, Base.Threads

const Q = NTuple{4,Float64}   # (a0,a1,a2,a3) <-> a0 + i a.sigma
@inline qmul(a::Q,b::Q)::Q = (a[1]*b[1]-a[2]*b[2]-a[3]*b[3]-a[4]*b[4],
    a[1]*b[2]+b[1]*a[2]-(a[3]*b[4]-a[4]*b[3]),
    a[1]*b[3]+b[1]*a[3]-(a[4]*b[2]-a[2]*b[4]),
    a[1]*b[4]+b[1]*a[4]-(a[2]*b[3]-a[3]*b[2]))
@inline qdag(a::Q)::Q = (a[1],-a[2],-a[3],-a[4])
@inline qadd(a::Q,b::Q)::Q = (a[1]+b[1],a[2]+b[2],a[3]+b[3],a[4]+b[4])
@inline qscale(s,a::Q)::Q = (s*a[1],s*a[2],s*a[3],s*a[4])
@inline qnorm(a::Q) = sqrt(a[1]^2+a[2]^2+a[3]^2+a[4]^2)

struct Lat
    L::Int; Lt::Int; V::Int
    up::Matrix{Int}; dn::Matrix{Int}; par::Vector{Int}; tslice::Vector{Int}
end
function Lat(L,Lt)
    V=L^3*Lt; up=zeros(Int,4,V); dn=zeros(Int,4,V); par=zeros(Int,V); ts=zeros(Int,V)
    dims=(L,L,L,Lt)
    idx(c)=1+c[1]+L*(c[2]+L*(c[3]+L*c[4]))
    for t in 0:Lt-1, z in 0:L-1, y in 0:L-1, x in 0:L-1
        c=[x,y,z,t]; i=idx(c); par[i]=(x+y+z+t)%2; ts[i]=t
        for mu in 1:4
            cp=copy(c); cp[mu]=mod(cp[mu]+1,dims[mu]); up[mu,i]=idx(cp)
            cm=copy(c); cm[mu]=mod(cm[mu]-1,dims[mu]); dn[mu,i]=idx(cm)
        end
    end
    Lat(L,Lt,V,up,dn,par,ts)
end

# A with Re Tr(U_mu(x) A) = sum of the plaquettes containing U_mu(x) (directions in dirs)
function staple(U::Array{Q,2},lat::Lat,mu,i,dirs)
    A::Q=(0.0,0.0,0.0,0.0)
    ip=lat.up[mu,i]
    for nu in dirs
        nu==mu && continue
        inu=lat.up[nu,i]
        A=qadd(A,qmul(qmul(U[nu,ip],qdag(U[mu,inu])),qdag(U[nu,i])))
        imnu=lat.dn[nu,i]; ipmnu=lat.dn[nu,ip]
        A=qadd(A,qmul(qmul(qdag(U[nu,ipmnu]),qdag(U[mu,imnu])),U[nu,imnu]))
    end
    A
end

function randsu2(rng)
    while true
        a=(2rand(rng)-1,2rand(rng)-1,2rand(rng)-1,2rand(rng)-1); n=qnorm(a)
        (n<1 && n>1e-6) && return qscale(1/n,a)
    end
end

# x in SU(2) with density ~ exp(alpha x0) dHaar  (Kennedy-Pendleton)
function heatbath_x(rng,alpha)
    while true
        r1=1-rand(rng); r2=rand(rng); r3=1-rand(rng); r4=rand(rng)
        d=-(log(r1)+cos(2pi*r2)^2*log(r3))/alpha
        if r4^2 <= 1-d/2
            x0=1-d; r=sqrt(max(0.0,1-x0^2))
            ct=2rand(rng)-1; st=sqrt(1-ct^2); ph=2pi*rand(rng)
            return (x0, r*st*cos(ph), r*st*sin(ph), r*ct)
        end
    end
end

# action S = beta sum_p (1 - Tr U_p / 2): local weight exp(beta/2 Re Tr(U A)) = exp(beta k x0), X = U W
function sweep!(U,lat,beta,rngs,kind)
    for mu in 1:4, p in 0:1
        @threads :static for tid in 1:nthreads()
            rng=rngs[tid]
            for i in tid:nthreads():lat.V
                lat.par[i]==p || continue
                A=staple(U,lat,mu,i,1:4); k=qnorm(A); W=qscale(1/k,A)
                if kind==:hb
                    U[mu,i]=qmul(heatbath_x(rng,beta*k),qdag(W))
                else
                    U[mu,i]=qmul(qmul(qdag(W),qdag(U[mu,i])),qdag(W))
                end
            end
        end
    end
    @threads for i in 1:lat.V
        for mu in 1:4; U[mu,i]=qscale(1/qnorm(U[mu,i]),U[mu,i]); end
    end
end

function plaq(U,lat)
    s=zeros(nthreads())
    @threads :static for tid in 1:nthreads()
        acc=0.0
        for i in tid:nthreads():lat.V, mu in 1:3, nu in mu+1:4
            acc+=qmul(qmul(U[mu,i],U[nu,lat.up[mu,i]]),qmul(qdag(U[mu,lat.up[nu,i]]),qdag(U[nu,i])))[1]
        end
        s[tid]=acc
    end
    sum(s)/(6lat.V)
end

# APE smearing of spatial links within time slices; the sum of 3-link paths parallel to U is A^dagger
function ape(U,lat,alpha,n)
    S=copy(U); T=similar(U)
    for it in 1:n
        @threads for i in 1:lat.V
            for k in 1:3
                A=staple(S,lat,k,i,1:3)
                v=qadd(qscale(1-alpha,S[k,i]),qscale(alpha/4,qdag(A)))
                T[k,i]=qscale(1/qnorm(v),v)
            end
            T[4,i]=S[4,i]
        end
        S,T=T,S
    end
    S
end

# per time slice: (half-)traces of spatial plaquettes per plane, 1x2 rectangles per plane,
# zero-momentum spatial Polyakov loops (full trace) per direction
function loops_per_slice(S,lat)
    Lt=lat.Lt; L=lat.L
    P=zeros(3,Lt); R=zeros(3,Lt); Pol=zeros(3,Lt)
    planes=((1,2),(2,3),(3,1))
    for i in 1:lat.V
        t=lat.tslice[i]+1
        for (pl,(a,b)) in enumerate(planes)
            ia=lat.up[a,i]; ib=lat.up[b,i]
            P[pl,t]+=qmul(qmul(S[a,i],S[b,ia]),qmul(qdag(S[a,ib]),qdag(S[b,i])))[1]
            iaa=lat.up[a,ia]; iab=lat.up[b,ia]; ibb=lat.up[b,ib]
            r1=qmul(qmul(qmul(S[a,i],S[a,ia]),S[b,iaa]),qmul(qmul(qdag(S[a,iab]),qdag(S[a,ib])),qdag(S[b,i])))
            r2=qmul(qmul(qmul(S[a,i],S[b,ia]),S[b,iab]),qmul(qmul(qdag(S[a,ibb]),qdag(S[b,ib])),qdag(S[b,i])))
            R[pl,t]+=r1[1]+r2[1]
        end
    end
    for i in 1:lat.V, d in 1:3
        c = d==1 ? (i-1)%L : d==2 ? ((i-1)÷L)%L : ((i-1)÷L^2)%L
        c==0 || continue
        q::Q=(1.0,0.0,0.0,0.0); j=i
        for s in 1:L; q=qmul(q,S[d,j]); j=lat.up[d,j]; end
        Pol[d,lat.tslice[i]+1]+=2q[1]
    end
    P,R,Pol
end

function main()
    beta=parse(Float64,ARGS[1]); L=parse(Int,ARGS[2]); Lt=parse(Int,ARGS[3])
    ntherm=parse(Int,ARGS[4]); nmeas=parse(Int,ARGS[5]); nskip=parse(Int,ARGS[6])
    seed=parse(Int,ARGS[7]); out=ARGS[8]
    lat=Lat(L,Lt)
    rngs=[Xoshiro(seed+1000t) for t in 1:nthreads()]
    U=Array{Q,2}(undef,4,lat.V)
    for i in 1:lat.V, mu in 1:4; U[mu,i]=randsu2(rngs[1]); end
    upd()=(sweep!(U,lat,beta,rngs,:hb); for k in 1:3; sweep!(U,lat,beta,rngs,:or); end)
    t0=time()
    for n in 1:ntherm; upd(); end
    @printf(stderr,"therm done %.1fs plaq=%.6f\n",time()-t0,plaq(U,lat))
    smears=(0,5,12,25)   # APE alpha=0.5 cumulative levels
    open(out,"a") do f
        println(f,"# beta=$beta L=$L Lt=$Lt seed=$seed smears=$(smears) alpha=0.5 cols: plaq | per level: P(3,Lt) R(3,Lt) Pol(3,Lt) column-major")
        for m in 1:nmeas
            for k in 1:nskip; upd(); end
            row=[plaq(U,lat)]
            S=U; prev=0
            for ns in smears
                S = ns==prev ? S : ape(S,lat,0.5,ns-prev); prev=ns
                P,R,Pol=loops_per_slice(S,lat)
                append!(row,vec(P)); append!(row,vec(R)); append!(row,vec(Pol))
            end
            println(f,join((@sprintf("%.10e",x) for x in row)," "))
            m%20==0 && (flush(f); @printf(stderr,"meas %d %.1fs\n",m,time()-t0))
        end
    end
end
main()
