# Analysis of su2mc.jl output: glueball (A1++, E++) and torelon energies by GEVP with jackknife errors,
# then the spectral (free-boson Fock) estimate of log Zcal_{L^3}(T0) at T0 = L/2, to compare with 1/8192.
# Usage: julia analyse.jl data/b2.3_L16_T16.dat [nbin]
using LinearAlgebra, Printf, Statistics

function load(f)
    hdr=""; rows=Vector{Vector{Float64}}()
    for ln in eachline(f)
        if startswith(ln,"#"); hdr=ln; continue; end
        push!(rows,parse.(Float64,split(ln)))
    end
    L=parse(Int,match(r"L=(\d+)",hdr)[1]); Lt=parse(Int,match(r"Lt=(\d+)",hdr)[1])
    beta=parse(Float64,match(r"beta=([\d.]+)",hdr)[1])
    nlev=length(eval(Meta.parse(match(r"smears=(\([^)]*\))",hdr)[1])))
    beta,L,Lt,nlev,reduce(hcat,rows)'   # nmeas x ncol
end

# operators: returns Dict channel => array (nmeas, nops, Lt)
function operators(X,L,Lt,nlev)
    nm=size(X,1); blk=9Lt
    A1=zeros(nm,2nlev,Lt); E=zeros(nm,2nlev,Lt,2); T=zeros(nm,nlev,Lt,3)
    for m in 1:nm, l in 1:nlev
        base=1+(l-1)*blk
        P=reshape(X[m,base+1:base+3Lt],3,Lt); R=reshape(X[m,base+3Lt+1:base+6Lt],3,Lt); Po=reshape(X[m,base+6Lt+1:base+9Lt],3,Lt)
        for t in 1:Lt
            A1[m,2l-1,t]=sum(P[:,t]); A1[m,2l,t]=sum(R[:,t])
            E[m,2l-1,t,1]=P[1,t]-P[2,t]; E[m,2l-1,t,2]=(P[1,t]+P[2,t]-2P[3,t])/sqrt(3)
            E[m,2l,t,1]=R[1,t]-R[2,t];   E[m,2l,t,2]=(R[1,t]+R[2,t]-2R[3,t])/sqrt(3)
            for d in 1:3; T[m,l,t,d]=Po[d,t]; end
        end
    end
    A1,E,T
end

# correlation matrix C[i,j,dt] averaged over source slices and components, from measurement subset idx
function corr(O,idx,subtract)
    nops=size(O,2); Lt=size(O,3); ncomp=size(O,4)
    C=zeros(nops,nops,Lt)
    for c in 1:ncomp
        Oc=O[idx,:,:,c]
        mu = subtract ? dropdims(mean(Oc,dims=(1,3)),dims=(1,3)) : zeros(nops)
        for m in axes(Oc,1), t0 in 1:Lt, dt in 0:Lt-1
            t1=mod(t0-1+dt,Lt)+1
            for i in 1:nops, j in 1:nops
                C[i,j,dt+1]+=(Oc[m,i,t1]-mu[i])*(Oc[m,j,t0]-mu[j])
            end
        end
    end
    C./(length(idx)*Lt*ncomp)
end

# lowest GEVP effective energies E(t) = log(lambda(t)/lambda(t+1)), t0 = 0 (normalisation slice), t = 1..tmax
function gevp_meff(C,tmax)
    C0=Symmetric((C[:,:,1]+C[:,:,1]')/2)
    F=eigen(C0); keep=F.values .> 1e-12*maximum(F.values)
    B=F.vectors[:,keep]*Diagonal(1 ./ sqrt.(F.values[keep]))
    lam(t)=maximum(eigvals(Symmetric(B'*((C[:,:,t+1]+C[:,:,t+1]')/2)*B)))
    [log(lam(t)/lam(t+1)) for t in 0:tmax-1]
end

function jack(f,nm,nbin)
    bs=nm÷nbin; full=f(1:nbin*bs)
    js=[f(setdiff(1:nbin*bs,(b-1)*bs+1:b*bs)) for b in 1:nbin]
    jm=mean(js); err=sqrt.((nbin-1)/nbin*sum((j.-jm).^2 for j in js))
    full,err,js
end

# lattice dispersion sinh^2(E/2) = sinh^2(m/2) + sum sin^2(p/2): never above continuum, so the sum below is not underestimated
latE(m,p)=2asinh(sqrt(sinh(m/2)^2+sum(sin.(p./2).^2)))

# log Zcal estimate: free-boson Fock space over single-particle levels
#  0++ (mult 1), 2++ (mult 5, E++ mass), torelons: 3 single-winding sectors with transverse momenta (2 dims),
#  3 double-winding (energy sqrt2 E_T), 1 triple (sqrt3 E_T); momenta n in (-nmax..nmax)^d
function logZcal(m0,m2,ET,L,T0; nmax=6)
    s=0.0
    for nx in -nmax:nmax, ny in -nmax:nmax, nz in -nmax:nmax
        p=2pi .* (nx,ny,nz) ./ L
        s+= -log(1-exp(-T0*latE(m0,p))) - 5log(1-exp(-T0*latE(m2,p)))
    end
    for ny in -nmax:nmax, nz in -nmax:nmax
        p=2pi .* (ny,nz) ./ L
        s+= -3log(1-exp(-T0*latE(ET,p))) - 3log(1-exp(-T0*latE(sqrt(2)ET,p))) - log(1-exp(-T0*latE(sqrt(3)ET,p)))
    end
    s
end

function main()
    f=ARGS[1]; nbin=length(ARGS)>1 ? parse(Int,ARGS[2]) : 20
    beta,L,Lt,nlev,X=load(f); nm=size(X,1)
    A1,E,T=operators(X,L,Lt,nlev)
    A1=reshape(A1,size(A1)...,1)
    tmax=4
    @printf("%s  beta=%.2f L=%d Lt=%d nmeas=%d  <plaq>=%.6f\n",f,beta,L,Lt,nm,mean(X[:,1]))
    res=Dict{String,Any}()
    for (name,O,sub) in (("A1++",A1,true),("E++",E,false),("torelon",T,false))
        full,err,js=jack(idx->gevp_meff(corr(O,idx,sub),tmax),nm,nbin)
        res[name]=(full,err,js)
        @printf("  %-8s aE_eff(t=0..%d): %s\n",name,tmax-1,join((@sprintf("%.3f(%d)",full[k],round(Int,1000err[k])) for k in 1:tmax),"  "))
    end
    # energies: plateau value at t=1 (between slices 1 and 2) ; conservative lower value = central - 2 sigma
    T0=L÷2
    pick(nm_)= (res[nm_][1][2], res[nm_][2][2])
    (m0,s0)=pick("A1++"); (m2,s2)=pick("E++"); (et,se)=pick("torelon")
    lz=logZcal(m0,m2,et,L,T0); lzc=logZcal(max(m0-2s0,0.05),max(m2-2s2,0.05),max(et-2se,0.05),L,T0)
    @printf("  T0=%d: a m0=%.3f(%d) a m2=%.3f(%d) a E_T=%.3f(%d)\n",T0,m0,round(Int,1000s0),m2,round(Int,1000s2),et,round(Int,1000se))
    @printf("  log Zcal estimate = %.3e  (energies -2sigma: %.3e)   bound 1/8192 = %.3e\n",lz,lzc,1/8192)
end
main()
