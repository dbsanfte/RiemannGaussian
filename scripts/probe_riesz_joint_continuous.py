#!/usr/bin/env python3
"""Optional continuous delay-equation audit of the joint modal flux.

This is only a synthetic continuum diagnostic, never an arithmetic bound.
Cutoff coordinates use a common delay of one, so there is no rounded cutoff
cell. All counts are included by the delay equation. The final convolutions
and radial/share integrals still require refinement and are not certified.
Use --em2 for the second-order trapezoid correction; compare resolutions.
Use --point-audit to compare convolution with separate adaptive quadrature.
Never run this diagnostic as part of ordinary CI.
"""
import argparse,hashlib,json,math,time
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp,quad
from scipy.linalg import eigh_tridiagonal
from scipy.signal import fftconvolve
from scipy.stats import binom
from probe_riesz_joint_renewal import gauss
from probe_riesz_joint_masked import rectangle_values

INTERP_NODES=np.arange(-2,4)
INTERP_POLYS=[np.polynomial.polynomial.polyfromroots([l for l in INTERP_NODES if l!=j])/
              math.prod(j-l for l in INTERP_NODES if l!=j) for j in INTERP_NODES]

def interpolate(table,indices,derivative=False):
    lo=np.floor(indices).astype(int);f=indices-lo;rows=np.arange(len(lo))
    result=np.zeros(len(lo))
    for j,poly in zip(INTERP_NODES,INTERP_POLYS):
        if derivative:poly=np.polynomial.polynomial.polyder(poly)
        result+=np.polynomial.polynomial.polyval(f,poly)*table[rows,lo+j]
    return result

def gamma_rule(k,n):
    i=np.arange(n,dtype=float);j=np.arange(1,n,dtype=float)
    x,v=eigh_tridiagonal(k+2*i,np.sqrt(j*(j+k-1)))
    return x,v[0]**2

def beta_rule(a,b,n):
    i=np.arange(n,dtype=float);j=np.arange(1,n,dtype=float)
    alpha,beta=b-1,a-1;s=alpha+beta
    diagonal=((beta-alpha)*s/((2*i+s)*(2*i+s+2))+1)/2
    off=np.sqrt(j*(j+alpha)*(j+beta)*(j+s)/((2*j+s-1)*(2*j+s+1)))/(2*j+s)
    x,v=eigh_tridiagonal(diagonal,off)
    return x,v[0]**2

class BatchCascade:
    def __init__(self,xis,amplitudes,end,tol):
        self.xis=np.asarray(xis,dtype=complex);self.amps=np.asarray(amplitudes)
        self.b,self.m=self.xis.shape
        self.parts=[]
        initial=np.ones((self.b,2,self.m),dtype=complex).ravel()
        start=2.
        while start<end:
            stop=min(start+1,end)
            def rhs(t,state):
                delayed=self.density(t-1)
                return (np.exp(-self.xis*(t-1))[:,None,:]*delayed[:,:,None]).ravel()
            sol=solve_ivp(rhs,(start,stop),initial,method='DOP853',rtol=tol,atol=tol/100,
                          dense_output=True,max_step=min(.1,.5/max(1,np.max(abs(self.xis.imag)))))
            assert sol.success
            self.parts.append(sol)
            initial=sol.y[:,-1]
            start=stop

    def density(self,t):
        if t<1-1e-13:return np.zeros((self.b,2),dtype=complex)
        state=np.ones((self.b,2,self.m),dtype=complex)
        if t>=2 and self.parts:
            index=min(max(0,int(t-2)),len(self.parts)-1)
            state=self.parts[index].sol(t).reshape(self.b,2,self.m)
        ans=np.sum(self.amps[None,None,:]*np.exp(self.xis*t)[:,None,:]*state,axis=2)/t
        ans[:,0]*=-1
        return ans

    def tables(self,step,end):
        # Sample the continuous density, not an atomic cutoff approximation.
        grid=np.arange(math.ceil(end/step)+8)*step
        aa=np.zeros((self.b,len(grid)));bb=np.zeros_like(aa)
        for left in range(1,math.ceil(end+8*step)+1):
            ids=np.flatnonzero((grid>=left)&(grid<left+1))
            if not len(ids):continue
            t=grid[ids]
            if left==1:state=np.ones((self.b,2,self.m,len(ids)),dtype=complex)
            else:state=self.parts[min(left-2,len(self.parts)-1)].sol(t).reshape(self.b,2,self.m,-1)
            val=np.sum(self.amps[None,None,:,None]*np.exp(self.xis[:,:,None]*t)[:,None,:,:]*state,axis=2)/t
            assert np.max(abs(val.imag))<1e-7*max(1,np.max(abs(val.real)))
            aa[:,ids]=-val[:,0,:].real;bb[:,ids]=val[:,1,:].real
        return grid,aa,bb

def convolution_response(obj,step,end,s,d,em2):
    """Keep both zero atoms; convolve the ordinary densities separately.

    The inverse is -d*a(s)-integral_(s-d)^(s-1) (v-(s-d))*a(v)*b(s-v)dv.
    The optional correction compensates trapezoid errors at the ramp corner,
    the jump of b at one, and the derivative jump of b at two. Higher errors
    are NOT certified: resolution and direct-quadrature checks remain needed.
    """
    grid,aa,bb=obj.tables(step,end)
    first=round(1/step)
    assert abs(first*step-1)<1e-12
    bb[:,first]*=.5
    gap=s-d
    c0=fftconvolve(aa*np.maximum(0,grid[None,:]-gap[:,None]),bb,axes=1,mode='full')[:,:len(grid)]*step
    result=-interpolate(c0,s/step)-d*interpolate(aa,s/step)
    if em2:
        g1=np.sum(obj.amps[None,:]*np.exp(obj.xis),axis=1).real
        bg1=np.sum(obj.amps[None,:]*np.exp(obj.xis)*(obj.xis-1),axis=1).real
        atop=interpolate(aa,(s-1)/step)
        adtop=interpolate(aa,(s-1)/step,True)/step
        upper=((d-1)*adtop+atop)*g1-(d-1)*atop*bg1
        bottom=interpolate(aa,gap/step)*interpolate(bb,d/step)
        frac=gap/step-np.floor(gap/step)
        jump2=np.where(d>2,(d-2)*interpolate(aa,(s-2)/step)*g1*g1/2,0)
        result+=step*step*(upper/12-(frac*frac-frac+1/6)*bottom/2-jump2/12)
    return result

def moving_length(n):
    return 2*math.log(20000**n//(10001**n*(n+1))+2)

def factorial_derivative_audit():
    """Compare the exact two beta faces with a central finite difference.

    This verifies normalization only, never an estimate for the prime sum.
    """
    from scipy.stats import beta
    rows=[]
    for n,p,r in [(640,.55,.011),(640,.55,.039),(1536,.55,.04)]:
        lo,hi=(21*n+39)//40,23*n//40
        hlo=max(0,(n+99)//100-1);hhi=n//25-1
        faces=[]
        for h in (hlo-1,hhi):
            conditional=binom.cdf(hi,n-h,p/(1-r))-binom.cdf(lo-1,n-h,p/(1-r))
            faces.append(beta.pdf(r,h+1,n-h+1)*conditional)
        predicted=faces[0]-faces[1]
        eps=1e-7
        observed=float((rectangle_values(n,np.array([p]),np.array([r+eps]))[0]-
                        rectangle_values(n,np.array([p]),np.array([r-eps]))[0])/(2*eps))
        error=abs(observed-predicted)
        assert error<1e-6,error
        rows.append(dict(N=n,p=p,r=r,exact_beta_faces=float(predicted),
                         finite_difference=observed,absolute_difference=error))
    return rows

def point_audit(n):
    """An independent quadrature of the same continuous convolution.

    The DDE and scipy error indicators are floating point, not interval
    enclosures. The unscaled old lattice discretization is also recorded.
    """
    from probe_riesz_joint_renewal import modal_series_pair
    p,r,T=.55,.04,2*n
    modes=np.array([0j,.000025-.006j,.000025+.006j]);amps=[1,3,3]
    s=(1-p)/r;d=(moving_length(n)/T-p)/r;gap=s-d
    obj=BatchCascade((T*r*modes)[None,:],amps,14,1e-11)
    points=sorted({gap,s-1}|{float(j) for j in range(1,100) if gap<j<s-1}
                  |{s-j for j in range(1,100) if gap<s-j<s-1})
    value=-d*obj.density(s)[0,0].real;indicator=0.
    for a,b in zip(points,points[1:]):
        f=lambda v:((v-gap)*obj.density(v)[0,0]*obj.density(s-v)[0,1]).real
        val,err=quad(f,a,b,epsabs=1e-10,epsrel=1e-10,limit=200)
        value-=val;indicator+=err
    rows=[]
    for den in [256,512,1024,2048,4096]:
        raw=float(convolution_response(obj,1/den,13,np.array([s]),np.array([d]),False)[0])
        corrected=float(convolution_response(obj,1/den,13,np.array([s]),np.array([d]),True)[0])
        rows.append(dict(inverse_step=den,raw=raw,corrected=corrected,
                         corrected_difference=corrected-value))
    old=[]
    for grid in [2048,4096,8192,16384,32768,65536]:
        step=.5/grid
        aa,bb=modal_series_pair(np.exp(modes[None,:]*T*step),amps,np.array([r]),step,grid+2)
        index=(1-p)/step;base=int(index);frac=index-base;answer=0.
        for k,weight in [(base,1-frac),(base+1,frac)]:
            x=step*np.arange(k+1)
            answer-=weight*np.sum(aa[0,:k+1]*bb[0,k::-1]*np.maximum(0,x-(1-moving_length(n)/T)))/step
        old.append(dict(grid=grid,response=float(answer.real),difference=float(answer.real-value)))
    return dict(N=n,T=T,p=p,r=r,direct_quadrature=float(value),
                quadrature_error_indicator=float(indicator),
                continuous_convolution=rows,old_lattice_discretization=old,
                warning='Error indicators and refinement are not certified enclosures.')

def run(N,rnodes,tnodes,pnodes,step,tol,em2=False):
    start=time.monotonic();u=10001/20000
    ts,tw=gamma_rule(N+1,tnodes);ts/=u
    radial_mask=(ts>1.95*N)&(ts<=2.03*N)
    tw*=radial_mask
    ps,pw=gauss(pnodes,.5,.6)
    L=moving_length(N)
    jlo,jhi=(21*N+39)//40,23*N//40
    hlow=max(0,(N+99)//100-1);hupper=N//25-1
    modes=np.array([0j,.000025-.006j,.000025+.006j]);amps=[1,3,3]
    results=[]
    for h in [hlow-1,hupper]:
        rs,rw=beta_rule(h+1,N-h+1,rnodes)
        # Restrict the diagnostic. The arithmetic exterior theorem is NOT
        # an estimate for the omitted synthetic endpoint contribution.
        rw*=(rs>.005)&(rs<.06)
        tt,rr=np.meshgrid(ts,rs,indexing='ij');tt=tt.ravel();rr=rr.ravel()
        weights=np.outer(tw,rw).ravel()
        end=.5/min(rr)
        obj=BatchCascade(modes[None,:]*(tt*rr)[:,None],amps,end+8*step,tol)
        grid,aa,bb=obj.tables(step,end)
        # A and B have an atom of mass one at zero; keep it separately.
        # Their continuous densities jump at the first possible cofactor.
        first=round(1/step)
        assert abs(first*step-1)<1e-12
        bb[:,first]*=.5
        gap=(1-L/tt)/rr
        c0=fftconvolve(aa*np.maximum(0,grid[None,:]-gap[:,None]),bb,axes=1,mode='full')[:,:len(grid)]*step
        g1=np.sum(np.asarray(amps)[None,:]*np.exp(obj.xis),axis=1).real
        bg1=np.sum(np.asarray(amps)[None,:]*np.exp(obj.xis)*(obj.xis-1),axis=1).real
        agap=interpolate(aa,gap/step)
        fraction=gap/step-np.floor(gap/step)
        bernoulli=fraction*fraction-fraction+1/6
        values=np.zeros(len(tt));rows=np.arange(len(tt))
        for p,w in zip(ps,pw):
            s=(1-p)/rr;d=(L/tt-p)/rr
            index=s/step
            continuous=-interpolate(c0,index)
            atom=-d*interpolate(aa,index)
            if em2:
                atop=interpolate(aa,(s-1)/step)
                adtop=interpolate(aa,(s-1)/step,True)/step
                upper=((d-1)*adtop+atop)*g1-(d-1)*atop*bg1
                bottom=agap*interpolate(bb,d/step)
                jump2=np.where(d>2,(d-2)*interpolate(aa,(s-2)/step)*g1*g1/2,0)
                continuous+=step*step*(upper/12-bernoulli*bottom/2-jump2/12)
            F=continuous+atom
            conditional=binom.cdf(jhi,N-h,p/(1-rr))-binom.cdf(jlo-1,N-h,p/(1-rr))
            owner=np.sum(np.asarray(amps)[None,:]*np.exp(modes[None,:]*(tt*p)[:,None]),axis=1).real
            values+=w*conditional*owner*F/(p*(L/tt))
        flux=float(np.sum(weights*values))
        results.append(dict(order=h,flux=flux,max_sampled_integrand=float(np.max(abs(values))),
                            elapsed=time.monotonic()-start))
        print('front',h,flux,'elapsed',time.monotonic()-start,flush=True)
    flux=results[0]['flux']-results[1]['flux']
    return dict(scope='Uncertified synthetic continuum flux, all counts, exact moving length and factorial derivative. Not actual prime data.',
                N=N,rnodes=rnodes,tnodes=tnodes,pnodes=pnodes,step=step,tolerance=tol,
                interpolation='six-point polynomial',euler_maclaurin_second_order=em2,
                radial_mass=float(np.sum(tw)),fronts=results,signed_flux=flux,
                log_raw_norm=math.log(abs(flux))-(N+1)*math.log(u) if flux else None,
                endpoint_note='Exterior least-share endpoints are omitted in this diagnostic, not asserted small for the synthetic model.',
                elapsed=time.monotonic()-start)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,default=65536)
    ap.add_argument('--rnodes',type=int,default=8);ap.add_argument('--tnodes',type=int,default=16)
    ap.add_argument('--pnodes',type=int,default=256);ap.add_argument('--step',type=float,default=1/512)
    ap.add_argument('--tol',type=float,default=1e-9);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--em2',action='store_true');ap.add_argument('--point-audit',action='store_true')
    a=ap.parse_args()
    assert a.order>=10000 and a.rnodes>=2 and a.tnodes>=2 and a.pnodes>=2
    assert a.step>0 and 0<a.tol<1e-3
    result=dict(status='Exploration only; no literal prime-sum estimate or certified numerical bound.',
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                dependency_sha256={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                    for name in ['probe_riesz_joint_renewal.py','probe_riesz_joint_masked.py']},
                factorial_derivative_audit=factorial_derivative_audit())
    if a.point_audit:result['point_audit']=point_audit(a.order)
    else:result['joint_flux']=run(a.order,a.rnodes,a.tnodes,a.pnodes,a.step,a.tol,a.em2)
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
