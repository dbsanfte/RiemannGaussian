#!/usr/bin/env python3
"""Optional joint selected-background boundary audit; NOT a prime-sum bound.

The alternating background is summed before taking the two marked-leg
cutoff difference. Exact finite-lattice recurrences are checked against
count-by-count rational convolution. Continuum values use Dickman/Buchstab
renewal and precision/quadrature refinement, not interval certification.
A surviving pair coefficient is not a full multimode residue theorem.
Never run this exploratory probe in routine CI.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import math
import mpmath as mp
import numpy as np
from numpy.polynomial.legendre import leggauss

class Renewal:
    def __init__(self,end=50,degree=300,dps=140):
        mp.mp.dps=dps
        self.degree=degree
        self.rho_mp=[[mp.mpf(1)]+[mp.mpf(0)]*degree]
        self.omega_mp=[[mp.mpf(0)]*(degree+1)]
        half=mp.mpf('.5')
        for n in range(1,end+1):
            c=n+half
            prev=self.rho_mp[-1]
            row=[mp.mpf(0)]*(degree+1)
            for j in range(degree):
                row[j+1]=(-prev[j]-j*row[j])/(c*(j+1))
            row[0]=mp.polyval(prev[::-1],half)-mp.polyval(row[::-1],-half)
            self.rho_mp.append(row)
            if n==1:
                row=[(-1)**j/c**(j+1) for j in range(degree+1)]
            else:
                prev=self.omega_mp[-1]
                primitive=[mp.mpf(0)]+[prev[j]/(j+1) for j in range(degree)]
                primitive[0]=n*mp.polyval(prev[::-1],half)-mp.polyval(primitive[::-1],-half)
                row=[primitive[0]/c]
                for j in range(1,degree+1):row.append((primitive[j]-row[-1])/c)
            self.omega_mp.append(row)
        self.rho_table=np.array([[float(v) for v in row] for row in self.rho_mp])
        self.omega_table=np.array([[float(v) for v in row] for row in self.omega_mp])

    def val(self,kind,x):
        xx=np.asarray(x,dtype=float);out=np.zeros_like(xx)
        table=self.rho_table if kind=='rho' else self.omega_table
        inds=np.floor(xx).astype(int)
        for n in np.unique(inds):
            if n<0:continue
            assert n<len(table),(kind,x,n)
            mask=inds==n
            out[mask]=np.polynomial.polynomial.polyval(xx[mask]-n-.5,table[n])
        return float(out) if out.ndim==0 else out

    def val_mp(self,kind,x):
        x=mp.mpf(x);n=int(mp.floor(x))
        if n<0:return mp.mpf(0)
        table=self.rho_mp if kind=='rho' else self.omega_mp
        return mp.polyval(table[n][::-1],x-n-mp.mpf('.5'))

    def second_difference(self,s,d,order=32):
        # F(s,d)-2 F(s,d-1)+F(s,d-2), including the empty B atom.
        tri=lambda v:max(0,v)-2*max(0,v-1)+max(0,v-2)
        result=self.val('rho',s-1)/s*tri(d)
        cuts=sorted({0.,1.,2.}|{float(j-(s-d)) for j in range(1,100)
                               if 0<j-(s-d)<2}|
                    {float(d-j) for j in range(1,100) if 0<d-j<2})
        nodes,weights=leggauss(order)
        for lo,hi in zip(cuts,cuts[1:]):
            x=lo+(hi-lo)*(nodes+1)/2
            t=s-d+x
            y=np.minimum(x,2-x)*self.val('rho',t-1)/t*self.val('omega',d-x)
            result+=(hi-lo)/2*np.dot(weights,y)
        return result



def triangle(r,d):
    return max(0,d)-2*max(0,d-r)+max(0,d-2*r)


def lattice(ell,size,exact=False):
    """The exact recurrences formalized in ZetaRieszRenewalCurvature.

    A=exp(-sum_{j>=ell} X^j/j), B=1/A. D=A/(1-X) is positive.
    Every empty atom is one, and no factorial order is removed.
    """
    Q=Fraction if exact else mp.mpf
    dd,aa,bb=[Q(1)],[Q(1)],[Q(1)]
    small,rough=Q(1),Q(0)
    for n in range(1,size+1):
        if n>=ell:
            small-=dd[n-ell]
            rough+=bb[n-ell]
        dd.append(small/n)
        aa.append(-dd[n-ell]/n if n>=ell else Q(0))
        bb.append(rough/n)
        small+=dd[-1]
    return dd,aa,bb


def lattice_response(aa,bb,S,d):
    return -sum(aa[S-j]*bb[j]*max(0,d-j) for j in range(S+1))


def lattice_curvature(aa,bb,S,d,r):
    return -sum(aa[S-j]*bb[j]*triangle(r,d-j) for j in range(S+1))


def exact_regression():
    ell,S,d,r=20,185,Fraction(143,2),20
    dd,aa,bb=lattice(ell,S,True)
    counts=[[Fraction(int(n==0)) for n in range(S+1)]]
    for k in range(1,S//ell+1):
        prev=counts[-1]
        counts.append([sum((prev[n-j]/j for j in range(ell,n+1)),Fraction(0))/k
                       for n in range(S+1)])
    assert all(aa[n]==sum((-1)**k*c[n] for k,c in enumerate(counts))
               and bb[n]==sum(c[n] for c in counts) for n in range(S+1))
    assert all(sum(aa[:n+1])==dd[n] for n in range(S+1))
    observed=lattice_curvature(aa,bb,S,d,r)
    direct=lattice_response(aa,bb,S,d)-2*lattice_response(aa,bb,S,d-r)+        lattice_response(aa,bb,S,d-2*r)
    assert observed==direct and observed>0
    # ell is the smallest lattice atom: this comparison includes every
    # possible background count, and owner+two marked legs give <=12.
    _,lo_a,lo_b=lattice(5,215,True)
    lower=lattice_curvature(lo_a,lo_b,215,d,5)
    assert 0<lower<observed
    face_comparison=dict(common_cofactor_degree_before_pair=225,
        common_cutoff_d=str(d),lower_minimum_grid=5,upper_minimum_grid=20,
        lower_background_degree=215,upper_background_degree=185,
        lower_value=mp.nstr(mp.mpf(lower.numerator)/lower.denominator,40),
        lower_minus_upper_is_negative=True,
        scope='Exact rational fixed-slice recurrence; finite factorial faces and radial integration are not included.')
    return dict(cutoff=ell,total_degree=S,cutoff_d=str(d),pair_step=r,
        both_face_regression=face_comparison,
        background_count_cap=S//ell,total_with_owner_and_marked_pair=S//ell+3,
        count_convolution_identity=True,empty_atoms_retained=True,
        second_difference_identity=True,strictly_positive=True,
        exact_numerator_bits=observed.numerator.bit_length(),
        value=mp.nstr(mp.mpf(observed.numerator)/observed.denominator,40))


def full_response(renewal,s,d,order=64):
    """Inverse A*B ramp, including B's atom; valid for 0<d<s.

    a(v)=-rho(v-1)/v, b(v)=omega(v). A's atom is zero by d<s.
    """
    assert 0<d<s
    out=d*renewal.val('rho',s-1)/s
    lo,hi=max(1.,s-d),s-1
    if hi<=lo:return out
    cuts=sorted({lo,hi}|{float(j) for j in range(1,100) if lo<j<hi}|
                {float(s-j) for j in range(1,100) if lo<s-j<hi})
    nodes,weights=leggauss(order)
    for a,b in zip(cuts,cuts[1:]):
        v=a+(b-a)*(nodes+1)/2
        integrand=(v-(s-d))*renewal.val('rho',v-1)/v*renewal.val('omega',s-v)
        out+=(b-a)/2*np.dot(weights,integrand)
    return out


def continuum_checks():
    base=Renewal()
    fine=Renewal(degree=400,dps=180)
    u=mp.mpf(10001)/20000
    lam=-2*u*mp.log(u)
    rows=[]
    for p in (.525,.55,.575):
        for r,cap in ((.01,55),(.04,13)):
            s=(1-p)/r-2;d=(float(lam)-p)/r
            value=base.second_difference(s,d,32)
            quadrature=fine.second_difference(s,d,64)
            inverse=sum(c*full_response(fine,s,d-shift)
                        for c,shift in ((1,0),(-2,1),(1,2)))
            assert value>0 and abs(value-quadrature)<abs(value)*1e-11
            assert abs(inverse-quadrature)<abs(value)*1e-10
            background_cap=math.floor(s)
            assert background_cap+3<=cap
            # This rate concerns only the opposite-mode minimum corner.
            # It omits every other assignment and the full radial integral.
            rate=mp.log(u/(u-2*(mp.mpf(1)/40000)*mp.mpf(str(r))))
            rows.append(dict(owner_share=p,least_share=r,lambda_ratio=float(lam),
                background_total=s,cutoff_remainder=d,
                maximum_total_count=background_cap+3,retained_count_ceiling=cap,
                coefficient=quadrature,quadrature_change=quadrature-value,
                independent_ramp_difference_error=inverse-quadrature,
                pair_corner_candidate_log_rate=mp.nstr(rate,30),
                joined_face_sign=1 if r==.01 else -1))
    # A rational slice shared exactly by the Lean regression and refinements.
    truth=fine.second_difference(9.25,3.575,64)
    grid=[]
    for ell in (20,40,80,160,320,640,1280):
        S=37*ell//4;d=mp.mpf(143)*ell/40
        _,aa,bb=lattice(ell,S)
        value=lattice_curvature(aa,bb,S,d,ell)
        grid.append(dict(cutoff_grid=ell,value=mp.nstr(value,35),
                         difference_from_continuum=mp.nstr(value-truth,12)))
    assert abs(mp.mpf(grid[-1]['difference_from_continuum']))<        abs(mp.mpf(grid[0]['difference_from_continuum']))
    higher=[]
    for marked in (2,4,6,8,10):
        s=11.25-marked;d=3.575
        def ramp(t):
            if t<=0:return 0.
            if t>=s:return 1.
            return full_response(fine,s,t)
        difference=sum((-1)**j*math.comb(marked,j)*ramp(d-j)
                       for j in range(marked+1))
        if marked==10:
            # Only one background atom fits in total 5/4 at unit cutoff.
            exact=sum((-1)**j*math.comb(10,j)*
                      min(max(Fraction(0),Fraction(143,40)-j),Fraction(5,4))/Fraction(5,4)
                      for j in range(11))
            assert exact==Fraction(-96,5) and abs(difference-float(exact))<1e-12
        higher.append(dict(marked_legs=marked,background_total=s,
            background_count_cap=math.floor(s),difference=difference,
            upper_face_sign='negative' if difference>0 else 'positive'))
    return dict(method='unit-cell Taylor recurrence; positive triangle convolution',
        higher_even_differences=higher,
        higher_difference_scope='Fixed-slice coefficient only. Higher terms have BOTH signs; the empty-background coalescence is separate.',

        precisions=[140,180],taylor_degrees=[300,400],gauss_orders=[32,64],
        density_reference={'rho(2)':mp.nstr(fine.val_mp('rho',2),35),
            'omega(20)':mp.nstr(fine.val_mp('omega',20),35)},
        rows=rows,rational_slice_continuum=truth,lattice_refinement=grid,
        warning='Refinements are not certified error enclosures or prime-density transport.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    mp.mp.dps=180
    report=dict(scope='Selected-background pair coefficient, not the entire modal or arithmetic response',
        exact_lattice=exact_regression(),continuum=continuum_checks(),
        normalization='Owner has negative selected phase; response is minus the cofactor count sum.',
        target_unchanged='lowerThresholdPacket(3..55)-shortOverflowPacket(3..13)',
        unresolved=['Remaining mode assignments and corner terms',
            'Full radial/factorial integration with both finite beta faces',
            'Literal signed prime-sum bound and complementary arithmetic floor'],
        source='https://arxiv.org/abs/1303.1856, Sections 3.5-3.6',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
