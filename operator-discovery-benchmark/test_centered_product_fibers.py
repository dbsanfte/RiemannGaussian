import unittest
from fractions import Fraction as Q
from math import gcd

from flint import arb,ctx
import centered_product_fibers as P


class Meter:
    operations=0
    def charge(self,n=1):
        type(self).operations+=n
    def live(self,n):
        pass


def fixture(a_values,m_values):
    H=len(a_values)-1
    a=list(map(arb,a_values));m=list(map(arb,m_values))
    b=[x-y for x,y in zip(a,m)]
    R=[arb(0)]*(H+1)
    mu=[0]*(H+1);mu[1]=1
    for n in range(2,H+1):
        residual=n;sign=1
        p=2
        while p*p<=residual:
            if residual%p==0:
                residual//=p;sign=-sign
                if residual%p==0:
                    sign=0;break
                while residual%p==0:residual//=p
            p+=1
        if sign and residual>1:sign=-sign
        mu[n]=sign
    for n in range(1,H+1):R[n]=R[n-1]+b[n]
    Meter.operations+=100*(H+1)
    return dict(H=H,a=a,m=m,b=b,R=R,mu=mu,sixth=[arb(0)]+[arb(n).root(6) for n in range(1,H+1)])


def literal(X,T,gamma,state,band=None):
    N=2*X-1
    values={key:arb(0) for key in P.SECTORS}
    centered=arb(0)
    for h in range(1,N+1):
        for k in range(1,N+1):
            product=h*k
            if product>T or (band is not None and 2*product<=band):continue
            weight=arb(2*X-max(X,h,k))/(X*X)
            if gamma:
                weight/=arb(product).root(6)**int(6*gamma)
            sf=bool(state['mu'][h] and state['mu'][k] and gcd(h,k)==1)
            suffix='_sf' if sf else '_ns'
            a,m,b=state['a'],state['m'],state['b']
            values['aa'+suffix]+=weight*a[h]*a[k]
            values['cross'+suffix]-=weight*(a[h]*m[k]+m[h]*a[k])
            values['mm'+suffix]+=weight*m[h]*m[k]
            centered+=weight*b[h]*b[k]
            Meter.operations+=100
    values['centered']=centered
    return values


class CenteredProductTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=160

    def test_quadratic_inverse_and_unpaid_unstable_recovery(self):
        grammar=P.stencils()
        self.assertEqual(len(grammar),25)
        for row in grammar:
            g=P.inverse_coefficients(row['coefficients'],12,Meter())
            for n in range(12):
                coefficient=sum(row['coefficients'][k]*g[n-k] for k in range(3) if n>=k)
                self.assertEqual(coefficient,int(n==0))
            if row['cofinal_inverse_admitted']:
                self.assertTrue(all(abs(value)<=n+1 for n,value in enumerate(g)))
        unstable=next(row for row in grammar if row['coefficients']==[1,-2,0])
        self.assertFalse(unstable['cofinal_inverse_admitted'])
        self.assertEqual(P.inverse_coefficients([1,-2,0],8,Meter()),[2**n for n in range(8)])

    def test_complete_six_sector_scatter_with_units_and_repeats(self):
        state=fixture([0,0,2,-1,3,0,-2,1],[0,1,1,1,1,1,1,1])
        rows=P.scatter(4,state,Meter())
        values=P.profiles(4,rows,state,[0,1,6,15,49],Meter())
        for T in values:
            for gamma in P.GAMMAS:
                reference=literal(4,T,Q(gamma),state)
                for key,value in reference.items():
                    self.assertTrue((values[T][gamma][key]-value).contains(0),(T,gamma,key))
        self.assertTrue(values[1]['0']['mm_sf']>0)
        self.assertTrue((values[49]['0']['centered_sf']+values[49]['0']['centered_ns']-values[49]['0']['centered']).contains(0))

    def test_full_kernel_recovers_weighted_prefix_square(self):
        state=fixture([0,1,-2,3,-1,2,-4,1],[0,1,0,1,0,1,0,1])
        rows=P.scatter(4,state,Meter())
        totals=P.profiles(4,rows,state,[49],Meter())[49]
        diagnostics=P.prefix_diagnostics(4,state,Meter())
        for gamma in P.GAMMAS:
            self.assertTrue((totals[gamma]['centered']-diagnostics['weighted_energy'][gamma]).contains(0))
        self.assertTrue((diagnostics['normalized_abel_energy']['0']-diagnostics['original_energy']).contains(0))

    def test_all_partial_breakpoints_against_literal_source(self):
        state=fixture([0,1,-3,2],[0,1,1,1])
        rows=P.scatter(2,state,Meter());grammar=P.stencils()
        result=P.search_bands(2,rows,state,grammar,Meter())
        J=result['J'];points={Q(1,2),Q(1)}
        for h in range(1,4):
            for k in range(1,4):
                product=h*k;j=(product-1).bit_length()
                points.add(Q(product,1<<j))
        direct={}
        for gamma_text in P.GAMMAS:
            gamma=Q(gamma_text)
            for point in points:
                bands=[]
                for j in range(J+1):
                    top=1<<j;cutoff=(point.numerator*top)//point.denominator
                    value=literal(2,cutoff,gamma,state,band=top)['centered']
                    if gamma:value*=arb(top).root(6)**int(6*gamma)
                    bands.append(value)
                for stencil in grammar:
                    if not stencil['cofinal_inverse_admitted']:continue
                    maximum=direct.get((stencil['id'],gamma_text),arb(0))
                    for j in range(J+1):
                        value=sum((stencil['coefficients'][offset]*bands[j-offset] for offset in range(3) if j>=offset),arb(0))
                        maximum=maximum.max(value.abs_upper())
                    direct[(stencil['id'],gamma_text)]=maximum
        energy=P.prefix_diagnostics(2,state,Meter())['original_energy']
        for row in result['candidates']:
            expected=direct[(row['stencil_id'],row['gamma'])]
            self.assertTrue(abs(row['upper']-expected)<arb(2)**-90)
            self.assertTrue(row['recovered_energy_upper']>=energy.lower())
            self.assertFalse(row['uniform_in_X_proved'])
            self.assertFalse(row['RH_proved'])

    def test_unit_only_head_and_zero_source(self):
        for a,m in (([0,0],[0,2]),([0,0],[0,0])):
            state=fixture(a,m);rows=P.scatter(1,state,Meter())
            result=P.search_bands(1,rows,state,P.stencils(),Meter())
            self.assertEqual(result['J'],0)
            for row in result['candidates']:
                self.assertTrue((row['upper']-state['b'][1]**2).contains(0))

    def test_selected_pairs_keep_their_original_semantics(self):
        state=fixture([0,1,-2,3],[0,1,1,1]);rows=P.scatter(2,state,Meter())
        grammar=P.stencils();admitted=[r for r in grammar if r['cofinal_inverse_admitted']]
        pairs={(admitted[0]['id'],'1/6'),(admitted[-1]['id'],'0')}
        result=P.search_bands(2,rows,state,grammar,Meter(),pairs)
        self.assertEqual({(r['stencil_id'],r['gamma']) for r in result['candidates']},pairs)
        with self.assertRaises(ValueError):P.search_bands(2,rows,state,grammar,Meter(),{(-1,'0')})

    def test_profile_and_state_domains(self):
        state=fixture([0,1],[0,0])
        with self.assertRaises(ValueError):P.scatter(2,state,Meter())
        rows=P.scatter(1,state,Meter())
        with self.assertRaises(ValueError):P.profiles(1,rows,state,[-1],Meter())
        with self.assertRaises(ValueError):P.inverse_coefficients([2,0,0],4,Meter())
        encoded=P.serialize({'x':arb(1),'y':[False]})
        self.assertTrue(arb(encoded['x']).contains(1))
        self.assertEqual(encoded['y'],[False])


def tearDownModule():
    print('SYNTHETIC_WORK module=test_centered_product_fibers operations='+str(Meter.operations))


if __name__=='__main__':unittest.main()
