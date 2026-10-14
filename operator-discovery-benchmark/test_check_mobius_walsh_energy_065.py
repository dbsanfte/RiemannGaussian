"""Synthetic-only independent checker tests; no scientific artifacts."""
import copy
import itertools
import unittest
from fractions import Fraction as Q
from math import gcd,isqrt
import check_mobius_walsh_energy_065 as C

class ChargeOnly:
    def __init__(self):self.operations=0
    def charge(self,n=1):self.operations+=n
METER=ChargeOnly()

def fixture(rows,weights=None,cycles=None):
    H=max(6,len(rows));rs=rows+[{}]*(H-len(rows));weights=weights or ['1' if r else '0' for r in rs]
    parent=dict(schema='mobius-quadratic-contraction-v1',N=16,y=1,H=H,K=0,conditioned_primes=[],endpoints=[],budget='0')
    cert=dict(schema='mobius-walsh-energy-bound-v1',N=16,y=1,H=H,K=0,conditioned_primes=[],endpoints=[],budget='0')
    cost=sum((abs(Q(a)) for r in rs for a in r.values()),Q(0));parent['budget']=str(cost)
    for ratio in ['2/3','1']:
        parent['endpoints'].append(dict(ratio=ratio,rows=[dict(j=j,terms=[dict(index=i,coefficient=str(Q(a))) for i,a in sorted(r.items())]) for j,r in enumerate(rs,1)],l1=str(cost)))
        energy={}
        for r,w in zip(rs,weights):
            for i,a in r.items():
                for k,b in r.items():
                    key=i*k//gcd(i,k)**2;energy[key]=energy.get(key,Q(0))+Q(a)*Q(b)/Q(w)
        energy={i:a for i,a in energy.items() if a};l1=sum(map(abs,energy.values()),Q(0));cs=copy.deepcopy(cycles or [])
        upper=l1-2*sum((Q(c['mass']) for c in cs),Q(0));mass=sum(map(Q,weights),Q(0));vb=Q(isqrt(max(0,(mass*upper).numerator//(mass*upper).denominator))+1) if mass else Q(0)
        cert['endpoints'].append(dict(ratio=ratio,weights=weights[:],energy_terms=[dict(index=i,coefficient=str(a)) for i,a in sorted(energy.items())],cycles=cs,weight_mass=str(mass),energy_l1=str(l1),energy_upper=str(upper),variation_bound=str(vb)))
    cert['budget']=max((e['variation_bound'] for e in cert['endpoints']),key=Q)
    return parent,cert

def accept(p,c):return C.verify_energy(p,c,METER)

class Tests(unittest.TestCase):
    def reject(self,p,c):
        with self.assertRaises((ValueError,OverflowError,MemoryError)):accept(p,c)
    def test_diagonal_unit(self):
        p,c=fixture([{1:2}]);self.assertEqual(accept(p,c)['endpoints'][0]['energy_l1'],'4')
    def test_cross_row_coalescing(self):
        p,c=fixture([{1:1,2:1},{1:1,2:-1}]);self.assertEqual(accept(p,c)['endpoints'][0]['energy_l1'],'4')
    def test_shared_character_factors(self):
        p,c=fixture([{2:1,6:2}]);self.assertIn({'index':3,'coefficient':'4'},c['endpoints'][0]['energy_terms']);accept(p,c)
    def test_arbitrary_rational_weights(self):
        p,c=fixture([{1:'7/11',3:'-2/13'}],['17/19']+['0']*5);accept(p,c)
    def test_negative_cycle(self):
        p,c=fixture([{1:1,2:2,3:3,6:-1}],cycles=[dict(indices=[2,3,6],mass='2')]);accept(p,c)
    def test_shared_cycles(self):
        p,c=fixture([{1:1,2:2,3:3,6:-1}],cycles=[dict(indices=[2,3,6],mass='1')]*2);accept(p,c)
    def test_overconsumption(self):
        p,c=fixture([{1:1,2:2,3:3,6:-1}],cycles=[dict(indices=[2,3,6],mass='3')]);self.reject(p,c)
    def test_positive_cycle(self):
        p,c=fixture([{1:1,2:2,3:3,6:1}],cycles=[dict(indices=[2,3,6],mass='1')]);self.reject(p,c)
    def test_noncycle(self):
        p,c=fixture([{1:1,2:2,3:3,6:-1}],cycles=[dict(indices=[2,3],mass='1')]);self.reject(p,c)
    def test_cauchy_direction(self):
        p,c=fixture([{1:2}]);c['endpoints'][0]['variation_bound']='1';self.reject(p,c)
    def test_missing_weight(self):
        p,c=fixture([{1:1}]);c['endpoints'][0]['weights'].pop();self.reject(p,c)
    def test_missing_term(self):
        p,c=fixture([{1:1,2:1}]);c['endpoints'][0]['energy_terms'].pop();self.reject(p,c)
    def test_parameter_mismatch(self):
        p,c=fixture([{1:1}]);c['N']=32;self.reject(p,c)
    def test_ratio_mismatch(self):
        p,c=fixture([{1:1}]);c['endpoints'][0]['ratio']='3/4';self.reject(p,c)
    def test_zero(self):
        p,c=fixture([{}]);self.assertEqual(accept(p,c)['budget'],'0')
    def test_zero_row_positive_weight(self):
        p,c=fixture([{}]);c['endpoints'][0]['weights'][0]='1';self.reject(p,c)
    def test_nonzero_row_zero_weight(self):
        p,c=fixture([{1:1}]);c['endpoints'][0]['weights'][0]='0';self.reject(p,c)
    def test_strict_bool_index(self):
        p,c=fixture([{1:1}]);p['endpoints'][0]['rows'][0]['terms'][0]['index']=True;self.reject(p,c)
    def test_squareful(self):
        p,c=fixture([{4:1}]);self.reject(p,c)
    def test_noncanonical_rational(self):
        p,c=fixture([{1:1}]);c['endpoints'][0]['weight_mass']='2/2';self.reject(p,c)
    def test_conditioned_key(self):
        p,c=fixture([{2:1}]);p['conditioned_primes']=[2];c['conditioned_primes']=[2];self.reject(p,c)
    def test_parent_l1_mutation(self):
        p,c=fixture([{1:1}]);p['endpoints'][0]['l1']='2';self.reject(p,c)
    def test_coefficient_mutation(self):
        p,c=fixture([{1:1,2:2}]);c['endpoints'][0]['energy_terms'][0]['coefficient']='6';self.reject(p,c)
    def test_charge_only_and_work_cap(self):
        p,c=fixture([{1:1}]);accept(p,c)
        with self.assertRaises(OverflowError):C.verify_energy(p,c,C.Meter(cap=0))
    def test_exhaustive_soundness(self):
        for a,b,d in itertools.product((-2,-1,1,2),repeat=3):
            rows=[{1:a,2:b,3:d,6:-1},{2:1,3:-2}];p,c=fixture(rows);out=accept(p,c)
            energy={t['index']:Q(t['coefficient']) for t in c['endpoints'][0]['energy_terms']}
            for x,z in itertools.product((-1,1),repeat=2):
                chars={1:1,2:x,3:z,6:x*z};actual=sum(abs(sum(Q(v)*chars[i] for i,v in r.items())) for r in rows)
                ev=sum(v*chars[i] for i,v in energy.items())
                self.assertLessEqual(ev,Q(out['endpoints'][0]['energy_upper']));self.assertLessEqual(actual,Q(out['budget']))
    def test_exhaustive_cycle_soundness(self):
        p,c=fixture([{1:1,2:2,3:3,6:-1}],cycles=[dict(indices=[2,3,6],mass='2')]);out=accept(p,c)
        for x,z in itertools.product((-1,1),repeat=2):self.assertLessEqual(abs(1+2*x+3*z-x*z),Q(out['budget']))

if __name__=='__main__':
    unittest.main(exit=False)
    print('charged_work_units='+str(METER.operations))
