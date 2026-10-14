"""Synthetic/tiny independent fixtures only; no producer or old-suite imports."""
import copy
import unittest
from unittest.mock import patch
from fractions import Fraction as Q
import check_mobius_count_control_076 as C

def data_fixture(us=(17,80,160,400)):
    spec={'grid':80,'theta':['1/2','3/4'],'multipliers':[2,3]}
    def mu(n):
        s=1;p=2
        while p*p<=n:
            if n%p==0:
                n//=p;s=-s
                if n%p==0:return 0
            p+=1
        return -s if n>1 else s
    def M(n):return sum(mu(j) for j in range(1,n+1))
    def G(u):return M(u//8)-M(u//10)-M(u//4)+M(u//5)
    rows=[]
    for u in us:
        x=u//4;cuts=[C.F.cut(x,Q(t),C.Meter()) for t in spec['theta']]
        primes=[p for p in range(cuts[0]+1,cuts[1]+1) if p>=2 and all(p%d for d in range(2,p))]
        vs=[G(u//p) for p in primes];direct=[G(u//d) for d in spec['multipliers']]
        rows.append(dict(u=u,X=x,cuts=cuts,z=G(u),components=[sum(vs)]+direct,moments=[sum(v*v for v in vs)]+[v*v for v in direct],counts=[len(primes),1,1]))
    return dict(schema='prime-grid-moment-data-v1',spec=spec,rows=rows)
def program(d):
    return dict(schema='count-adaptive-control-program-v1',spec=d['spec'],atoms=[],operator=[],beta=['0']*3,correlation_mode='structural_cauchy',q='1',base_u=16,price_bounds=['10','1/2','1/3'],rho_upper='0',sqrt_rho_upper='0',innovation_C='100',base_upper='100',bound_B='100',precision=8,training_scales=[r['u'] for r in d['rows']],uniform_innovation_proved=False,uniform_source_bound_proved=False,RH_proved=False)
class Tests(unittest.TestCase):
    def test_baseline_full_base_and_flags(self):
        d=data_fixture();r=C.verify_program(program(d),d)
        self.assertEqual(r['status'],'VERIFIED_ON_FINITE_DOMAIN');self.assertTrue(r['conditional_induction_verified']);self.assertTrue(r['universal_correlation_proved']);self.assertFalse(r['RH_proved']);self.assertFalse(r['uniform_source_bound_proved']);self.assertEqual(r['complete_base']['integers_checked'],16)
        p=program(d);p['base_upper']='0';self.assertEqual(C.verify_program(p,d)['status'],'INVALID')
    def test_repeated_columns_negative_and_direct_gamma(self):
        d=data_fixture();p=program(d);p.update(atoms=[{'column':1,'gamma':'0'},{'column':1,'gamma':'17/31'},{'column':2,'gamma':'1001/1000'}],operator=['1/10','-1/10','-1/10'],beta=['0','1/10','1/20'],rho_upper='1/10',sqrt_rho_upper='1/2',innovation_C='20')
        r=C.verify_program(p,d);self.assertEqual(r['status'],'VERIFIED_ON_FINITE_DOMAIN');self.assertTrue(r['universal_correlation_proved'])
        lo,hi=C.operator_interval(d['rows'][1],[(1,Q(0)),(1,Q(17,31)),(2,Q(1001,1000))],[Q(1,10),Q(-1,10),Q(-1,10)],8)
        self.assertEqual(lo,hi);self.assertEqual(lo,-Q(d['rows'][1]['components'][2],10))
    def test_fractional_gamma_roots_and_cache(self):
        for g in (Q(17,31),Q(1001,1000),Q(1,2)):
            lo,hi=C.count_enclosure(7,g,8);self.assertLessEqual(lo**g.denominator,7**g.numerator);self.assertGreaterEqual(hi**g.denominator,7**g.numerator)
            with patch.object(C,'power_enclosure',side_effect=AssertionError('cache must avoid roots')):self.assertEqual(C.count_enclosure(7,g,8),(lo,hi))
        self.assertEqual(C.count_enclosure(0,Q(10**100),8),(Q(1),Q(1)))
    def test_empty_counts_units_and_signed_intervals(self):
        d=data_fixture((1,2,3,17));self.assertEqual(C.F.verify_data(d)['status'],'VERIFIED')
        row={'components':[0,1],'counts':[0,1]};lo,hi=C.operator_interval(row,[(0,Q(17,31)),(1,Q(1,3))],[Q(-3),Q(-2)],8)
        self.assertEqual((lo,hi),(Q(-2),Q(-2)))
        self.assertEqual(C.square_interval(Q(-2),Q(3)),(Q(0),Q(9)))
    def test_structural_rejections(self):
        d=data_fixture();p=program(d);p.update(atoms=[{'column':0,'gamma':'17/31'}],operator=['1/100'],beta=['1/100','0','0'],rho_upper='1/10',sqrt_rho_upper='1/2',innovation_C='20')
        self.assertTrue(C.verify_program(p,d)['universal_correlation_proved'])
        for gamma,beta in [('1/3',['1/100','0','0']),('1/2',['0','0','0']),('1/2',['1/1000000','0','0'])]:
            t=copy.deepcopy(p);t['atoms'][0]['gamma']=gamma;t['beta']=beta;self.assertEqual(C.verify_program(t,d)['status'],'INVALID')
        p['operator']=['0'];p['atoms'][0]['gamma']='0';p['beta']=['0']*3;self.assertTrue(C.verify_program(p,d)['universal_correlation_proved'])
    def test_input_binding_and_tampering(self):
        d=data_fixture();p=program(d)
        for key,value in [('RH_proved',True),('uniform_innovation_proved',True),('sqrt_rho_upper','-1/2'),('sqrt_rho_upper','1'),('price_bounds',['0']*3),('rho_upper','1'),('training_scales',[])]:
            t=copy.deepcopy(p);t[key]=value;self.assertEqual(C.verify_program(t,d)['status'],'INVALID',key)
        t=copy.deepcopy(d);t['spec']['multipliers']=[2,4];self.assertEqual(C.verify_program(p,t)['status'],'INVALID')
        t=copy.deepcopy(p);t['atoms']=[{'column':0,'gamma':'2/4'}];t['operator']=['0'];self.assertEqual(C.verify_program(t,d)['status'],'INVALID')
        t['atoms']=[{'column':0,'gamma':'1'},{'column':0,'gamma':'1/2'}];t['operator']=['0','0'];self.assertEqual(C.verify_program(t,d)['status'],'INVALID')
    def test_arithmetic_refutation_and_innovation_ambiguity(self):
        d=data_fixture();p=program(d);p.update(atoms=[{'column':1,'gamma':'0'}],operator=['10'],correlation_mode='arithmetic_claim')
        r=C.verify_program(p,d);self.assertEqual(r['status'],'REFUTED');self.assertFalse(r['universal_correlation_proved']);self.assertTrue(any(f['lemma']=='correlation' and f['status']=='REFUTED' for f in r['failures']))
        p=program(d);p['q']='3/2';p['training_scales']=[17];z=d['rows'][0]['z'];lo,hi=C.power_enclosure(17,Q(3,2),8,C.Meter());p['innovation_C']=str((Q(z*z)/lo+Q(z*z)/hi)/2)
        self.assertEqual(C.verify_program(p,d)['status'],'UNRESOLVED_ROUNDING')
    def test_correlation_rounding_and_zero_crossing(self):
        # Synthetic source values: source admission intentionally separate.
        d=data_fixture((80,));d['rows'][0].update(components=[1,0,0],moments=[1,0,0],counts=[2,1,1],z=0)
        lo,hi=C.count_enclosure(2,Q(1,3),8)
        midpoint=(1/lo**2+1/hi**2)/2;p=program(d);p.update(atoms=[{'column':0,'gamma':'1/3'}],operator=['1/10'],beta=[str(midpoint/100),'0','0'],correlation_mode='arithmetic_claim',rho_upper='1/10',sqrt_rho_upper='1/2',innovation_C='20')
        r=C.verify_program(p,d);self.assertEqual(r['status'],'UNRESOLVED_ROUNDING');self.assertEqual(r['failures'][0]['lemma'],'correlation')
        atoms=[(0,Q(1,3)),(1,Q(0))];a=[Q(1),-(1/lo+1/hi)/2];row={'components':[1,1],'counts':[2,1]}
        Llo,Lhi=C.operator_interval(row,atoms,a,8);self.assertLess(Llo,0);self.assertGreater(Lhi,0);self.assertEqual(C.square_interval(Llo,Lhi)[0],0)
    def test_structural_boundary_tightening_and_power_gate(self):
        d=data_fixture((80,));d['rows'][0].update(components=[2,0,0],moments=[2,0,0],counts=[2,1,1],z=0)
        p=program(d);p.update(atoms=[{'column':0,'gamma':'1/2'}],operator=['1/10'],beta=['1/100','0','0'],rho_upper='1/10',sqrt_rho_upper='1/2',innovation_C='20')
        r=C.verify_program(p,d);self.assertEqual(r['status'],'VERIFIED_ON_FINITE_DOMAIN');self.assertEqual(r['correlation_theorem_tightenings'],1)
        with self.assertRaises(C.ResourceLimit):C.count_enclosure(2,Q(1,10**100),8)
    def test_base_cache_independent_and_memory_gate(self):
        first=C.complete_base_bound(19,Q(1),8);first['upper']=Q(0)
        with patch.object(C.F,'source',side_effect=AssertionError('cached full base')):
            second=C.complete_base_bound(19,Q(1),8)
        self.assertGreater(second['upper'],0)
        d=data_fixture();p=program(d);p['base_u']=10**100;p['training_scales']=[10**100+1]
        with patch.object(C.F,'source',side_effect=AssertionError('prospective rejection')):r=C.verify_program(p,d)
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit']);self.assertIn('memory',r['reason'])
        self.assertEqual(C.verify_program(program(d),d,C.Meter(0))['status'],'INVALID')
if __name__=='__main__':unittest.main()
