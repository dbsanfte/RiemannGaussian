import copy
import unittest
from unittest.mock import patch
from fractions import Fraction
import check_mobius_prime_moment_075 as c

def fixture(us=(17,80,160,400)):
    spec={'grid':80,'theta':['1/2','3/4'],'multipliers':[2,3]}
    def mu(n):
        sign=1; d=2
        while d*d<=n:
            if n%d==0:
                n//=d; sign=-sign
                if n%d==0:return 0
            d+=1
        return -sign if n>1 else sign
    def M(n):return sum(mu(k) for k in range(1,n+1))
    def G(u):return M(u//8)-M(u//10)-M(u//4)+M(u//5)
    rows=[]
    for u in us:
        x=u//4; cuts=[c.cut(x,Fraction(t),c.Meter()) for t in spec['theta']]
        ps=[p for p in range(cuts[0]+1,cuts[1]+1) if p>=2 and all(p%d for d in range(2,p))]
        vals=[G(u//p) for p in ps]; direct=[G(u//d) for d in spec['multipliers']]
        rows.append(dict(u=u,X=x,cuts=cuts,z=G(u),components=[sum(vals)]+direct,moments=[sum(v*v for v in vals)]+[v*v for v in direct],counts=[len(ps),1,1]))
    return dict(schema='prime-grid-moment-data-v1',spec=spec,rows=rows)
def program(data):
    return dict(schema='prime-grid-control-program-v1',spec=data['spec'],q='1',operator=['0']*3,beta=['0']*3,base_u=16,price_bounds=['10','1/2','1/3'],rho_upper='0',sqrt_rho_upper='0',innovation_C='100',base_upper='100',bound_B='100',precision=8,training_scales=[r['u'] for r in data['rows']],uniform_innovation_proved=False,uniform_correlation_proved=False,uniform_source_bound_proved=False,RH_proved=False)
class Tests(unittest.TestCase):
    def test_source(self):
        d=fixture(tuple(range(1,501))); self.assertEqual(c.verify_data(d)['status'],'VERIFIED')
        d['rows'][79]['moments'][0]+=1; self.assertEqual(c.verify_data(d)['status'],'INVALID')
    def test_program_and_no_promotion(self):
        d=fixture(); r=c.verify_program(program(d),d)
        self.assertEqual(r['status'],'VERIFIED_ON_FINITE_DOMAIN'); self.assertTrue(r['conditional_induction_verified']); self.assertFalse(r['RH_proved']); self.assertFalse(r['uniform_source_bound_proved'])
    def test_tampering(self):
        d=fixture(); p=program(d)
        for key,value in [('RH_proved',True),('price_bounds',['0']*3),('rho_upper','1'),('base_upper','0')]:
            t=copy.deepcopy(p);t[key]=value;self.assertEqual(c.verify_program(t,d)['status'],'INVALID',key)
        t=copy.deepcopy(d);t['spec']['multipliers']=[2,4];self.assertEqual(c.verify_program(p,t)['status'],'INVALID')
    def test_direct_cauchy(self):
        d=fixture();p=program(d);p.update(operator=['0','1/3','0'],beta=['0','1/9','0'],rho_upper='1/18',sqrt_rho_upper='1/2',innovation_C='20')
        self.assertTrue(c.verify_program(p,d)['universal_direct_correlation_proved'])
        p['operator'][1]='1/2'; self.assertFalse(c.verify_program(p,d)['universal_direct_correlation_proved'])
    def test_finite_counterexamples(self):
        d=fixture();p=program(d);p['innovation_C']='0'
        self.assertEqual(c.verify_program(p,d)['status'],'REFUTED')
        p=program(d);p['operator']=['10','0','0']
        self.assertEqual(c.verify_program(p,d)['status'],'REFUTED')
    def test_roots_and_denominators(self):
        for n in (1,2,15,16,17,65535,65536,65537):
            q=Fraction(7,5);lo,hi=c.power_enclosure(n,q,8,c.Meter());self.assertLessEqual(lo**5,n**7);self.assertGreaterEqual(hi**5,n**7)
        d=fixture();p=program(d);p['q']='1001/1000';self.assertEqual(c.verify_program(p,d)['status'],'VERIFIED_ON_FINITE_DOMAIN')
    def test_rounding_straddle(self):
        d=fixture();p=program(d);p['q']='3/2';p['training_scales']=[17]
        z=d['rows'][0]['z'];lo,hi=c.power_enclosure(17,Fraction(3,2),8,c.Meter())
        self.assertNotEqual(z,0)
        p['innovation_C']=str((Fraction(z*z)/lo+Fraction(z*z)/hi)/2)
        self.assertEqual(c.verify_program(p,d)['status'],'UNRESOLVED_ROUNDING')
    def test_prospective_memory_without_allocation(self):
        d=fixture();p=program(d);p['base_u']=10**100;p['training_scales']=[10**100+1]
        with patch.object(c,'source',side_effect=AssertionError('must reject before source')):
            r=c.verify_program(p,d)
        self.assertEqual(r['status'],'INVALID');self.assertIn('prospective base',r['reason'])
        m=c.Meter()
        with patch.object(c,'array',side_effect=AssertionError('must reject before array')):
            with self.assertRaises(c.ResourceLimit):c.source(10**100,m)
        self.assertGreater(m.peak_bytes,c.MEMORY_BUDGET)
        m=c.Meter();m.pending_bytes=c.MEMORY_BUDGET
        with patch.object(c,'array',side_effect=AssertionError('must account pending allocations')):
            with self.assertRaises(c.ResourceLimit):c.source(1,m)
    def test_limits_and_canonical(self):
        self.assertEqual(c.verify_data(fixture(),c.Meter(0))['status'],'INVALID')
        d=fixture();d['spec']['theta'][0]='2/4';self.assertEqual(c.verify_data(d)['status'],'INVALID')
if __name__=='__main__':unittest.main()
