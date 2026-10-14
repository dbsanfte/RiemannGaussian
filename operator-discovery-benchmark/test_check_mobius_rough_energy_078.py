import copy
import unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_rough_energy_078 as C

def I(l,r,w):return {'left':l,'right':r,'weight':w}
def factors(n):
    ps=[];d=2
    while d*d<=n:
        if n%d==0:
            n//=d;ps.append(d)
            if n%d==0:return None
        d+=1
    if n>1:ps.append(n)
    return ps

def feature_fixture(rows,P,g):
    H=max((r['right'] for r in rows),default=0);g=Q(g);y=C.ceil_power(H,g);s1=C.ceil_power(H,g/3);s2=C.ceil_power(H,2*g/3)
    result=[{} for _ in range(10)]
    for n in range(1,H+1):
        ps=factors(n)
        if ps is None or any(n%p==0 for p in P):continue
        least=min(ps) if ps else float('inf');omega=len(ps);mu=(-1)**omega
        index=omega if least>y else 7 if least<=s1 else 8 if least<=s2 else 9
        for row in rows:
            if row['left']<n<=row['right']:
                for token,a in row['weight'].items():result[index][token]=result[index].get(token,Q(0))+mu*Q(a)
    return [{token:str(a) for token,a in poly.items() if a} for poly in result]
def program(rays=None):return {'schema':'rough-energy-program-v1','q':'1','tau':'1/2','rays':[] if rays is None else rays,'innovation_C':'3/8'}
def row(u,value):return {'u':u,'features':[{'1':str(value)}]+[{}]*9,'token_intervals':{'1':['1','1']}}
class Tests(unittest.TestCase):
    def test_independent_factor_sieve_and_cache(self):
        source=C.ensure_horizon(200)
        for n in range(1,201):
            fs=factors(n)
            expected=0 if fs is None else (-1)**len(fs)
            self.assertEqual(int(source['mu'][n]),expected)
            if fs is not None:
                self.assertEqual(int(source['omega'][n]),len(fs))
                if fs:self.assertEqual(int(source['least'][n]),min(fs))
        with self.assertRaises(ValueError):source['mu'][1]=0
        with patch.object(C.np,'ones',side_effect=AssertionError('largest cache reused')):self.assertEqual(int(C.ensure_horizon(100)['mu'][1]),1)
    def test_feature_all_boundaries_signs_and_tokens(self):
        rows=[I(0,40,{'1':'1','count:7^(-17/31)':'-2/3'}),I(43,160,{'1':'-2'})];P=[2,7];g='1/3';features=feature_fixture(rows,P,g)
        residual={}
        for poly in features:
            for token,a in poly.items():residual[token]=residual.get(token,Q(0))+Q(a)
        residual={token:str(a) for token,a in residual.items() if a}
        r=C.verify_features(rows,P,g,features,residual);self.assertEqual(r['status'],'VERIFIED_FEATURES');self.assertFalse(r['uniform_growth_proved'])
        bad=copy.deepcopy(features);bad[0]['1']='2';self.assertEqual(C.verify_features(rows,P,g,bad)['status'],'INVALID')
        self.assertEqual(C.verify_features(rows,P,g,features,{'1':'999'})['status'],'INVALID')
        with patch.object(C.np,'cumsum',side_effect=AssertionError('query cache reused')):self.assertEqual(C.verify_features(rows,P,g,features)['status'],'VERIFIED_FEATURES')
    def test_unit_empty_and_resource_domain(self):
        rows=[I(0,1,{'x':'1'})];features=feature_fixture(rows,[],'0')
        self.assertEqual(C.verify_features(rows,[],'0',features)['features'][0],{'x':'1'})
        self.assertEqual(C.verify_features([],[],'0',[{}]*10)['cutoff'],1)
        r=C.verify_features([I(0,100,{'x':'1'})],[],'0',[{}]*10)
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['domain_unpaid'])
        with patch.object(C.np,'ones',side_effect=AssertionError('must gate before allocation')):
            with self.assertRaises(C.AdmissionError):C.ensure_horizon(4000001)
    def test_arbitrary_gamma_and_unit_above_source_sentinel(self):
        rows=[I(0,17,{'x':'1'})]
        for gamma in ('17/31','1001/1000','53/17'):
            expected=feature_fixture(rows,[],gamma);r=C.verify_features(rows,[],gamma,expected)
            self.assertEqual(r['status'],'VERIFIED_FEATURES');self.assertEqual(r['features'][0],{'x':'1'})
        bad=copy.deepcopy(expected);bad[7]={'x':'99'}
        self.assertEqual(C.verify_features(rows,[],'53/17',bad)['status'],'INVALID')
    def test_prospective_memory_and_work_gates(self):
        with patch.object(C,'_resident',return_value=C.MEMORY_BUDGET),patch.object(C.np,'ones',side_effect=AssertionError('no oversize allocation')):
            with self.assertRaises(C.ResourceLimit):C.ensure_horizon(201)
        rows=[I(0,1,{'x':'1'})];r=C.verify_features(rows,[],'0',[{'x':'1'}]+[{}]*9,meter=C.Meter(0))
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit'])
    def test_energy_projection_and_finite_drift(self):
        p=program();parent=row(8,2);child=row(4,1);r=C.verify_drift(p,parent,child)
        self.assertEqual(r['status'],'CERTIFIED_FINITE');self.assertEqual(r['lower'],'3/8');self.assertEqual(r['upper'],'3/8');self.assertTrue(r['projection_verified']);self.assertFalse(r['complete_base_proved']);self.assertFalse(r['uniform_drift_proved']);self.assertFalse(r['RH_proved'])
        p['innovation_C']='0';self.assertEqual(C.verify_drift(p,parent,child)['status'],'REFUTED_FINITE')
        p=program([{'a':['1','-1']+['0']*8,'eta':'0','lambda':'1'}]);energy=C.verify_energy(p,parent)
        self.assertEqual(energy['energy_lower'],'8');self.assertEqual(energy['energy_upper'],'8')
    def test_shared_token_cancellation_and_interval_ambiguity(self):
        r=row(8,1);r['features']=[{'x':'1'},{'x':'-1'}]+[{}]*8;r['token_intervals']={'x':['-1','1']}
        e=C.verify_energy(program(),r);self.assertEqual(e['energy_upper'],'0')
        p=program();parent=row(8,1);parent['features'][0]={'x':'1'};parent['token_intervals']={'x':['1','2']};child=row(4,1);p['innovation_C']='1/8'
        self.assertEqual(C.verify_drift(p,parent,child)['status'],'UNRESOLVED_INTERVAL')
        parent['token_intervals']={'x':['-1','1']};energy=C.verify_energy(p,parent);self.assertEqual(energy['energy_lower'],'0')
    def test_fractional_eta_and_q_enclosures(self):
        p=program([{'a':['1','0']+['0']*8,'eta':'17/31','lambda':'2/3'}]);p['q']='1001/1000';r=C.verify_energy(p,row(8,2))
        self.assertEqual(r['status'],'VERIFIED_ENERGY_ENCLOSURE');self.assertGreaterEqual(Q(r['energy_lower']),4);self.assertGreaterEqual(Q(r['energy_upper']),Q(r['energy_lower']))
        self.assertGreaterEqual(Q(r['normalized_upper']),Q(r['normalized_lower']))
    def test_invalid_zero_projection_domain_and_binding(self):
        for a in (['0']*10,['1']*10,['-2']*10):self.assertEqual(C.verify_energy(program([{'a':a,'eta':'0','lambda':'1'}]),row(8,2))['status'],'INVALID')
        for key,value in [('q','2'),('tau','-1'),('tau','3/2'),('innovation_C','-1')]:
            p=program();p[key]=value;self.assertEqual(C.verify_energy(p,row(8,2))['status'],'INVALID')
        p=program([{'a':['1','0']+['0']*8,'eta':'0','lambda':'0'}]);self.assertEqual(C.verify_energy(p,row(8,2))['status'],'INVALID')
        self.assertEqual(C.verify_drift(program(),row(8,2),row(3,1))['status'],'INVALID')
        bad=row(8,2);bad['token_intervals']={};self.assertEqual(C.verify_energy(program(),bad)['status'],'INVALID')
if __name__=='__main__':unittest.main()
