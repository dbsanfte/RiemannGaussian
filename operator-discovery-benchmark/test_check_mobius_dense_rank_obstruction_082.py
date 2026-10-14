import copy,unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_dense_rank_obstruction_082 as C
import check_mobius_dense_completion_082 as D

def fixture():
    p=dict(schema='dense-divisor-completion-v1',kernel=[{'divisor':2,'weight':'1'},{'divisor':3,'weight':'-1'}],memory=1,rays=[],drift_multiplier='3/2',profiles=[{'scale':'1','eta':'1'}],theta=[['0','0']],gram_weights=['0','0','0'])
    cert=dict(schema='dense-rank-interval-v1',intervals=[dict(left='13/50',right='7/25',profiles=[1],source=['0','0'],t='-1'),dict(left='7/20',right='2/5',profiles=[1],source=['1','0'],t='1')],tau='1/200',threshold=1440000,H00='1',lower_coefficient='1/40000')
    return p,cert
class Tests(unittest.TestCase):
    def test_generic_fullradius_uniform_witness_and_scope(self):
        p,c=fixture();r=C.verify_obstruction(p,c)
        self.assertEqual(r['status'],'VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION');self.assertTrue(r['uniform_completion_price_obstruction_proved']);self.assertEqual(r['profile_moments'],['0']);self.assertEqual(r['source_moments'],['1','0'])
        self.assertFalse(r['actual_arithmetic_drift_refuted']);self.assertFalse(r['uniform_source_bound_proved']);self.assertFalse(r['RH_proved']);self.assertTrue(r['source_kernel_binding_still_required'])
    def test_connects_to_exact_finite_rankone_dual(self):
        p,c=fixture();u=100;m=D.build_model(p,u);z=[Q(0)]*m['group_count']
        for row in c['intervals']:
            key=tuple(map(Q,row['source']))+tuple(map(Q,row['profiles']));g=m['features'].index(key);z[g]+=Q(c['tau'])*u*Q(row['t'])/m['counts'][g]
        self.assertTrue(all(abs(v)<=1 for v in z))
        lam=[str(v*v)for v in z];nu=[str(2*z[g]*z[h])for g in range(len(z))for h in range(g+1,len(z))]
        cert={'lambda':lam,'nu':nu,'lower_bound':str(Q(c['lower_coefficient'])*u*u)}
        r=D.verify_price_dual(p,u,cert);self.assertEqual(r['status'],'VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND');self.assertTrue(all(Q(v)==0 for v in r['zero_template_functionals']))
    def test_fractional_sublinear_profiles_and_duplicate_linear(self):
        p,c=fixture();p['profiles'] +=[{'scale':'5/7','eta':'17/31'},{'scale':'1/2','eta':'1'}];p['theta'] +=[['0','0'],['0','0']];p['gram_weights']+=['0','0']
        for row in c['intervals']:row['profiles'] +=[0,1]
        self.assertEqual(C.verify_obstruction(p,c)['status'],'VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION')
        c['threshold']=100;self.assertEqual(C.verify_obstruction(p,c)['status'],'INVALID')
    def test_exact_null_and_source_value_tampering(self):
        p,c=fixture()
        for mode in ['t','source','profiles']:
            bad=copy.deepcopy(c)
            if mode=='t':bad['intervals'][0]['t']='-1/2'
            if mode=='source':bad['intervals'][1]['source'][0]='0'
            if mode=='profiles':bad['intervals'][0]['profiles'][0]=0
            self.assertEqual(C.verify_obstruction(p,bad)['status'],'INVALID')
    def test_cell_boundaries_overlap_and_thresholds(self):
        p,c=fixture()
        for mode in ['sourcebreak','linearmargin','overlap','population','tau']:
            bad=copy.deepcopy(c)
            if mode=='sourcebreak':bad['intervals'][1]['left']='1/4'
            if mode=='linearmargin':bad['intervals'][0]['left']='1/4'
            if mode=='overlap':bad['intervals'][1]['left']='27/100'
            if mode=='population':bad['threshold']=1439999
            if mode=='tau':bad['tau']='1/100';bad['lower_coefficient']='1/10000'
            self.assertEqual(C.verify_obstruction(p,bad)['status'],'INVALID')
    def test_H00_energy_binding_and_parameter_independence(self):
        p,c=fixture();p['rays']=[{'a':['2'],'weight':'1/4'}]
        self.assertEqual(C.verify_obstruction(p,c)['status'],'INVALID');c['H00']='2';c['lower_coefficient']='1/20000'
        self.assertEqual(C.verify_obstruction(p,c)['status'],'VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION')
        p['theta']=[['16','-16']];p['gram_weights']=['16']*3
        self.assertEqual(C.verify_obstruction(p,c)['status'],'VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION')
    def test_strict_schema_canonical_rationals_unit_and_empty(self):
        p,c=fixture()
        for mode in ['schema','noncanonical','unit','empty','zero_t','bool']:
            bad=copy.deepcopy(c)
            if mode=='schema':bad['uniform_source_bound_proved']=True
            if mode=='noncanonical':bad['tau']='2/400'
            if mode=='unit':bad['intervals'][0]['left']='0'
            if mode=='empty':bad['intervals']=[]
            if mode=='zero_t':bad['intervals'][0]['t']='0'
            if mode=='bool':bad['threshold']=True
            self.assertEqual(C.verify_obstruction(p,bad)['status'],'INVALID')
    def test_resource_and_no_source_sieve(self):
        p,c=fixture()
        with patch.object(D,'squarefree_prefix',side_effect=AssertionError('uniform proof must not query squarefree populations')):
            self.assertEqual(C.verify_obstruction(p,c)['status'],'VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION')
        self.assertTrue(C.verify_obstruction(p,c,C.Meter(limit=1))['resource_limit'])
        p['profiles'][0]['eta']='1/100001';p['profiles'][0]['scale']='2'
        for row in c['intervals']:row['profiles'][0]=0
        self.assertTrue(C.verify_obstruction(p,c)['resource_limit'])
if __name__=='__main__':unittest.main()
