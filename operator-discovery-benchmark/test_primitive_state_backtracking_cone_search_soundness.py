"""Synthetic continuation premises only; no publication data or source evaluation."""
import copy
from fractions import Fraction as F
import time
import unittest
import primitive_state_backtracking_cone_search as P
import check_primitive_state_backtracking_cone_search as C
from test_primitive_state_feedback_cone_search_soundness import fixture


def inputs():
    chart,center,_,cache,necessary,review,c=fixture()
    free=chart['free_indices'];ctx=P.OLD.context();z=[F(0)]*444;z[0]=F(1,4)
    base=list(map(F,center['candidate_projected_vector']));seed=list(base)
    for j,v in zip(free,z):seed[j]+=v
    b=P.Budget(time.monotonic()+30)
    rows={r['pivot']:{j:F(q)for j,q in r['terms']}for r in chart['normalized_rows']+[chart['appended_row']]}
    warm=P.EXACT.back_substitute(rows,seed,1224,b)
    original=P.EXACT.canonical_lift(warm,chart['retained_indices'],b)
    rec=lambda q:P.OLD.mp_record(P.OLD.to_mp(q,ctx,b))
    prior_map=dict(schema='primitive-state-feedback-cone-map-v1',complete=True,free_indices=free,pivot_columns=chart['pivot_columns'],center_projected_vector=list(map(str,base)),initial_free_vector=[str(base[j])for j in free],scaling=P.PREVIOUS.SCALING,scale_vector=['1']*444)
    proposal=dict(schema=P.PREVIOUS.SCHEMA,complete=True,status='proposed',stop_reason='line_search_failed',free_indices=free,scale_vector=['1']*444,normalizers=['2','3','4'],final_z_mp=[rec(v)for v in z],final_free_vector=[str(seed[j])for j in free],iterations=[dict(accepted=False,trials=[dict(index=i,finite=True,armijo_passed=False,step=rec(F(8,2**i)))for i in range(3)])])
    endpoint=dict(schema='primitive-state-feedback-cone-endpoint-v1',complete=True,free_indices=free,final_free_vector=proposal['final_free_vector'],final_projected_vector=list(map(str,warm)),candidate_original_vector=list(map(str,original)))
    return chart,center,prior_map,proposal,endpoint,c

class Soundness(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=inputs();cls.mapping,cls.receipt=P.setup(*cls.data[:5],deadline=time.monotonic()+30)
    def test_absolute_warm_increment_and_unrounded_center(self):
        m=self.mapping
        self.assertEqual(P.OLD.record_fraction(P.OLD.mp_record(m['warm_z'][0])),F(1,4))
        self.assertEqual(m['initial'][0],self.data[5])
        self.assertEqual(m['warm_free'][0],self.data[5]+F(1,4))
        self.assertGreater(m['warm_free'][0].denominator.bit_length(),269)
        self.assertEqual(m['warm_projected'][148],-m['warm_free'][0])
    def test_frozen_normalizers_and_step(self):
        self.assertEqual(self.mapping['fixed_normalizers'],[F(2),F(3),F(4)])
        self.assertEqual(self.receipt['normalizers'],['2','3','4'])
        self.assertEqual(P.OLD.record_fraction(self.receipt['initial_step']),F(1))
        self.assertEqual(P.SEARCH['power_steps'],0)
        self.assertEqual(P.SCALING['new_norm_calculations'],0)
    def test_missing_learned_row_rejected(self):
        data=copy.deepcopy(self.data[:5]);data[0]['appended_row']['terms']=[[148,'1']]
        with self.assertRaises(ValueError):P.setup(*data,deadline=time.monotonic()+30)
    def test_rounded_warm_endpoint_rejected(self):
        data=copy.deepcopy(self.data[:5]);data[4]['final_free_vector'][0]='5/4'
        with self.assertRaises(ValueError):P.setup(*data,deadline=time.monotonic()+30)
    def test_wrong_halving_and_partial_prior_rejected(self):
        data=copy.deepcopy(self.data[:5]);data[3]['complete']=False
        with self.assertRaises(ValueError):P.setup(*data,deadline=time.monotonic()+30)
        data=copy.deepcopy(self.data[:5]);data[3]['iterations'][-1]['trials'][1]['step']=data[3]['iterations'][-1]['trials'][0]['step']
        with self.assertRaises(ValueError):P.setup(*data,deadline=time.monotonic()+30)
    def test_zero_scale_rejected(self):
        data=copy.deepcopy(self.data[:5]);data[2]['scale_vector'][0]='0'
        with self.assertRaises(ValueError):P.setup(*data,deadline=time.monotonic()+30)
    def test_twelve_trial_reserve_matches_independent_formula(self):
        m=self.mapping
        license=type('L',(),dict(summary={'sparse_map_entries':sum(map(len,m['converted'].values()))},parent_vector=m['parent_projected'],free=m['free'],pivots=m['pivots'],source={'shape':[366,613],'offset':1597}))()
        self.assertEqual(P.iteration_work_reserve(m),C.iteration_work_reserve(license))
        self.assertGreaterEqual(P.iteration_work_reserve(m),12*2*96*15**3)

if __name__=='__main__':unittest.main()
