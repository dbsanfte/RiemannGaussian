"""Synthetic exact chart/reduction/repair tests, no research source replay."""
import copy
import time
import unittest
from fractions import Fraction as F
from unittest.mock import patch
import hashlib
import primitive_state_feedback_affine as P
import check_primitive_state_feedback_affine as C


def fixture(kind='independent'):
    original=dict(shape=[366,613],offset=1597,specs=[['full_child',15],['full_parent',15],['storage_K',15]])
    retained,recipes=C.projection_layout(original);columns=[{}for _ in range(1957)]
    for i in range(5641):columns[retained[i%779]][i]=F(1)
    for omitted,recipe in recipes.items():
        for j,q in recipe.items():
            for i,v in columns[j].items():columns[omitted][i]=columns[omitted].get(i,F(0))+q*v
    original.update(columns=[[[i,str(q)]for i,q in sorted(p.items())if q]for p in columns],rhs=['0']*5641,monomials=[[i]for i in range(5641)])
    projection=dict(complete=True,status='complete',original_columns=1957,projected_columns=1224,rows=5641,retained_indices=retained,recipes=[[i,[[j,str(q)]for j,q in sorted(r.items())]]for i,r in sorted(recipes.items())])
    tape=dict(complete=True,status='complete',coefficient_consistency='consistent',inconsistent_augmented_pivots=[],variables=1224,original_rows=5641,augmented_rhs_column=1224,row_order=list(range(5641)),transcript=[dict(source_row=i,steps=[],pivot_column=i,normalization='1',basis_index=i)for i in range(779)]+[dict(source_row=i,steps=[[i%779,'1']],pivot_column=None,normalization=None,basis_index=None)for i in range(779,5641)],retained_indices=list(range(779)),pivot_columns=list(range(779)),augmented_rank=779,variable_mapping='identity',objective_mapping='identity',cone_mapping='identity')
    full=[F(0)]*1957
    if kind!='inconsistent':full[retained[800 if kind=='independent'else 20]]=F(1)
    for omitted,recipe in recipes.items():full[omitted]=sum((q*full[j]for j,q in recipe.items()),F(0))
    row=dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,X=7,assignment=[2*n+1 for n in range(1,28)],layout=dict(n_variables=1957),entries=[dict(index=i,coefficient=str(q))for i,q in enumerate(full)if q],zero_coordinates=[i for i,q in enumerate(full)if not q],rhs='0'if kind=='redundant'else'1')
    return dict(original=original),projection,tape,dict(complete=True,candidate_original_vector=['0']*1957),row

class FeedbackCheckerTests(unittest.TestCase):
    def test_all_cases_full_replay_and_hash_free_verified_chart(self):
        for kind in ('independent','redundant','inconsistent'):
            inputs=fixture(kind)
            with patch.object(hashlib,'sha256',side_effect=AssertionError('nohash')):
                chart,r=P.build(*inputs,deadline=time.monotonic()+30);self.assertTrue(r['complete'],r.get('reason'));check=C.verify_feedback(*inputs,chart,r)
            self.assertEqual(check['classification'],kind);self.assertTrue(check['all_original_rows_replayed']);self.assertEqual(check['augmented_rank'],779 if kind=='redundant'else 780)
            if kind=='inconsistent':self.assertFalse(check['normalized_chart_verified']);self.assertIsNone(check['new_free_count'])
            else:self.assertTrue(check['candidate_equations_verified']);self.assertTrue(check['finite_candidate_feasible']);self.assertEqual(len(chart['free_indices']),445 if kind=='redundant'else 444)
    def test_leading_free_does_not_stop_later_old_pivot(self):
        b=C.Budget(time.monotonic()+10);basis={3:{3:F(1),4:F(2)},1:{1:F(1),3:F(5)}}
        classification,new,reduction=C.reduce_feedback([F(1),F(2),F(0),F(11),F(0)],F(7),basis,b)
        self.assertEqual(classification,'independent');self.assertEqual(reduction['multipliers'],[[1,'2'],[3,'1']]);self.assertNotIn(3,new);self.assertEqual(new[4],-2);self.assertEqual(new[5],7)
        self.assertEqual(C.backsubstitute({**basis,0:new},[F(0)]*5,b),[F(7),F(0),F(0),F(0),F(0)])
    def test_tampered_source_tape_row_chart_and_candidate_rejected(self):
        inputs=fixture();chart,r=P.build(*inputs,deadline=time.monotonic()+30)
        for mode in ('source','tape','omitted_rhs','row','chart','candidate','flags'):
            bad=list(copy.deepcopy(inputs));ch=copy.deepcopy(chart);rc=copy.deepcopy(r)
            if mode=='source':bad[0]['original']['columns'][367]=[]
            elif mode=='tape':bad[2]['transcript'][0]['normalization']='2'
            elif mode=='omitted_rhs':bad[0]['original']['rhs'][-1]='1'
            elif mode=='row':bad[4]['entries'][1]['coefficient']='2'
            elif mode=='chart':ch['free_indices'].append(800)
            elif mode=='candidate':rc['candidate_original_vector'][0]='1'
            else:rc['global_bound_proved']=True
            with self.assertRaises(ValueError):C.verify_feedback(*bad,ch,rc)
    def test_psd_zero_pivot_negative_witness_and_strict_caps(self):
        b=C.Budget(time.monotonic()+10);r=C.exact_psd([[F(0),F(1)],[F(1),F(0)]],b);self.assertFalse(r['psd']);v=list(map(F,r['witness']));self.assertLess(2*v[0]*v[1],0)
        self.assertTrue(C.exact_psd([[F(0),F(0)],[F(0),F(1)]],b)['psd'])
        with self.assertRaises(ValueError):C.Budget(float('nan'))
        with self.assertRaises(ValueError):C.Budget(time.monotonic()+1,max_operations=True)
        with self.assertRaises(OverflowError):C.Budget(time.monotonic()+1).rational(str(1<<4096))
        inputs=fixture();chart,r=P.build(*inputs,deadline=time.monotonic()+30)
        with self.assertRaises(OverflowError):C.verify_feedback(*inputs,chart,r,max_operations=1)

if __name__=='__main__':unittest.main()
