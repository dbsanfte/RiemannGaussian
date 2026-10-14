import copy
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import check_primitive_state_chart_dual_search as C
import primitive_state_chart_dual_search as P


def fixture():
    pivots=list(range(782));rows=[dict(pivot=p,terms=[[p,'1']]+([[1224,'-1']]if p==0 else[]))for p in pivots]
    chart=dict(schema='primitive-state-augmented-cone-chart-v1',complete=True,width=1224,original_width=1957,retained_indices=C.retained_indices(),normalized_rows=rows,pivot_columns=pivots,free_indices=list(range(782,1224)),old_pivots=[p for p in pivots if p not in(160,170)])
    review=dict(schema='primitive-state-augmented-cone-search-independent-review-v1',all_passed=True,chart_verified=True,center_verified=True,status='SCALAR_REJECTED',independent_search_check=dict(verified=True,chart_verified=True,center_verified=True,chart_used_without_old_tape_replay=True))
    records=C.fixed_descriptions()
    for block in('C','H'):
        for i in range(15):
            vector=['0']*15;vector[i]='1';records.append(dict(index=len(records),kind='rank_one',block=block,vector=vector,origin='endpoint_eigenvector'))
    rays=dict(schema=C.RAYS_SCHEMA,complete=True,width=1224,retained_indices=C.retained_indices(),scalar_projected_indices=C.SCALAR_INDICES,C_projected_indices=C.C_INDICES,P_projected_indices=C.P_INDICES,records=records)
    alpha=['0']*851;alpha[0]='1';lam=['0']*782;lam[0]='1';functional=['0']*1224;functional[0]='1'
    certificate=dict(schema=C.CERTIFICATE_SCHEMA,complete=True,width=1224,pivot_columns=pivots,free_indices=chart['free_indices'],rays=rays,alpha=alpha,lambda_vector=lam,pairing='-1',combined_functional=functional,exact_identity_verified=True,**C.FLAGS)
    return chart,review,certificate


class Tests(unittest.TestCase):
    def check(self,args=None,**kwargs):return C.verify_certificate(*(args or fixture()),deadline=time.monotonic()+30,**kwargs)
    def test_full_exact_scalar_separator_and_no_hashes(self):
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):result=self.check()
        self.assertTrue(result['verified']);self.assertTrue(result['finite_augmented_cone_infeasibility_certified']);self.assertEqual(result['generator_count'],851);self.assertEqual(result['active_generators'],1);self.assertEqual(result['pairing'],'-1');self.assertFalse(result['RH_proved']);self.assertFalse(result['original_unlearned_cone_infeasibility_certified']);self.assertFalse(result['native_LP_replayed'])
    def test_authentic_producer_exact_certificate(self):
        chart,review,certificate=fixture();rows={r['pivot']:{j:F(q)for j,q in r['terms']}for r in chart['normalized_rows']};b=P.Budget(time.monotonic()+30,60000000)
        proposed=P.certify(rows,1224,chart['free_indices'],chart['retained_indices'],certificate['rays'],[F(q)for q in certificate['alpha']],b)
        result=self.check((chart,review,proposed));self.assertTrue(result['all_coordinate_equalities_verified'])
    def test_full_weight_vectors_required_and_negative_alpha_rejected(self):
        for key in('alpha','lambda_vector'):
            args=fixture();args[2][key].pop()
            with self.assertRaises(ValueError):self.check(args)
        args=fixture();args[2]['alpha'][1]='-1'
        with self.assertRaises(ValueError):self.check(args)
    def test_pairing_functional_and_lambda_tamper(self):
        for key,value in [('pairing','1'),('lambda_vector',['0']*782),('combined_functional',['0']*1224)]:
            args=fixture();args[2][key]=value
            with self.assertRaises(ValueError):self.check(args)
    def test_parent_premise_and_missing_chart_row_rejected(self):
        args=fixture();args[1]['chart_verified']=False
        with self.assertRaises(ValueError):self.check(args)
        args=fixture();args[0]['normalized_rows'].pop()
        with self.assertRaises(ValueError):self.check(args)
        args=fixture();args[0]['normalized_rows'][2]['terms'].append([1,'1'])
        with self.assertRaises(ValueError):self.check(args)
    def test_fixed_catalog_coverage_and_relation_ray_rejected(self):
        args=fixture();args[2]['rays']['records'][0]['coordinate']=366
        with self.assertRaises(ValueError):self.check(args)
        args=fixture();args[2]['rays']['records'][400],args[2]['rays']['records'][401]=args[2]['rays']['records'][401],args[2]['rays']['records'][400]
        with self.assertRaises(ValueError):self.check(args)
        args=fixture();args[2]['rays']['records'].pop()
        with self.assertRaises(ValueError):self.check(args)
    def test_arbitrary_extra_dyadic_rank_one_not_eigen_proof(self):
        args=fixture();v=args[2]['rays']['records'][821]['vector'];v[0]='1/2';v[1]='-1/4'
        result=self.check(args);self.assertFalse(result['native_eigenvectors_independently_verified'])
        for value in('1/3','2','-1'):
            bad=copy.deepcopy(args);bad[2]['rays']['records'][821]['vector'][0]=value
            with self.assertRaises(ValueError):self.check(bad)
        bad=copy.deepcopy(args);bad[2]['rays']['records'][821]['vector']=['0']*15
        with self.assertRaises(ValueError):self.check(bad)
    def test_exact_rank_one_quadratic_identity_and_offdiagonal_two(self):
        b=C.Budget(time.monotonic()+30);v=[F(0)]*15;v[0]=F(2);v[1]=F(-3);u=[F(i-2,7)for i in range(15)]
        ray=dict(index=0,kind='rank_one',block='C',vector=list(map(str,v)),origin='toy');row=C.generator(ray,b)
        self.assertEqual(row[C.C_INDICES[1]],F(-12));q=sum(row.get(C.C_INDICES[k],F(0))*u[i]*u[j]for k,(i,j)in enumerate(C.PAIRS));self.assertEqual(q,sum(x*y for x,y in zip(u,v))**2)
        self.assertTrue(all(j not in row for j in range(366,979)))
    def test_H_storage_sign_and_parent_negative_counterexample(self):
        b=C.Budget(time.monotonic()+30);v=['1']+['0']*14;ray=dict(index=0,kind='rank_one',block='H',vector=v,origin='toy');row=C.generator(ray,b)
        self.assertEqual(row,{984:F(4),1104:F(1)})
        # C11=1,P11=-1 gives H11=3: negative P alone is not infeasibility.
        self.assertEqual(row[984]*1+row[1104]*(-1),3)
        with self.assertRaises(ValueError):C.check_identity([{1104:F(1),1224:F(-1)}],[row],['1'],['1'],1224,b)
    def test_signed_beta_is_not_a_nonnegative_quotient_coordinate(self):
        b=C.Budget(time.monotonic()+30)
        with self.assertRaises(ValueError):C.generator(dict(index=0,kind='scalar',coordinate=366),b)
        with self.assertRaises(ValueError):C.check_identity([{366:F(1),1224:F(-1)}],[{0:F(1)}],['1'],['1'],1224,b)
    def test_scope_and_noncertified_LP_never_promote(self):
        chart,review,_=fixture();out=dict(status='NONCERTIFIED',certificate=None,native=dict(status='optimal'),**C.FLAGS)
        result=C.verify_outcome(chart,review,out,deadline=time.monotonic()+30);self.assertFalse(result['complete']);self.assertFalse(result['finite_augmented_cone_infeasibility_certified']);self.assertFalse(result['primal_feasibility_certified'])
        with self.assertRaises(OverflowError)as caught:C.verify_outcome(chart,review,out,max_operations=1)
        self.assertIsNotNone(caught.exception.independent_audit_counts)
        out['finite_cone_infeasibility_verified']=True
        with self.assertRaises(ValueError):C.verify_outcome(chart,review,out)
        args=fixture();args[2]['RH_proved']=True
        with self.assertRaises(ValueError):self.check(args)
    def test_rational_byte_deadline_and_shared_work_caps(self):
        with self.assertRaises(OverflowError)as captured:self.check(max_operations=20)
        self.assertIsNotNone(captured.exception.independent_audit_counts);self.assertLessEqual(captured.exception.independent_audit_counts['operations'],20)
        with self.assertRaises(OverflowError):self.check(max_certificate_bytes=20)
        args=fixture();args[2]['alpha'][0]=str(1<<4096)
        with self.assertRaises(OverflowError):self.check(args)
        args=fixture();args[2]['alpha'][0]='01'
        with self.assertRaises(ValueError):self.check(args)
        with self.assertRaises(ValueError):C.Budget(float('nan'))
        with self.assertRaises(TimeoutError):C.verify_certificate(*fixture(),deadline=time.monotonic()-1)

if __name__=='__main__':unittest.main()
