import copy
from fractions import Fraction as Q
import unittest
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

import mobius_residual_fold_077 as P
import check_mobius_residual_fold_077 as C


class Fold(unittest.TestCase):
    def test_large_horizon_interval_identity_without_expansion(self):
        components=[dict(parent=16_000_000,weight={'1':'1'}),dict(parent=8_000_000,weight={'t':'-2/7'})]
        intervals=P.OLD.stencil_intervals(components)
        checked=C.verify_stencil(components,intervals)
        self.assertEqual(checked['status'],'VERIFIED_IDENTITY',checked)
        self.assertLess(len(intervals),12)
        after=P.fold_intervals(intervals,3)
        self.assertEqual(C.verify_fold(intervals,after,3)['status'],'VERIFIED_IDENTITY')
        self.assertLess(len(after),30)
        self.assertLess(checked['peak_bytes'],16*1024**2)

    def test_interval_fold_matches_sparse_reference_on_restricted_domain(self):
        intervals=[dict(left=0,right=19,weight={'x':'1/3'}),dict(left=21,right=60,weight={'x':'-4/7','y':'2'})]
        sparse=P.OLD.materialize(intervals)
        prior=[]
        for p in [2,5,3]:
            before=intervals;intervals=P.fold_intervals(intervals,p,prior)
            self.assertEqual(C.verify_fold(before,intervals,p,prior)['status'],'VERIFIED_IDENTITY')
            sparse=P.OLD.fold(sparse,p,prior);prior.append(p)
            literal=P.OLD.materialize(intervals)
            literal={n:w for n,w in literal.items() if all(n%r for r in prior)}
            self.assertEqual(literal,sparse)
        tokens={'x':['-1/5','1/7'],'y':['2/3','2/3']}
        own=P.bound_intervals(intervals,tokens,prior)
        check=C.bound_intervals(intervals,tokens,prior)
        self.assertEqual(check['status'],'VERIFIED_BOUND',check)
        self.assertEqual(own['upper'],check['l1_upper'])
        self.assertEqual(own['lower'],check['l1_lower'])
        self.assertEqual(Q(own['upper']),P.OLD.coefficient_bound(sparse,tokens))

    def test_coprime_count_with_big_products_is_exact(self):
        primes=[2,3,5,101,103]
        for left,right in [(0,0),(0,1),(1,20),(12,150),(400,533)]:
            divisors=P.signed_divisors(tuple(primes),right)
            literal=sum(all(n%p for p in primes) for n in range(left+1,right+1))
            self.assertEqual(P.count_coprime(left,right,divisors),literal)
            self.assertEqual(C.coprime_count(left,right,primes),literal)

    def test_generic_kernel_discovers_verified_uniform_method_obstruction(self):
        cert=P.uniform_obstruction(P.KERNEL,2,[2,3,5,7],'129/128')
        checked=C.verify_bulk_obstruction(P.KERNEL,2,[2,3,5,7],cert)
        self.assertEqual(checked['status'],'VERIFIED_UNIFORM_COEFFICIENT_OBSTRUCTION',checked)
        self.assertEqual((cert['lower'],cert['upper'],cert['coefficient']),('1/5','1/4','-1'))
        self.assertFalse(checked['arithmetic_residual_refuted'])
        self.assertFalse(checked['uniform_source_bound_proved'])
        other=[dict(divisor=3,weight='-2'),dict(divisor=7,weight='1')]
        generic=P.uniform_obstruction(other,2,[11],'33/32')
        self.assertEqual(C.verify_bulk_obstruction(other,2,[11],generic)['status'],'VERIFIED_UNIFORM_COEFFICIENT_OBSTRUCTION')
        bad=dict(cert,A='1')
        self.assertEqual(C.verify_bulk_obstruction(P.KERNEL,2,[2,3,5,7],bad)['status'],'INVALID')

    def test_uniform_density_lower_bound_matches_integer_counts(self):
        primes=[2,3,5];cert=P.uniform_obstruction(P.KERNEL,2,primes,'1')
        for u in [1,19,80,513,4096,cert['threshold_u'],2*cert['threshold_u']]:
            count=C.coprime_count(u//5,u//4,primes)
            self.assertGreaterEqual(Q(count),Q(cert['A'])*u-Q(cert['E']))
            if u>=cert['threshold_u']:self.assertGreaterEqual(Q(count),Q(cert['A'])*u/2)

    def test_compiler_binds_actual_prime_children_and_arbitrary_count_power(self):
        spec=dict(grid=80,theta=['1/2','17/31','7/8'],multipliers=[2,3])
        data=P.S.make_data(spec,[257,800])
        program=dict(spec=spec,atoms=[dict(column=0,gamma='1001/1000'),dict(column=1,gamma='1/3'),dict(column=2,gamma='0')],operator=['2/3','-1/7','1/4'])
        for row in data['rows']:
            compiled=P.compile_row(program,row)
            checked=C.verify_compiled(program,row,compiled['prime_groups'],compiled['compiled'])
            self.assertEqual(checked['status'],'VERIFIED_IDENTITY',checked)
            self.assertTrue(checked['source_data_admission_still_required'])
            self.assertEqual(C.verify_stencil(compiled['compiled']['components'],compiled['intervals'])['status'],'VERIFIED_IDENTITY')
            bad=copy.deepcopy(compiled['compiled']);bad['token_intervals']['1']=['0','0']
            self.assertEqual(C.verify_compiled(program,row,compiled['prime_groups'],bad)['status'],'INVALID')

    def test_search_discovers_operator_free_cancellation_and_preserves_method_scope(self):
        # Full coefficient functions f(1)=f(7)=1 and f(49)=2; actual mu unused.
        intervals=[dict(left=0,right=1,weight={'1':'1'}),dict(left=6,right=7,weight={'1':'1'}),dict(left=48,right=49,weight={'1':'2'})]
        row=dict(u=200,intervals=intervals,compiled=dict(token_intervals={'1':['1','1']}))
        result=P.search_schedules([row],'1',primes=(2,3,7),depth=1,width=2)
        self.assertEqual(result['prime_schedule'],[7])
        self.assertEqual(result['bounds'][0]['upper'],'0')
        self.assertFalse(result['mobius_values_used_for_selection'])
        self.assertFalse(result['uniform_residual_proved'])
        self.assertEqual(C.verify_fold(intervals,result['final_intervals'][0],7)['status'],'VERIFIED_IDENTITY')

    def test_prime_memory_gate_precedes_allocation_and_fraction_bit_gate(self):
        class Tiny:
            ops=0
            def reserve(self,n):raise MemoryError('deliberate prospective gate')
            def charge(self,n):self.ops+=n
        row=dict(u=160,X=40,cuts=[6,25],counts=[6])
        spec=dict(grid=80,theta=['1/2','7/8'],multipliers=[])
        # Correct cutoffs are required before the prospective allocation gate.
        row['cuts']=[P.S.B.floor_power(40,Q(t)) for t in spec['theta']]
        with self.assertRaises(MemoryError):P.prime_groups(row,spec,Tiny())
        with self.assertRaises(ValueError):P.bounded_add(Q(1,(1<<60000)+1),Q(1,(1<<60000)+3),P.S.Meter())

    def test_complete_runner_task_keeps_signed_candidate_and_obstructs_method(self):
        import run_mobius_residual_fold_077 as R
        import check_mobius_prime_moment_075 as SOURCE
        spec=dict(grid=80,theta=['1/2','7/8'],multipliers=[2,3])
        data=P.S.make_data(spec,[320,640]);self.assertEqual(SOURCE.verify_data(data)['status'],'VERIFIED')
        program=dict(spec=spec,atoms=[dict(column=0,gamma='1/2')],operator=['1/8'],q='1',innovation_C='1/100')
        config=dict(R.SPEC,discovery_k=[4],validation_k=[8],phases=[0],primes=[2,3],depth=1,width=1)
        with tempfile.TemporaryDirectory() as tmp,patch.object(R,'OUT',Path(tmp)),patch.object(R,'SPEC',config),patch.object(R,'_ROWS',{r['u']:r for r in data['rows']}):
            result=R.construction_task(dict(id='test',aliases=['test'],program=program))
            self.assertFalse(result['signed_candidate_rejected'])
            self.assertFalse(result['uniform_residual_bound_proved'])
            self.assertEqual(result['rows_checked'],2)
            self.assertEqual(result['uniform_coefficient_obstruction']['status'],'VERIFIED_UNIFORM_COEFFICIENT_OBSTRUCTION')
            saved=json.loads((Path(tmp)/'construction_test.json').read_text())
            self.assertTrue(saved['frozen_before_validation'])
            with self.assertRaises(ValueError):R.bind(program,641,P.S.Meter())

    def test_formula_dedup_keeps_every_original_obligation_id(self):
        import run_mobius_residual_fold_077 as R
        p=dict(q='1',atoms=[],operator=[])
        jobs=R.select_jobs([dict(id='a',program=p),dict(id='b',program=p),dict(id='c',program=dict(p,q='33/32'))])
        self.assertEqual(len(jobs),2)
        self.assertEqual(jobs[0]['aliases'],['a','b'])


if __name__=='__main__':unittest.main()
