"""Synthetic integration checks; no source files, actual LP or eigenvectors.

The required catalog and chart dimensions use unit rows and axis endpoints.
Only a few scalar affine forms are nontrivial. Native support is simulated;
geometry discovery and exact support restoration use the authentic producer.
"""
import copy
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch

import check_primitive_state_chart_dual_geometry_search as C
import primitive_state_chart_dual_geometry_search as P


def fixture(compressed=False):
    direct=C.DIRECT
    # Two matrix diagonal unit equations give genuine conditional kernel faces.
    pivots=[*range(780),984,1104]
    rows={p:{p:F(1)} for p in pivots}
    rows[0][1224]=F(-1) if compressed else F(-2)
    if compressed:
        rows[0][782]=F(1)       # s0=-x-1
        rows[1][782]=F(-1)      # s1=x
        rows[2].update({782:F(2),1224:F(-1)})  # s2=-2x-1
    rows[3][782]=F(-2)          # duplicate positive line s3=2x
    rows[4][782]=F(1)           # opposite line s4=-x
    free=[j for j in range(1224) if j not in pivots]
    chart=dict(schema='primitive-state-augmented-cone-chart-v1',complete=True,
               width=1224,original_width=1957,retained_indices=direct.retained_indices(),
               normalized_rows=[dict(pivot=p,terms=[[j,str(q)] for j,q in sorted(rows[p].items())]) for p in pivots],
               pivot_columns=pivots,free_indices=free,
               old_pivots=[p for p in pivots if p not in (160,170)])
    review=dict(schema='primitive-state-augmented-cone-search-independent-review-v1',
                all_passed=True,chart_verified=True,center_verified=True,status='SCALAR_REJECTED',
                independent_search_check=dict(verified=True,chart_verified=True,
                    center_verified=True,chart_used_without_old_tape_replay=True))
    records=direct.fixed_descriptions()
    for block in ('C','H'):
        for j in range(15):
            vector=['0']*15;vector[j]='1'
            records.append(dict(index=len(records),kind='rank_one',block=block,
                                vector=vector,origin='endpoint_eigenvector'))
    rays=dict(schema=direct.RAYS_SCHEMA,complete=True,width=1224,
              retained_indices=direct.retained_indices(),scalar_projected_indices=direct.SCALAR_INDICES,
              C_projected_indices=direct.C_INDICES,P_projected_indices=direct.P_INDICES,records=records)
    saved=[]
    def native(columns,rhs,row_keys,**kwargs):
        # The first three retained columns are precisely the scalar toy system.
        vector=[0.0]*len(columns);vector[:3]=[1.0,1.0,1e-300]
        return dict(attempted=True,success=True,status=0,scaled_vector=vector,counts={})
    with patch.object(P,'native_proposal',side_effect=native if compressed else AssertionError('singleton needs no LP')):
        outcome=P.search(chart,rays,deadline=time.monotonic()+30,save_geometry=saved.append)
    if outcome['status']!='CERTIFICATE_PROPOSED':raise AssertionError(outcome)
    return chart,review,rays,saved[0],outcome


class Integration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.direct=fixture();cls.compressed=fixture(True)
        cls.audit_instances=[]
        cls.producer_operations=sum(sum(v.get('operations',0) for v in args[4]['stage_counts'].values())
                                    for args in (cls.direct,cls.compressed))
        cls.geometry_checks={}
        for args in (cls.direct,cls.compressed):
            budget=C.Budget(time.monotonic()+30);cls.audit_instances.append(budget)
            cls.geometry_checks[args[4]['route']]=C.verify_geometry(*args[:4],budget)

    @classmethod
    def tearDownClass(cls):
        operations=cls.producer_operations+sum(b.operations for b in cls.audit_instances)
        # This module plus producer and small workflow checks must fit the
        # final combined suite's 15m reservation within 65m total preparation.
        if operations>7000000:raise AssertionError('synthetic checker module reserve exhausted')
        print('Synthetic geometry checker work: producer=%d independent=%d total=%d' %
              (cls.producer_operations,sum(b.operations for b in cls.audit_instances),operations))

    def check(self,args=None,*,full=False,**kwargs):
        original=C.Budget
        def tracked(*args,**kw):
            budget=original(*args,**kw);self.audit_instances.append(budget);return budget
        kwargs.setdefault('deadline',time.monotonic()+30)
        args=args if args is not None else self.direct
        # Most tampering here concerns the outcome/certificate handoff. Reuse
        # geometry independently checked above; the two authentic integration
        # tests and geometry tamper tests exercise the complete path separately.
        geometry=C.verify_geometry if full else lambda *a,**k:copy.deepcopy(
            self.geometry_checks['negative_constant_ray' if args[3]['negative_constant_ray'] is not None else 'compressed_lp'])
        with patch.object(C,'Budget',side_effect=tracked), \
             patch.object(C,'verify_geometry',side_effect=geometry), \
             patch.object(P,'geometry',side_effect=AssertionError('independent composition')), \
             patch.object(P.P,'certify',side_effect=AssertionError('independent identity')), \
             patch.object(P,'native_proposal',side_effect=AssertionError('no LP replay')):
            return C.verify_outcome(*args,**kwargs)

    def assert_rejected(self,args,**kwargs):
        with self.assertRaises(ValueError):self.check(args,**kwargs)

    def test_authentic_singleton_separator_and_conditional_faces(self):
        result=self.check(full=True)
        self.assertEqual(result['status'],'FINITE_CONE_INFEASIBLE')
        self.assertTrue(result['certificate_verified'])
        self.assertTrue(result['all_affine_forms_verified'])
        self.assertTrue(result['all_generator_responses_verified'])
        self.assertTrue(result['exact_compression_verified'])
        self.assertEqual(result['negative_constant_ray'],0)
        self.assertEqual(result['certificate_check']['active_generators'],1)
        self.assertEqual(self.direct[4]['certificate']['alpha'][0],'1/2')
        self.assertEqual(result['remaining_matrix_dimensions'],dict(C=14,H=14))
        self.assertTrue(result['conditional_faces_only'])
        self.assertFalse(result['primal_feasibility_certified'])
        self.assertFalse(result['certificate_check']['original_unlearned_cone_infeasibility_certified'])
        self.assertFalse(result['RH_proved'])
        self.assertFalse(result['native_LP_replayed'])
        self.assertEqual(result['audit_operations'],result['independent_audit_work_reserve'])

    def test_authentic_compressed_support_and_zero_free_restoration(self):
        args=self.compressed;result=self.check(args,full=True)
        self.assertIsNone(result['negative_constant_ray'])
        self.assertEqual(args[4]['restoration_stats'],dict(support=[0,1,2],support_size=3,
            rank=2,free_support_coordinates=[2],free_rule='zero',complete=True))
        self.assertEqual(args[4]['certificate']['alpha'][:3],['1','1','0'])
        self.assertEqual(result['certificate_check']['active_generators'],2)
        self.assertTrue(result['finite_augmented_cone_infeasibility_certified'])
        # Even a tiny strictly positive native value contributes to the support.
        self.assertEqual(args[4]['native']['scaled_vector'][2],1e-300)

    def test_noncertified_and_unknown_keep_verified_geometry_only(self):
        for status in ('NONCERTIFIED','UNKNOWN'):
            args=copy.deepcopy(self.compressed);args[4].update(status=status,certificate=None)
            result=self.check(args)
            self.assertEqual(result['status'],status)
            self.assertTrue(result['geometry_verified'])
            self.assertFalse(result['certificate_verified'])
            self.assertFalse(result['finite_augmented_cone_infeasibility_certified'])
            self.assertIsNone(result['certificate_check'])
        args=copy.deepcopy(self.direct);args[4]['status']='NONCERTIFIED';self.assert_rejected(args)

    def test_affine_constants_free_units_and_complete_numbering(self):
        for mutate in (
            lambda g:g['forms'][0].update(constant='-1'),
            lambda g:g['forms'][782].update(terms=[]),
        ):
            args=copy.deepcopy(self.direct);mutate(args[3]);self.assert_rejected(args,full=True)

    def test_composed_responses_cannot_be_omitted_or_changed(self):
        for mutate in (
            lambda g:g['responses'][0].update(terms=[[1224,'-1']]),
        ):
            args=copy.deepcopy(self.direct);mutate(args[3]);self.assert_rejected(args,full=True)

    def test_complete_zero_signed_line_and_exposure_records(self):
        for mutate in (
            lambda g:g['exposures'][0]['combination'][0].update(weight='-1'),
        ):
            args=copy.deepcopy(self.direct);mutate(args[3]);self.assert_rejected(args,full=True)

    def test_positive_column_and_augmented_row_compression_receipts(self):
        for mutate in (
            lambda g:g['compression']['column_map'][3].update(positive_factor='-2'),
        ):
            args=copy.deepcopy(self.compressed);mutate(args[3]);self.assert_rejected(args,full=True)

    def test_kernel_span_scalar_faces_and_shortcut_metadata(self):
        for mutate in (
            lambda g:g['kernel_spans'][0]['basis_vectors'][0].__setitem__(0,'0'),
        ):
            args=copy.deepcopy(self.direct);mutate(args[3]);self.assert_rejected(args,full=True)

    def test_certificate_full_identity_weights_and_pairing(self):
        for mutate in (
            lambda c:c['alpha'].pop(),
            lambda c:c['alpha'].__setitem__(0,'-1/2'),
            lambda c:c['lambda_vector'].__setitem__(0,'0'),
            lambda c:c['combined_functional'].__setitem__(1223,'1'),
        ):
            args=copy.deepcopy(self.direct);mutate(args[4]['certificate']);self.assert_rejected(args)

    def test_certificate_saved_rays_and_partition_are_bound(self):
        for mutate in (
            lambda c:c['rays']['records'][821]['vector'].__setitem__(0,'1/2'),
        ):
            # Certificate and separately saved rays share an object in the
            # producer. Break that alias before testing binding tampering.
            args=copy.deepcopy(self.direct);args[4]['certificate']=copy.deepcopy(args[4]['certificate'])
            mutate(args[4]['certificate']);self.assert_rejected(args)

    def test_chart_premise_catalog_and_geometry_scope_are_required(self):
        args=copy.deepcopy(self.direct);args[1]['chart_verified']=False;self.assert_rejected(args,full=True)
        args=copy.deepcopy(self.direct);args[3]['policy']['exposure_scope']='feasibility proved';self.assert_rejected(args,full=True)

    def test_exact_shortcut_route_is_deterministic(self):
        for mutate in (
            lambda o:o.update(route='compressed_lp'),
        ):
            args=copy.deepcopy(self.direct);mutate(args[4]);self.assert_rejected(args)

    def test_compressed_route_and_successful_finite_native_vector_required(self):
        for mutate in (
            lambda o:o['native'].update(success=False),
            lambda o:o['native']['scaled_vector'].__setitem__(0,True),
        ):
            args=copy.deepcopy(self.compressed);mutate(args[4]);self.assert_rejected(args)

    def test_all_positive_native_support_and_restoration_metadata_bound(self):
        for mutate in (
            lambda o:o['restoration_stats'].update(support=[0,1],support_size=2),
            lambda o:o['restoration_stats'].update(free_support_coordinates=[0]),
            lambda o:o['native']['scaled_vector'].__setitem__(0,0.0),
        ):
            args=copy.deepcopy(self.compressed);mutate(args[4]);self.assert_rejected(args)

    def test_valid_exact_separator_still_requires_representative_only_lift(self):
        args=copy.deepcopy(self.compressed)
        # s3=2*s1, so moving its weight preserves the entire exact separator.
        certificate=args[4]['certificate'];certificate['alpha'][1]='0';certificate['alpha'][3]='1/2'
        certificate['lambda_vector'][1]='0';certificate['lambda_vector'][3]='1/2'
        certificate['combined_functional'][1]='0';certificate['combined_functional'][3]='1/2'
        with self.assertRaisesRegex(ValueError,'representative-only'):
            self.check(args)

    def test_scope_claims_and_producer_preadmission_are_rejected(self):
        for artifact_index in (3,):
            args=copy.deepcopy(self.direct);args[artifact_index]['RH_proved']=True;self.assert_rejected(args,full=True)
        for flag in ('finite_augmented_cone_infeasibility_certified','primal_feasibility_certified'):
            args=copy.deepcopy(self.direct);args[4][flag]=True;self.assert_rejected(args)

    def test_one_shared_audit_includes_geometry_and_separator(self):
        geometry_only=copy.deepcopy(self.direct);geometry_only[4].update(status='NONCERTIFIED',certificate=None)
        geometry=self.check(geometry_only,full=True);complete=self.check(full=True)
        self.assertGreater(complete['audit_operations'],geometry['audit_operations'])
        with self.assertRaises(OverflowError) as caught:
            self.check(full=True,max_operations=geometry['audit_operations'])
        counts=caught.exception.independent_audit_counts
        self.assertLessEqual(counts['operations'],geometry['audit_operations'])
        self.assertGreater(counts['operations'],geometry['audit_operations']-1000)

    def test_byte_rational_live_cell_and_deadline_caps_fail_closed(self):
        for kwargs,error in (
            (dict(max_operations=20),OverflowError),
            (dict(max_geometry_bytes=20),OverflowError),
            (dict(max_certificate_bytes=20),OverflowError),
            (dict(max_cells=1),OverflowError),
            (dict(deadline=time.monotonic()-1),TimeoutError),
        ):
            with self.assertRaises(error) as caught:self.check(full=True,**kwargs)
            self.assertIn('operations',caught.exception.independent_audit_counts)
        args=copy.deepcopy(self.direct);args[3]['forms'][0]['constant']=str(1<<4096)
        with self.assertRaises(OverflowError):self.check(args,full=True)
        args=copy.deepcopy(self.direct);args[4]['certificate']['alpha'][0]='01';self.assert_rejected(args)
        with self.assertRaises(ValueError):C.Budget(time.monotonic()+30,max_operations=70000001)


if __name__=='__main__':unittest.main()
