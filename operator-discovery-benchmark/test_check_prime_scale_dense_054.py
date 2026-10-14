"""Tiny synthetic NEW-witness/source admission tests; no saved arrays/studies."""
import copy
from fractions import Fraction as Q
import unittest
import numpy as np
import check_prime_scale_dense_054 as C
import prime_scale_dense_054 as P
import prime_scale_source_053 as SOURCE
from prime_bank_candidates import Meter as PipelineMeter

M=C.Meter(cap=50000000,seconds=180)
PM=P.Meter(cap=50000000,seconds=180)
SM=SOURCE.Meter(cap=50000000,seconds=180)
DENSE={}


def dense(alpha='1/2',max_n=16):
    key=(alpha,max_n)
    if key not in DENSE:
        s=SOURCE.make_source(alpha,max_n,bits=32,meter=SM)
        fields={k:getattr(s,k) for k in ('alpha','max_n','bits','mu','prefix_w','prefix_up','prefix_down')}
        fields['metadata']=s.metadata();DENSE[key]=P.dense_source(fields,PM)
    return DENSE[key]


def request(alpha='1/2',cs=None):
    return {'alpha':alpha,'q':2,'coefficients':[-2,-39,20] if cs is None else cs,
        'bound':{'C':'2','log_power':'0','minimum':2,'normalization':'divide_by_alpha'}}


def candidate_witness(r,N=2,max_n=16):
    d=dense(r['alpha'],max_n)
    center,lo,hi,rows=P._filter_interval(r,d,N,PM,include_rows=True)
    a=Q(r['alpha']);lower_abs=0 if lo<=0<=hi else min(abs(lo),abs(hi))
    return {'schema':'prime-scale-dense-counterexample-v1','id':'synthetic_dense',
        'request':copy.deepcopy(r),'N':N,'source_max_n':max_n,
        'source_support_used':r['q']**(len(r['coefficients'])-1)*N,
        'dyadic_bits':32,'denominator':1<<32,'term_rows':rows,
        'Tcenter':center,'Tlower':lo,'Tupper':hi,'lower_abs_numerator':lower_abs,
        'comparison':{'left':lower_abs**2*a.denominator**2,
            'right':4*N*a.numerator**2*(1<<64),'relation':'>',
            'formula':'lower_abs^2*alpha_den^2 > 4*N*alpha_num^2*2^(2*bits)'},
        'source_chain_replayed_here':False,'all_scale':False,'float_or_root_comparison_used':False}


def fixture():
    r=request();w=P.first_counterexample({'id':'synthetic_dense','request':r},dense(),[],PM)['first_counterexample']
    if w is None:raise AssertionError('registered synthetic witness absent')
    return r,w


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_prime_scale_dense_054 operations='+str(M.operations+PM.operations+SM.operations))


class DenseWitnessTests(unittest.TestCase):
    def bad(self,mutate):
        r,w=fixture();mutate(r,w)
        with self.assertRaises((ValueError,OverflowError)):C.verify_witness(r,w,M)

    def test_independent_actual_atom_admission(self):
        r,w=fixture();v=C.verify_witness(r,w,M)
        self.assertTrue(v['verified']);self.assertEqual(v['status'],'FINITE_REFUTATION')
        self.assertTrue(v['registered_uniform_bound_refuted']);self.assertFalse(v['RH_refuted'])
        self.assertEqual(v['request'],r);self.assertEqual(v['N'],w['N'])

    def test_source_availability_not_authority(self):
        r,w=fixture();v=C.verify_witness(r,w,M)
        self.assertEqual(v['checked_source_max_n'],8)
        self.assertEqual(v['producer_source_availability'],16)
        self.assertFalse(v['unused_source_indices_verified'])

    def test_context_incremental_new_audit_cache(self):
        r=request();ctx=C.prepare_context(M)
        first=C.verify_witness(r,candidate_witness(r,N=2),M,ctx)
        second=C.verify_witness(r,candidate_witness(r,N=3),M,ctx)
        third=C.verify_witness(r,candidate_witness(r,N=2),M,ctx)
        self.assertGreater(first['source_reconstruction']['new_atoms'],0)
        self.assertEqual(second['source_reconstruction']['reused_verified_through'],8)
        self.assertGreater(second['source_reconstruction']['new_atoms'],0)
        self.assertEqual(third['source_reconstruction']['new_atoms'],0)
        self.assertEqual(third['source_reconstruction']['reused_verified_through'],12)

    def test_arbitrary_fractional_denominator(self):
        for alpha in ['1/257','256/257']:
            r=request(alpha);w=candidate_witness(r)
            self.assertTrue(C.verify_witness(r,w,M)['verified'])

    def test_external_verified_flag_or_dataclass_not_authority(self):
        r,w=fixture()
        fake=C.VALUES.VerifiedSource('1/2',8,32,np.ones(9,dtype=np.int64),
            np.zeros(9,dtype=np.int64),{'verified':True})
        for ctx in [fake,{},C._Context()]:
            with self.assertRaises(ValueError):C.verify_witness(r,w,M,ctx)

    def test_drop_or_forge_divisor_source_atom(self):
        self.bad(lambda r,w:w['term_rows'][2].update(Acenter=w['term_rows'][2]['Acenter']+1))
        self.bad(lambda r,w:w['term_rows'][2].update(Adown=0))
        self.bad(lambda r,w:w['term_rows'][2].update(Aup=0))

    def test_unit_and_complete_support(self):
        self.bad(lambda r,w:w.update(source_support_used=7))
        self.bad(lambda r,w:w.update(source_max_n=7))
        self.bad(lambda r,w:w['term_rows'][0].update(Adown=w['term_rows'][0]['Adown']+w['N']))
        self.bad(lambda r,w:w['term_rows'].pop())

    def test_raw_term_endpoint_and_signed_crosses(self):
        self.bad(lambda r,w:w['term_rows'][1].update(lower_numerator=
            w['term_rows'][1]['coefficient']*w['term_rows'][1]['lower_numerator']))
        self.bad(lambda r,w:w.update(Tlower=sum(row['lower_numerator'] for row in w['term_rows'])))
        self.bad(lambda r,w:w.update(Tcenter=-w['Tcenter']))

    def test_wrong_rounding_lattice(self):
        self.bad(lambda r,w:w.update(dyadic_bits=31))
        self.bad(lambda r,w:w.update(denominator=(1<<32)+1))
        self.bad(lambda r,w:w.update(Tupper=w['Tupper']+1))

    def test_exact_square_and_normalization(self):
        self.bad(lambda r,w:w['comparison'].update(left=w['comparison']['left']+1))
        self.bad(lambda r,w:w['comparison'].update(right=w['comparison']['right']-1))
        self.bad(lambda r,w:w['comparison'].update(relation='>='))
        self.bad(lambda r,w:r['bound'].update(normalization='none'))

    def test_finite_pass_not_a_counterexample(self):
        r=request(cs=[-2,1]);w=candidate_witness(r)
        self.assertLessEqual(w['comparison']['left'],w['comparison']['right'])
        with self.assertRaises(ValueError):C.verify_witness(r,w,M)

    def test_request_and_index_binding(self):
        self.bad(lambda r,w:w['request'].update(alpha='1/3'))
        self.bad(lambda r,w:w.update(N=True))
        self.bad(lambda r,w:w['term_rows'][1].update(scale=5))
        self.bad(lambda r,w:w['term_rows'][1].update(j=2))

    def test_actual_parent_scope_only(self):
        self.bad(lambda r,w:r['bound'].update(C='1'))
        self.bad(lambda r,w:r['bound'].update(log_power='1/3'))
        self.bad(lambda r,w:r['bound'].update(minimum=3))
        self.bad(lambda r,w:r.update(coefficients=[1]))
        self.bad(lambda r,w:r.update(coefficients=[-3,1]))

    def test_typed_flags_and_no_rh_claim(self):
        for flag in ['source_chain_replayed_here','all_scale','float_or_root_comparison_used']:
            self.bad(lambda r,w,flag=flag:w.update({flag:True}))
        self.bad(lambda r,w:w['term_rows'][0].update(j=False))
        self.bad(lambda r,w:w.update(RH_refuted=True))

    def test_prospective_coverage_and_work_guards(self):
        self.bad(lambda r,w:w.update(source_max_n=C.MAX_N+1))
        r,w=fixture()
        with self.assertRaises(OverflowError):C.verify_witness(r,w,C.Meter(cap=1))
        large=request(cs=[-64,1]+[0]*13+[-64,1]);large['q']=64
        # Unsupported gigantic needed coverage is rejected before allocation.
        bad=copy.deepcopy(w);bad['request']=large;bad['source_max_n']=C.MAX_N
        with self.assertRaises(ValueError):C.verify_witness(large,bad,M)

    def test_charge_only_pipeline_meter(self):
        r,w=fixture();meter=PipelineMeter(cap=10000000,seconds=30)
        self.assertTrue(C.verify_witness(r,w,meter)['verified']);M.charge(meter.operations)

    def test_ordinary_mu_and_full_floor_identity(self):
        # A fresh tiny source is independently divisor-recursive; p^2 and
        # squarefree composite indices have their proper signed roles.
        r,w=fixture();ctx=C.prepare_context(M);v=C.verify_witness(r,w,M,ctx)
        s=C._CONTEXTS[ctx]['1/2']
        self.assertEqual([int(s.mu[n]) for n in [1,2,4,6,8]],[1,-1,0,1,0])
        for n in range(1,9):
            self.assertEqual(sum(int(s.mu[d]) for d in range(1,n+1) if n%d==0),int(n==1));M.charge(n)
        self.assertTrue(v['old_atoms_may_overlap_new_witness_reconstruction'])

    def test_unnormalized_source_interval_divided_by_alpha(self):
        r,w=fixture();v=C.verify_witness(r,w,M)
        lo=Q(w['Tlower'],w['denominator'])/Q(r['alpha'])
        hi=Q(w['Tupper'],w['denominator'])/Q(r['alpha'])
        self.assertEqual(v['normalized_source_interval'],{'lower':str(lo),'upper':str(hi)})
        self.assertGreater(min(abs(lo),abs(hi))**2,4*w['N'])


if __name__=='__main__':unittest.main()
