import copy
from fractions import Fraction as F
import sys
import time
import unittest
from unittest.mock import patch
import primitive_state_uniform_identity_probe as P


def fixture(X=1):
    """Synthetic complete-layout fixture, not a real arithmetic grammar build."""
    H=4*X-1;L=P.LANGUAGE
    blocks={}
    for name,ts in [('full_child',range(2*X,4*X)),('full_parent',range(X,2*X))]:
        blocks[name]=[[L.dump_poly(L.constant(1)),L.dump_poly(L.add(*(L.variable(n)for n in range(1,t+1))))]+[L.dump_poly(L.constant(0))]*13 for t in ts]
    delta={}
    for name,factor in [('full_child',1),('full_parent',-4)]:
        for row in blocks[name]:delta=L.add(delta,L.scale(L.mul(L.load_poly(row[1]),L.load_poly(row[1])),factor))
    D=32*X*X*(1 if X==1 else 2)
    native=dict(instance=dict(target='mu',horizon=H,lhs=L.dump_poly(L.add(L.constant(D),L.scale(delta,-1))),square_groups=[[]for _ in range(366)],relation_groups=[[]for _ in range(613)]),gram_blocks=blocks,storage_blocks=dict(kind='signed_storage_increment',child=blocks['full_child'],parent=blocks['full_parent'],child_multiplier='1',parent_multiplier='-4'),gram_specs=dict(full_child=15,full_parent=15,storage_K=15),gram_program=P.NATIVE.SPEC,primitive_state_spec=P.NATIVE.SPEC)
    vector=['0']*1957;plan=P.preflight(vector,dict(target='mu',q=6,C='32',claim='critical'),X=X,deadline=time.monotonic()+30)
    return native,vector,plan

class ProbeTests(unittest.TestCase):
    def run_probe(self,native,vector,plan,**limits):return P.probe_native(native,vector,plan,deadline=time.monotonic()+30,limits=limits)
    def test_complete_exact_row_and_modular_unverified_result(self):
        n,v,p=fixture();r=self.run_probe(n,v,p);self.assertTrue(r['complete'],r.get('reason'));self.assertEqual(r['status'],'UNVERIFIED_COUNTEREXAMPLE');self.assertFalse(r['identity_refuted']);self.assertEqual(F(r['feedback_row']['rhs']),-253);self.assertEqual(r['nonconstant_difference'],(-253)%65537);self.assertEqual(len(r['square_values']),366);self.assertEqual(len(r['relation_values']),613);self.assertEqual(sum(len(g['exact_columns'])for g in r['gram_values']),360)
    def test_signed_relation_pair_and_gram_parent_storage(self):
        n,v,p=fixture();L=P.LANGUAGE;n['instance']['relation_groups'][0]=[dict(spec=dict(kind='unit'),multiplier=L.dump_poly(L.constant(1)))];n['instance']['square_groups'][0]=[dict(weight='1',poly=L.dump_poly(L.add(L.constant(1),L.variable(1))))]
        r=self.run_probe(n,v,p);self.assertTrue(r['complete'],r.get('reason'));row={e['index']:F(e['coefficient'])for e in r['feedback_row']['entries']};self.assertEqual(row[0],15);self.assertEqual(row[366],3);self.assertEqual(row[367],-3)
        pairs=[(i,j)for i in range(15)for j in range(i,15)];prefix=pairs.index((1,1));cross=pairs.index((0,1));self.assertEqual(row[1597+240+prefix],253);self.assertEqual(row[1597+240+cross],22);self.assertTrue(all(i in r['feedback_row']['zero_coordinates']for i in range(1592,1597)))
    def test_feedback_row_coordinates_and_residual_agree(self):
        n,v,p=fixture();v[1597+240+16]='3/2';p=P.preflight(v,p['program'],X=1,deadline=time.monotonic()+30);r=self.run_probe(n,v,p);row=r['feedback_row'];self.assertEqual(len(row['entries'])+len(row['zero_coordinates']),1957);self.assertEqual((r['feedback_rhs_mod_prime']-r['feedback_row_dot_mod_prime'])%65537,r['nonconstant_difference'])
    def test_denominator_bad_coordinates_and_partial_caps_unknown(self):
        n,v,p=fixture();n['instance']['square_groups'][0]=[dict(weight='1/65537',poly=[])]
        r=self.run_probe(n,v,p);self.assertFalse(r['complete']);self.assertEqual(r['status'],'UNKNOWN');self.assertIsNone(r['nonconstant_difference'])
        n,v,p=fixture();n['instance']['relation_groups'].pop();self.assertFalse(self.run_probe(n,v,p)['complete']);n,v,p=fixture();self.assertFalse(self.run_probe(n,v,p,max_source_cells=1)['complete'])
    def test_exact_zero_is_only_not_refuted(self):
        n,v,p=fixture();pairs=[(i,j)for i in range(15)for j in range(i,15)];v[1597+240+pairs.index((1,1))]='-1';p=P.preflight(v,p['program'],X=1,deadline=time.monotonic()+30);r=self.run_probe(n,v,p);self.assertEqual(r['nonconstant_difference'],0);self.assertEqual(r['status'],'NOT_REFUTED_BY_THIS_PROBE');self.assertFalse(r['universal_identity_proved'])
    def test_prime_and_rational_preallocation(self):
        _,v,p=fixture();v[0]='1/65537'
        with self.assertRaises(ValueError):P.preflight(v,p['program'],X=1)
        b=P.Budget(deadline=time.monotonic()+30)
        for q in ['1/0','01','1/-2']:
            with self.assertRaises(ValueError):b.rational(q)
        with self.assertRaises(OverflowError):b.rational('9'*2000)
        with self.assertRaises(ValueError):P.Budget(deadline=float('nan'))
        with self.assertRaises(ValueError):P.preflight(['0']*1957,p['program'],X=1,prime=65535)
    def test_math_only_complete_legacy_source_and_factor_order_oracle(self):
        import cancellation_factor_search_language as legacy
        self.assertEqual(P.MATH_NATIVE.FACTOR_ORDER,[(d['theta'],d['kernel'])for d in legacy.template_catalog()['selected']])
        program=dict(target='mu',q=6,C='32',claim='critical');deadline=time.monotonic()+120
        new=P.MATH_NATIVE.build_affine(program,1)
        def reference(*args,**kwargs):return P.NATIVE.BASE.build(program,1,max_horizon=3,max_operations=10000000,max_terms=100000,max_coefficient_bits=4096)
        with patch.object(P,'build_native',side_effect=reference):old=P.build_native_metered(program,1,deadline=deadline,max_line_events=10000000)
        for key in ['instance','gram_blocks','storage_blocks','gram_specs']:self.assertEqual(new[key],old[key],key)
    def test_actual_tiny_math_only_source_probe_has_no_crypto_calls(self):
        import hashlib
        program=dict(target='mu',q=6,C='32',claim='critical');deadline=time.monotonic()+120;vector=['0']*1957
        with patch.object(hashlib,'sha256',side_effect=AssertionError('cryptographic hash forbidden in research path')):
            n=P.build_native_metered(program,1,deadline=deadline,max_line_events=10000000)
            p=P.preflight(vector,program,X=1,deadline=deadline);r=P.probe_native(n,vector,p,deadline=deadline)
        self.assertTrue(r['complete'],r.get('reason'));self.assertEqual(n['gram_specs'],dict(full_child=15,full_parent=15,storage_K=15));self.assertEqual(r['nonconstant_difference'],65284)
    def test_source_guard_escapes_legacy_except_and_restores_trace(self):
        seen=[]
        def previous(frame,event,arg):return previous
        def legacy(*args,**kwargs):
            try:
                for i in range(10000):seen.append(i)
            except Exception:seen.append('swallowed')
            return {}
        old=sys.gettrace();sys.settrace(previous)
        try:
            with patch.object(P,'build_native',side_effect=legacy):
                with self.assertRaises(OverflowError):P.build_native_metered({},1,deadline=time.monotonic()+30,max_line_events=50)
            self.assertIs(sys.gettrace(),previous);self.assertNotIn('swallowed',seen)
        finally:sys.settrace(old)
    def test_source_guard_latch_and_no_arbitrary_callback_inside(self):
        def legacy(*args,**kwargs):
            try:
                for i in range(10000):pass
            except BaseException:pass
            return {}
        with patch.object(P,'build_native',side_effect=legacy):
            with self.assertRaises(OverflowError):P.build_native_metered({},1,deadline=time.monotonic()+30,max_line_events=50)

if __name__=='__main__':unittest.main()
