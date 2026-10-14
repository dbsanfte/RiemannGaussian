"""Small synthetic native factors; no published candidate or fresh X7 source."""
import copy
from fractions import Fraction as F
import sys
import time
import unittest
from unittest.mock import patch
import check_primitive_state_uniform_identity_probe as C
import primitive_state_uniform_identity_probe as P


def fixture():
    X=1;H=3;sq=[[]for _ in range(366)];rel=[[]for _ in range(613)]
    sq[0]=[dict(weight='1',poly=[dict(m=[1],c='1')])]
    rel[0]=[dict(spec={'kind':'unit'},multiplier=[dict(m=[],c='1')])]
    lhs=[dict(m=[],c='32'),dict(m=[1,1],c='2'),dict(m=[1,2],c='-4'),dict(m=[1,3],c='-2'),dict(m=[2,2],c='-2'),dict(m=[2,3],c='-2'),dict(m=[3,3],c='-1')]
    def state(t):return [[dict(m=[],c='1')],[dict(m=[i],c='1')for i in range(1,t+1)],[],[],[],[],*[ [dict(m=[],c='-1/2')]for _ in range(9)]]
    blocks=dict(full_child=[state(2),state(3)],full_parent=[state(1)])
    native=dict(instance=dict(target='mu',horizon=H,lhs=lhs,square_groups=sq,relation_groups=rel),gram_blocks=blocks,storage_blocks=dict(kind='signed_storage_increment',child=blocks['full_child'],parent=blocks['full_parent'],child_multiplier='1',parent_multiplier='-4'),gram_specs={'full_child':15,'full_parent':15,'storage_K':15},gram_program=C.LOCAL.SPEC,primitive_state_spec=C.LOCAL.SPEC)
    vector=['0']*1957
    for i,q in [(0,2),(366,2),(367,5),(1598,1),(1718,-2),(1838,3),(1843,7),(1592,123)]:vector[i]=str(q)
    plan=P.preflight(vector,dict(target='mu',q=6,C='32',claim='critical'),X=X)
    receipt=P.probe_native(native,vector,plan,deadline=time.monotonic()+30)
    license=C._SourceLicense(C._TOKEN,native,plan,vector,dict(native_line_events=0,audit_operations=0,audit_cells=0))
    return native,vector,plan,receipt,license


class ProbeCheckerTests(unittest.TestCase):
    def test_complete_exact_feedback_and_modular_formal_refutation(self):
        native,vector,plan,receipt,license=fixture();result=C.verify_probe(license,vector,plan,receipt)
        self.assertTrue(result['nonconstant_formal_identity_refuted']);self.assertFalse(result['identity_refuted']);self.assertFalse(result['universal_identity_proved']);self.assertFalse(result['arithmetic_or_scalar_identity_refuted'])
        row=result['necessary_formal_identity_constraint'];coeff={r['index']:F(r['coefficient'])for r in row['entries']}
        self.assertEqual(F(row['rhs']),-253);self.assertEqual(coeff[0],9);self.assertEqual(coeff[366],3);self.assertEqual(coeff[367],-3);self.assertEqual(coeff[1598],46);self.assertEqual(coeff[1718],6);self.assertEqual(coeff[1838],22)
        self.assertTrue(set(range(1592,1597))<=set(row['zero_coordinates']));self.assertEqual(sum(coeff.get(i,F(0))*F(q)for i,q in enumerate(vector)),109);self.assertEqual(result['nonconstant_difference'],(-362)%65537)
    def test_unverified_native_never_promotes(self):
        native,v,plan,receipt,_=fixture()
        with self.assertRaises(ValueError):C.verify_probe(native,v,plan,receipt)
    def test_source_row_group_and_semantic_tampering(self):
        native,v,plan,receipt,lic=fixture()
        for key in ('feedback','relation','gram','target','source','flags'):
            bad=copy.deepcopy(receipt)
            if key=='feedback':bad['feedback_row']['entries'][0]['coefficient']='10'
            elif key=='relation':bad['relation_values'][0]['exact_baseline']='0'
            elif key=='gram':bad['gram_values'][2]['exact_columns'][1]['value']='1'
            elif key=='target':bad['target_exact_values'][0]='0'
            elif key=='source':bad['program']={}
            else:bad['universal_identity_proved']=True
            with self.assertRaises(ValueError):C.verify_probe(lic,v,plan,bad)
    def test_constant_slack_and_modular_false_negative_scope(self):
        native,v,plan,receipt,_=fixture();native['instance']['square_groups'][0]=[dict(weight='65537',poly=[dict(m=[1],c='1')])]
        v=['0']*1957;v[0]='1';plan=P.preflight(v,plan['program'],X=1);receipt=P.probe_native(native,v,plan,deadline=time.monotonic()+30)
        lic=C._SourceLicense(C._TOKEN,native,plan,v,{})
        result=C.verify_probe(lic,v,plan,receipt);self.assertEqual(result['nonconstant_difference'],(-253)%65537)
        # A zero reduction of one nonzero coefficient is not identity evidence.
        self.assertEqual(F(receipt['feedback_row']['entries'][0]['coefficient']),9*65537);self.assertFalse(result['universal_identity_proved'])
    def test_denominator_missing_coords_assignment_prime_and_caps(self):
        native,v,plan,receipt,lic=fixture()
        for field,value in [('assignment',[1]*3),('baseline',[1,0,0]),('prime',65535),('X',True),('layout',{})]:
            bad=copy.deepcopy(plan);bad[field]=value
            with self.assertRaises(ValueError):C.verify_plan(bad,v,C.Budget())
        bad=list(v);bad[1]='1/65537'
        with self.assertRaises(ValueError):C.verify_plan(plan,bad,C.Budget())
        with self.assertRaises(ValueError):C.verify_plan(plan,v[:-1],C.Budget())
        with self.assertRaises(OverflowError):C.verify_probe(lic,v,plan,receipt,max_operations=1)
        with self.assertRaises(ValueError):C.Budget(max_operations=True)
    def test_direct_polynomial_sensitivity(self):
        native,v,plan,receipt,lic=fixture();native['instance']['square_groups'][0][0]['poly'][0]['c']='2'
        changed=P.probe_native(native,v,plan,deadline=time.monotonic()+30)
        self.assertEqual(F(changed['feedback_row']['entries'][0]['coefficient']),36)
        with self.assertRaises(ValueError):C.verify_probe(lic,v,plan,receipt)
    def test_trace_guard_not_swallowed_and_trace_restored(self):
        native,v,plan,receipt,lic=fixture()
        def swallowed(*args):
            try:
                for _ in range(100):pass
            except BaseException:pass
            return native
        with patch.object(C,'_construct_source',side_effect=swallowed):
            with self.assertRaises(OverflowError):C.rebuild_source(plan,v,max_source_line_events=1)
        self.assertIsNone(sys.gettrace())
        with patch.object(C,'_construct_source',return_value=native):
            out=C.rebuild_source(plan,v,max_source_line_events=10000)
        self.assertEqual(out.plan,plan);self.assertIsNone(sys.gettrace())
    def test_independent_forward_constructor_tiny_equivalence(self):
        program=dict(target='mu',q=6,C='32',claim='critical')
        actual=C._construct_source(program,1);expected=C.LOCAL.build(program,1,max_horizon=27,max_operations=200000000,max_terms=100000,max_coefficient_bits=4096)
        self.assertEqual({k:actual[k]for k in ('instance','gram_blocks','storage_blocks','gram_specs')},{k:expected[k]for k in ('instance','gram_blocks','storage_blocks','gram_specs')})
    def test_math_only_native_to_probe_without_hashes(self):
        import hashlib
        vector=['0']*1957;program=dict(target='mu',q=6,C='32',claim='critical')
        with patch.object(hashlib,'sha256',side_effect=AssertionError('unexpected hash')):
            native=C._construct_source(program,1);plan=P.preflight(vector,program,X=1)
            receipt=P.probe_native(native,vector,plan,deadline=time.monotonic()+30)
            lic=C._SourceLicense(C._TOKEN,native,plan,vector,{})
            checked=C.verify_probe(lic,vector,plan,receipt)
        self.assertTrue(checked['verified'])

if __name__=='__main__':unittest.main()
