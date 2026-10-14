import copy
import unittest
import primitive_state_localizer_probe as P
import check_primitive_state_localizer_probe as C


def fixture():
    groups=[[dict(spec=dict(kind='prime_power',p=2,e=1),multiplier=[dict(m=[1],c='1')])],
            [dict(spec=dict(kind='unit'),multiplier=[dict(m=[],c='1')])]]
    inst=dict(target='mu',horizon=2,lhs=[],square_groups=[],relation_groups=groups)
    desc=[dict(id='prime-unit'),dict(id='unit')]
    dual=dict(monomials=[dict(instance=0,m=m) for m in [[],[1],[1,2]]],weights=['0','0','1'])
    return [inst],desc,dual


class Probe(unittest.TestCase):
    def test_signed_violation_and_zero(self):
        inputs=fixture();r=P.probe(*inputs)
        self.assertEqual(r['status'],'witness_invalid_for_localizer_cone')
        self.assertEqual(r['counts'],dict(violated_relation=1,annihilated_relation=1,unknown_missing_coordinates=0))
        self.assertTrue(C.verify(*inputs,r)['verified'])
        inputs[2]['weights'][2]='-1';r=P.probe(*inputs)
        self.assertEqual(r['rows'][0]['status'],'violated_relation')
        self.assertTrue(C.verify(*inputs,r)['verified'])

    def test_all_zero_extension_and_missing(self):
        inputs=fixture();inputs[2]['weights'][2]='0'
        self.assertEqual(P.probe(*inputs)['status'],'witness_extends_to_localizer_cone')
        inputs[2]['monomials'].pop();inputs[2]['weights'].pop()
        r=P.probe(*inputs)
        self.assertEqual(r['status'],'unknown_missing_coordinates')
        self.assertNotIn('pairing',r['rows'][0]);self.assertTrue(C.verify(*inputs,r)['verified'])

    def test_cancel_missing_before_support_check(self):
        inst,desc,dual=fixture();term=copy.deepcopy(inst[0]['relation_groups'][0][0]);term['multiplier'][0]['c']='-1'
        inst[0]['relation_groups'][0].append(term);dual['monomials'].pop();dual['weights'].pop()
        r=P.probe(inst,desc,dual)
        self.assertEqual(r['status'],'witness_extends_to_localizer_cone')
        self.assertEqual(r['missing_coordinates'],[]);self.assertTrue(C.verify(inst,desc,dual,r)['verified'])

    def test_corrupt_pairing_support_source_and_scope(self):
        inputs=fixture();result=P.probe(*inputs)
        for name,value in [('pairing','0'),('missing_indices',[0]),('complete_column_sha256','bad')]:
            bad=copy.deepcopy(result);bad['rows'][0][name]=value
            with self.assertRaises(ValueError):C.verify(*inputs,bad)
        bad=copy.deepcopy(result);bad['larger_cone_feasibility_proved']=True
        with self.assertRaises(ValueError):C.verify(*inputs,bad)
        bad=copy.deepcopy(result);bad['rows'].pop()
        with self.assertRaises(ValueError):C.verify(*inputs,bad)

    def test_false_prime_and_resource_cap(self):
        inst,desc,dual=fixture();inst[0]['relation_groups'][0][0]['spec']['p']=4
        with self.assertRaises(ValueError):P.probe(inst,desc,dual)
        with self.assertRaises(OverflowError):P.probe(*fixture(),max_operations=1)


if __name__=='__main__':unittest.main()
