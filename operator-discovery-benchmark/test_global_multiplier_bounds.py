import copy
import unittest

import arithmetic_prefix_relations as A
import global_multiplier_bounds as P
import check_global_multiplier_bounds as C


SYNTHETIC = dict(lattice=14, channels=[
    dict(atoms=[dict(kind='power',shift=5),dict(kind='mu',shift=0),dict(kind='mu',shift=0)],weight=['2','0']),
    dict(atoms=[dict(kind='power',shift=5),dict(kind='mu',shift=0),dict(kind='mu',shift=9)],weight=['-2','0']),
    dict(atoms=[dict(kind='power',shift=5),dict(kind='mu',shift=9)],weight=['0','-1']),
    dict(atoms=[dict(kind='mu',shift=0)],weight=['-2','0'])])


class CompleteMultiplierSearch(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.meter=A.Meter(cap=20_000_000,seconds=90)
        cls.relations=A.generate(SYNTHETIC,cls.meter)
        cls.result=P.search(SYNTHETIC,cls.relations,cls.meter)

    def test_complete_symbolic_search_and_independent_replay(self):
        replay=C.verify_search(SYNTHETIC,self.relations,self.result)
        self.assertTrue(replay['verified'])
        self.assertEqual(replay['exact_endpoint_equivalences'],1)
        self.assertFalse(replay['whole_signed_bound_proved'])
        self.assertEqual(self.result['cases'][0]['status'],'no_bound_in_provider_span')
        conditional=self.result['cases'][2]
        self.assertEqual(conditional['open_providers'],['complete_joined_tail'])
        self.assertEqual(conditional['excess_growth_providers'],['rhs_1'])
        self.assertFalse(conditional['meets_subpower_target'])
        self.assertEqual(sum(x['meets_subpower_target'] for x in self.result['calibrations']),1)

    def test_source_tail_payment_and_unit_mutations_rejected(self):
        for which in ('source_rhs','tail_paid','growth','unit','floor_tail','scope'):
            bad=copy.deepcopy(self.result)
            if which=='source_rhs':bad['joined_relation']['forcing'][1]['weight'][1]='0'
            elif which=='tail_paid':bad['cases'][2]['providers'][-1]['price']['status']='PROVED'
            elif which=='growth':bad['cases'][2]['excess_growth_providers']=[]
            elif which=='unit':bad['joined_relation']['forcing'].pop(0)
            elif which=='floor_tail':bad['floor_templates'][0]['template']['lhs'][0]['inner_domain']='1<=k<=3'
            else:bad['whole_signed_bound_proved']=True
            with self.assertRaises(ValueError,msg=which):C.verify_search(SYNTHETIC,self.relations,bad)

    def test_endpoint_and_formal_witness_scope(self):
        case=next(c for c in self.result['auxiliary_cases'] if c['equivalent_obligation'] is not None)
        self.assertEqual(case['status'],'conditional_energy_implication')
        self.assertFalse(case['equivalent_obligation']['new_bound_proved'])
        for which in ('equivalence','witness','arithmetic_counterexample'):
            bad=copy.deepcopy(self.result)
            if which=='equivalence':
                row=next(c for c in bad['auxiliary_cases'] if c['equivalent_obligation'] is not None)
                row['equivalent_obligation']['target_coefficient']='0'
            elif which=='witness':bad['cases'][0]['obstruction']['vector'][0]='0'
            else:bad['cases'][0]['obstruction']['actual_arithmetic_counterexample']=True
            with self.assertRaises(ValueError,msg=which):C.verify_search(SYNTHETIC,self.relations,bad)

    def test_general_rational_prices_with_growth_charged(self):
        for powers in ([],['-257/256'],['-1'],['-37/257'],['-1/2'],['0'],['5/7'],['-1/3','-1/3']):
            rhs=dict(power_factors=powers,weight=['3/2','-1'])
            price=P.rhs_price(rhs)
            self.assertTrue(C.verify_rhs_price(rhs,price))
        rhs=dict(power_factors=['-37/257'],weight=['0','1'])
        bad=P.rhs_price(rhs);bad['subpower_eligible']=True
        with self.assertRaises(ValueError):C.verify_rhs_price(rhs,bad)
        bad=P.rhs_price(rhs);bad['energy']['constant']='0'
        with self.assertRaises(ValueError):C.verify_rhs_price(rhs,bad)

    def test_missing_shape_and_equivalence_debt_rejected(self):
        for rows in ([[[]]], [['1']*13], ['1']):
            with self.assertRaises(ValueError):C.matrix(rows)
        with self.assertRaises(ValueError):
            C.verify_formal_witness([['-1','0'],['0','0']],[['1']],['1','-1'])
        case=next(c for c in self.result['auxiliary_cases'] if c['equivalent_obligation'] is not None)
        claim=copy.deepcopy(case['equivalent_obligation']);claim['new_bound_proved']=True
        with self.assertRaises(ValueError):
            C.verify_equivalence(case['target'],claim['auxiliary'],case['relations'],case['providers'][:-1],claim)

    def test_omitted_template_and_equivalence_coverage_rejected(self):
        for which in ('missing_floor','repeated_floor','missing_equivalence'):
            bad=copy.deepcopy(self.result)
            if which=='missing_floor':bad['floor_templates']=[]
            elif which=='repeated_floor':bad['floor_templates'][1]=bad['floor_templates'][0]
            else:
                case=next(c for c in bad['auxiliary_cases'] if c['equivalent_obligation'] is not None)
                case['equivalent_obligation']=None
            with self.assertRaises(ValueError,msg=which):C.verify_search(SYNTHETIC,self.relations,bad)


if __name__=='__main__':
    unittest.main()
