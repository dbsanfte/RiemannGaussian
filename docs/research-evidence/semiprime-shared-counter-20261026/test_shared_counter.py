#!/usr/bin/env python3
"""Focused exact-counter algebra/negative controls; not a runtime campaign."""
import argparse
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import unittest
from shared_counter import (Factor,ExplicitDesign,Stats,Jets,count,direct_count,
                            separated_fibre_sum,hermite_at_zero,validate)


def rational_design(copies=1):
    forms={}
    for f in range(copies):
        forms[f,0]={0:(1,F(-1,2)),1:(0,F(1,2))}
        forms[f,1]={0:(0,F(1,3)),1:(1,F(-1,3))}
    return ExplicitDesign(2,2,2,1,1,
        {1:((0,),(1,)),2:((0,),(1,))},
        {1:(0,)*copies,2:(0,)*copies},
        {1:((),((1,),)),2:((),((1,),))},forms)


class CounterControls(unittest.TestCase):
    def test_nontrivial_rational_taylor_mobius(self):
        factors=[Factor((0,1),lambda b:b[0]*b[1])]
        result=count(2,factors,rational_design())
        self.assertEqual(result.value,1)
        self.assertEqual(result.value,direct_count(2,factors).value)
        self.assertEqual(result.stats['Taylor_order_q'],1)
        self.assertEqual(result.stats['jet_precision'],2)
        self.assertEqual(result.stats['mobius_pairs'],10)
        self.assertGreater(result.stats['maximum_recorded_denominator_bits'],1)
        self.assertFalse(result.stats['diagnostics_invoked'])

    def test_second_order_taylor_and_size_two_mobius_sets(self):
        factors=[Factor((0,1),lambda b:b[0]*b[1]) for _ in range(2)]
        result=count(2,factors,rational_design(2))
        self.assertEqual(result.value,1)
        self.assertEqual(result.stats['Taylor_order_q'],2)
        self.assertEqual(result.stats['jet_precision'],3)
        self.assertEqual(result.stats['mobius_pairs'],18)

    def test_exact_hermite_higher_jets(self):
        # H(T)=1+5T/6-T²/3, with two order-two Taylor packets.
        stats=Stats();ops=Jets(2,stats)
        taylor={1:(F(3,2),F(1,6)),2:(F(4,3),F(-1,2))}
        self.assertEqual(hermite_at_zero(taylor,ops),1)
        # A degree-five control exercises genuinely higher multiplicity.
        ops=Jets(3,Stats());coeff=(F(7,5),F(-2),F(1,3),F(4),F(-1,7),F(2,9))
        from math import comb
        packets={t:tuple(sum(coeff[d]*comb(d,k)*t**(d-k) for d in range(k,len(coeff)))
                         for k in range(3)) for t in (1,2)}
        self.assertEqual(hermite_at_zero(packets,ops),coeff[0])

    def test_measurement_representatives_need_not_satisfy_forced_bits(self):
        stats=Stats();ops=Jets(1,stats);seen_nonforced_representative=[]
        def evaluate(g,x):
            if g==0:return ops.const(1+x[0]*x[1])
            if x[1]==0 and x[0]+x[1]==1:seen_nonforced_representative.append(x)
            return ops.const((x[0]+x[1])*(1+x[2]))
        result=separated_fibre_sum(3,((0,1),(2,)),(((1,1),),((1,),)),2,
                                   evaluate,{1},ops,stats)
        self.assertEqual(result,(F(15),))
        self.assertTrue(seen_nonforced_representative)
        self.assertEqual(stats.counts['measurement_tuples'],15) # radii2 and1, not2 and2

    def test_actual_constructed_layout_interface(self):
        from shared_layout import build_layout
        factors=[Factor((0,1),lambda b:b[0]^b[1])]
        layout=build_layout(2,[(0,1)],2,3,2,1)
        result=count(2,factors,layout)
        self.assertEqual(result.value,2)
        self.assertFalse(result.stats['quantitative_promises_valid'])
        with self.assertRaises(ValueError):count(2,factors,layout,require_quantitative=True)

    def test_invalid_kernel_rejected(self):
        design=rational_design()
        design.measurements={1:((),()),2:((),())}
        with self.assertRaisesRegex(ValueError,'kernel'):count(2,[Factor((0,1),lambda b:b[0]&b[1])],design)

    def test_invalid_restoration_degree_partition_and_measurement(self):
        factors=[Factor((0,1),lambda b:b[0]&b[1])]
        d=copy.deepcopy(rational_design());d.forms[0,0][0]=(0,F(-1,2))
        with self.assertRaisesRegex(ValueError,'restoration'):count(2,factors,d)
        d=copy.deepcopy(rational_design());d.forms[0,0][0]=(1,0,1)
        with self.assertRaisesRegex(ValueError,'degree'):count(2,factors,d)
        d=copy.deepcopy(rational_design());d.partitions[1]=((0,),(0,))
        with self.assertRaisesRegex(ValueError,'partition'):count(2,factors,d)
        d=copy.deepcopy(rational_design());d.measurements[1]=((),((2,),))
        with self.assertRaisesRegex(ValueError,'range'):count(2,factors,d)
        with self.assertRaises(ValueError):count(-1,factors,rational_design())

    def test_empty_groups_unused_variables_and_constant_factors(self):
        d=ExplicitDesign(2,2,2,1,1,{1:((0,1),()),2:((0,1),())},
                         {1:(),2:()},{1:((),()),2:((),())},{})
        self.assertEqual(count(2,[],d).value,4)
        d.sigma={1:(1,),2:(1,)}
        self.assertEqual(count(2,[Factor((),lambda b:0)],d).value,0)
        self.assertEqual(count(2,[Factor((),lambda b:F(1,2))],d).value,2)

    def test_general_rational_entries_are_algebraic_not_automatic_space_claim(self):
        d=ExplicitDesign(2,2,2,1,1,{1:((0,),(1,)),2:((0,),(1,))},
                         {1:(0,),2:(0,)},{1:((),()),2:((),())},{(0,0):{0:(1,)}})
        result=count(2,[Factor((0,),lambda b:F(1,3))],d)
        self.assertEqual(result.value,F(4,3))
        self.assertFalse(result.stats['only_boolean_entry_values_observed'])
        self.assertIn('common',result.stats['resource_contract'])

    def test_diagnostic_output_is_explicitly_separate(self):
        diagnostic=direct_count(2,[Factor((0,1),lambda b:b[0]|b[1])])
        self.assertEqual(diagnostic.value,3)
        self.assertEqual(diagnostic.method,'diagnostic_direct_boolean_sum')
        self.assertEqual(diagnostic.stats['diagnostic_boolean_assignments'],4)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('shared-counter-validation.json'))
    args=parser.parse_args()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(CounterControls))
    output=dict(status='PASS' if result.wasSuccessful() else 'FAIL',tests=result.testsRun,
                failures=len(result.failures),errors=len(result.errors),
                scope='streamed exact-counter algebra and negative controls; no factoring/time claim')
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    raise SystemExit(not result.wasSuccessful())
