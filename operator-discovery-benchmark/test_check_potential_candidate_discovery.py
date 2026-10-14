"""Tiny finite arithmetic, syntax and cache counterexamples only."""
import copy
from fractions import Fraction as F
import time
import unittest

import check_potential_candidate_discovery as C


def integer(n):return ['int',n]
def var(name):return ['v',name]
def state(tree,weight='1'):return dict(states=[dict(weight=weight,tree=tree)])
def mertens(endpoint=None):return ['sum','n',integer(1),var('t')if endpoint is None else endpoint,['x',var('n')]]


class Checks(unittest.TestCase):
    meters=[]
    formal_operations=0

    @classmethod
    def tearDownClass(cls):
        operations=sum(m.operations for m in cls.meters)+cls.formal_operations
        print('SYNTHETIC_WORK module=test_check_potential_candidate_discovery operations=%d'%operations)
        if operations>5000000:raise AssertionError('owned tiny development invocation exceeds5m')

    def meter(self,cap=1000000,**kwargs):
        meter=C.Meter(cap,**kwargs);self.meters.append(meter);return meter

    def checker(self,horizon=15,**kwargs):return C.Checker(horizon,self.meter(),**kwargs)

    def test_actual_mobius_and_full_baseline_anchor(self):
        checker=self.checker()
        self.assertEqual(checker.values[:16],[0,1,-1,-1,0,-1,1,-1,0,0,1,-1,0,-1,1,1])
        baseline=dict(states=[])
        self.assertEqual(checker.measure(baseline,1),dict(X=1,E='1',V='0',W='1'))
        result=checker.case(baseline,3)
        self.assertEqual(result['parent'],dict(X=3,E='2/3',V='0',W='2/3'))
        self.assertEqual(result['child'],dict(X=6,E='1/2',V='0',W='1/2'))
        self.assertEqual(result['innovation'],'-1/6')

    def test_moving_prime_bank_retains_every_cross_term_and_full_E(self):
        checker=self.checker()
        inner=['sum','n',integer(1),['idiv',var('t'),var('p')],['x',var('n')]]
        tree=['sum','p',integer(2),['root',var('t'),1,2],
              ['guard',['prime',var('p')],['mul',['x',var('p')],inner]]]
        candidate=state(tree);result=checker.case(candidate,3)
        self.assertEqual(result['parent'],dict(X=3,E='2/3',V='0',W='2/3'))
        self.assertEqual(result['child'],dict(X=6,E='1/2',V='25/36',W='43/36'))
        self.assertEqual(result['innovation'],'19/36')
        # Separate bank squares give15/36; the omitted prime cross terms10/36
        # change the complete child potential and signed innovation.
        self.assertNotEqual(result['child']['V'],'5/12')
        self.assertEqual(checker.measure(candidate,1)['W'],'1')

    def test_child_uses_its_own_X_and_all_fractional_roots_are_exact(self):
        checker=self.checker()
        candidate=state(['embed',var('X')]);result=checker.case(candidate,2)
        self.assertEqual(result['parent']['V'],'2');self.assertEqual(result['child']['V'],'4')
        for denominator in(2,3,6):
            candidate=state(['embed',['root',var('t'),1,denominator]])
            result=checker.measure(candidate,3)
            expected=sum(F(next(k for k in range(6)if (k+1)**denominator>t))**2 for t in range(3,6))/9
            self.assertEqual(F(result['V']),expected)
        self.assertEqual(checker.measure(state(['embed',['root',integer(0),0,6]]),1)['V'],'1')
        huge=1<<4095
        bad=state(['embed',['root',integer(2),huge,1]])
        with self.assertRaises(OverflowError):checker.measure(bad,1)
        # Reduce equal exponents before power preflight; this is exactly t.
        self.assertEqual(checker.measure(state(['embed',['root',var('t'),huge,huge]]),1)['V'],'1')

    def test_controls_are_source_specific_diagnostics(self):
        baseline=dict(states=[])
        one=self.checker(source='one');self.assertEqual(one.measure(baseline,2)['E'],'13/4')
        masked=self.checker(source='partial_prime_2')
        self.assertEqual(masked.values[:9],[0,1,-1,1,0,1,-1,1,0])
        self.assertEqual(masked.measure(baseline,2)['E'],'1/4')
        self.assertEqual(self.checker().measure(baseline,2)['E'],'1/4')

    def test_full_syntax_checked_even_behind_false_guard(self):
        false=['eq',integer(1),integer(0)]
        checker=self.checker()
        safe=state(['guard',false,['ratio',integer(1),integer(0)]])
        self.assertEqual(checker.measure(safe,1)['V'],'0')
        for tree in (
            ['guard',false,['undefined']],
            ['guard',false,['x',var('N')]],
            ['sum','X',integer(1),integer(1),['q','1']],
            ['sum','N',integer(1),integer(1),['x',var('N')]],
            ['add',['q','1'],integer(2)],
            ['embed',integer(True)],
        ):
            with self.assertRaises(ValueError):checker.measure(state(tree),1)
        for candidate in (state(['q','1'],'-1'),state(['q','1'],'01'),state(['q','01']),
                          dict(states=[dict(weight='1',tree=['q','0'])]*3)):
            with self.assertRaises(ValueError):C.validate_candidate(candidate,self.meter())

    def test_boolean_short_circuit_floor_division_and_exact_masks(self):
        checker=self.checker()
        bad_comparison=['eq',['idiv',integer(1),integer(0)],integer(0)]
        guard=['and',['eq',integer(1),integer(0)],bad_comparison]
        self.assertEqual(checker.measure(state(['guard',guard,['q','1']]),1)['V'],'0')
        self.assertEqual(checker.measure(state(['embed',['idiv',integer(-3),integer(2)]]),1)['V'],'4')
        mask=['and',['squarefree',var('t')],['eq',['gcd',var('t'),integer(2)],integer(1)]]
        candidate=state(['guard',mask,['x',var('t')]])
        self.assertEqual(checker.measure(candidate,3)['V'],'2/9')
        with self.assertRaises(ValueError):checker.measure(state(['ratio',integer(1),integer(0)]),1)
        with self.assertRaises(ValueError):checker.measure(state(['x',integer(0)]),1)

    def test_sum_cache_binds_lower_endpoint_and_free_body_dependencies(self):
        checker=self.checker()
        shifted=['sum','n',integer(1),var('t'),['x',['iadd',var('n'),var('X')]]]
        candidate=state(shifted)
        self.assertEqual(checker.measure(candidate,1)['V'],'1')
        self.assertEqual(checker.measure(candidate,2)['V'],'5/4')
        lower=['sum','n',var('X'),var('t'),['x',['isub',var('n'),integer(1)]]]
        candidate=state(lower);checker.measure(candidate,2)
        with self.assertRaises(ValueError):checker.measure(candidate,1)
        # An empty domain must not evaluate its invalid scalar summand.
        candidate=state(['sum','n',integer(2),integer(1),['x',integer(0)]])
        self.assertEqual(checker.measure(candidate,1)['V'],'0')

    def test_cached_prefix_extends_only_the_requested_domain(self):
        checker=self.checker(horizon=3)
        candidate=state(['sum','n',integer(1),var('t'),['x',['iadd',var('n'),integer(1)]]])
        self.assertEqual(checker.measure(candidate,1)['V'],'1')
        with self.assertRaises(ValueError):checker.case(candidate,1)
        checker=self.checker(horizon=31);candidate=state(mertens())
        before=checker.meter.operations;first=checker.measure(candidate,8)
        initial=checker.meter.operations-before
        before=checker.meter.operations;second=checker.measure(candidate,8)
        reused=checker.meter.operations-before
        self.assertEqual(first,second);self.assertGreater(initial,reused*2)

    def test_signed_products_match_generic_exact_formal_compilation(self):
        from cancellation_arithmetic_language import Compiler
        checker=self.checker();tree=['mul',mertens(),mertens(['root',var('t'),1,2])]
        candidate=state(tree,weight='1/2');result=checker.measure(candidate,3)
        expected=F(0)
        for t in range(3,6):
            compiler=Compiler(3,15,max_operations=1000000)
            polynomial=compiler.compile(['scale','1/2',['mul',tree,tree]],bindings=dict(t=t))
            self.__class__.formal_operations+=compiler.operations
            value=F(0)
            for monomial,coefficient in polynomial.items():
                term=coefficient
                for index in monomial:term*=checker.values[index]
                value+=term
            expected+=value/9
        self.assertEqual(F(result['V']),expected)
        self.assertEqual(F(result['W']),F(result['E'])+expected)

    def test_every_full_value_innovation_and_anchor_is_verified(self):
        checker=self.checker();candidate=state(mertens());record=checker.case(candidate,3)
        self.assertEqual(checker.verify_case(candidate,record),record)
        anchor=checker.measure(candidate,1);self.assertEqual(checker.verify_measure(candidate,anchor),anchor)
        for mutate in (
            lambda r:r['parent'].update(E='0'),
            lambda r:r['child'].update(V='0'),
            lambda r:r.update(innovation='0'),
            lambda r:r['parent'].update(X=True),
        ):
            bad=copy.deepcopy(record);mutate(bad)
            with self.assertRaises(ValueError):checker.verify_case(candidate,bad)
        bad=dict(anchor,W='0')
        with self.assertRaises(ValueError):checker.verify_measure(candidate,bad)

    def test_shared_work_bits_cells_deadline_and_complete_case_fail_closed(self):
        meter=self.meter();one=C.Checker(7,meter);before=meter.operations
        two=C.Checker(7,meter);self.assertGreater(meter.operations,before)
        one.case(dict(states=[]),2);two.measure(dict(states=[]),1)
        with self.assertRaises(ValueError):one.case(dict(states=[]),3)
        short=self.meter(cap=1)
        with self.assertRaises(OverflowError):C.Checker(15,short)
        self.assertLessEqual(short.operations,short.max_operations)
        with self.assertRaises(OverflowError):C.Checker(15,self.meter(max_cells=10))
        with self.assertRaises(TimeoutError):C.Checker(15,self.meter(deadline=time.monotonic()-1))
        with self.assertRaises(OverflowError):C.validate_candidate(state(['q',str(1<<4096)]),self.meter())
        deep=['q','1']
        for _ in range(25):deep=['scale','1',deep]
        with self.assertRaises(OverflowError):C.validate_candidate(state(deep),self.meter())


if __name__=='__main__':unittest.main()
