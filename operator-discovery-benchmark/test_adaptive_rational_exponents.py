"""Exact, source-free iterator and production calibration."""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import time
import unittest

import adaptive_rational_exponents as A

WORK=0


def batch(**kwargs):
    global WORK
    try:result=A.next_batch(**kwargs)
    except ValueError as error:
        WORK+=getattr(error,'operations',0);raise
    WORK+=result['operations'];return result


class FactoryMeter:
    def charge(self,n):
        global WORK
        WORK+=n


class Exponents(unittest.TestCase):
    def test_height_order_and_small_interval_completeness(self):
        expected=[]
        for h in range(1,10):
            for a in range(-(h-1),h):
                b=h-abs(a)
                if math.gcd(a,b)==1 and F(-3,2)<=F(a,b)<=F(5,4):
                    expected.append(str(F(a,b)))
        actual=[];cursor=None
        while True:
            r=batch(cursor=cursor,lower='-3/2' if cursor is None else None,
                    upper='5/4' if cursor is None else None,max_candidates=1,work_budget=5000)
            cursor=r['cursor']
            actual.extend(q for q in r['candidates'] if abs(F(q).numerator)+F(q).denominator<=9)
            if r['coverage']['ordinary_complete_through_height']>=9:break
        self.assertEqual(actual,expected)
        self.assertFalse(r['coverage']['all_rationals_in_interval_covered'])
        self.assertTrue(r['coverage']['no_semantic_denominator_ceiling'])

    def test_pause_resume_equals_uninterrupted_without_restart(self):
        expected=batch(max_candidates=30,work_budget=100000)['candidates']
        cursor=None;actual=[];charged=0
        while len(actual)<30:
            r=batch(cursor=cursor,max_candidates=3,work_budget=500)
            cursor=r['cursor'];actual.extend(r['candidates']);charged+=r['operations']
            self.assertLessEqual(r['operations'],500)
        self.assertEqual(actual[:30],expected)
        self.assertEqual(cursor['operations_total'],charged)
        self.assertEqual(len(actual),len(set(actual)))
        self.assertEqual(cursor['scans_total'],(cursor['height']-1)**2+cursor['offset'])

    def test_requested_257_reduction_queue_and_ordinary_dedup(self):
        r=batch(max_candidates=2,work_budget=5000,requested=['2/514','1/257','0','3/2'])
        self.assertEqual(r['candidates'],['1/257','0'])
        self.assertEqual(r['coverage']['pending_requested'],1)
        r2=batch(cursor=r['cursor'],max_candidates=3,work_budget=5000)
        self.assertEqual(r2['candidates'],['1','1/2','1/3'])
        self.assertEqual(r2['request_rejections'][0]['reason'],'outside_interval')
        self.assertNotIn('0',r2['candidates'])
        # A finite resource ceiling does not silently drop a larger request.
        text='1/'+'9'*200
        paused=batch(requested=[text],max_candidates=1,work_budget=100)
        self.assertEqual(paused['candidates'],[])
        self.assertEqual(paused['cursor']['requests'],[text])
        admitted=batch(cursor=paused['cursor'],max_candidates=1,work_budget=200000)
        self.assertEqual(admitted['candidates'],[text])
        self.assertEqual(admitted['coverage']['pending_requested'],0)

    def test_signed_bounds_singleton_and_zero_work(self):
        paused=batch(lower='-2/4',upper='1/2',requested=['-3/6','+0/-3'],work_budget=0)
        self.assertFalse(paused['coverage']['interval_validated'])
        self.assertEqual(paused['cursor']['offset'],0)
        self.assertEqual(len(paused['cursor']['requests']),2)
        r=batch(cursor=paused['cursor'],max_candidates=4,work_budget=5000)
        self.assertEqual(r['candidates'][:2],['-1/2','0'])
        self.assertEqual(len(r['candidates']),len(set(r['candidates'])))
        self.assertEqual(r['coverage']['interval'],['-1/2','1/2'])
        one=batch(lower='-2/4',upper='-3/6',work_budget=5000)
        self.assertEqual(one['candidates'],['-1/2'])
        self.assertTrue(one['coverage']['all_rationals_in_interval_covered'])
        again=batch(cursor=one['cursor'],work_budget=5000)
        self.assertEqual(again['candidates'],[])

    def test_invalid_exact_inputs_and_cursor_rejected(self):
        for kwargs in (dict(lower=0.0),dict(requested=[.5]),dict(upper='1/0'),
                       dict(lower='2',upper='1'),dict(requested=['0.5']),
                       dict(max_candidates=True),dict(max_candidates=0),dict(work_budget=-1)):
            with self.assertRaises(ValueError):batch(**kwargs)
        cursor=batch(max_candidates=1,work_budget=5000)['cursor']
        bad=dict(cursor,offset=True)
        with self.assertRaises(ValueError):batch(cursor=bad)
        bad=dict(cursor,scans_total=999)
        with self.assertRaises(ValueError):batch(cursor=bad)
        with self.assertRaises(ValueError):batch(cursor=cursor,upper='2')

    def test_new_typed_productions_without_bound_promotion(self):
        meter=FactoryMeter()
        twist=A.coefficient_twist('2/514',3,meter)
        self.assertEqual(twist,dict(op='coefficient_twist',exponent='1/257',state=3))
        negative=A.coefficient_twist(F(-7,3),0,meter)
        self.assertEqual(negative['exponent'],'-7/3')
        contract=A.production_contract(twist)
        self.assertTrue(contract['recovery_needed']);self.assertFalse(contract['recovery_paid'])
        self.assertFalse(contract['uniform_bound_proved'])
        power=A.signed_power('1/257',8,meter)
        self.assertEqual(power['op'],'signed_power')
        self.assertEqual(A.signed_power_ast('1/257',1,meter),['rpow',['input',1],'1/257','signed'])
        for state in (True,-1):
            with self.assertRaises(ValueError):A.coefficient_twist('1/2',state,meter)
        with self.assertRaises(ValueError):A.coefficient_twist(.5,0,meter)
        with self.assertRaises(ValueError):A.signed_power_ast('1/2',2,meter)


if __name__=='__main__':
    start=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Exponents))
    path=Path(__file__).with_name('adaptive_rational_exponents_development.json')
    previous=json.loads(path.read_text()) if path.exists() else dict(runs=[])
    previous['runs'].append(dict(returncode=0 if result.wasSuccessful() else 1,operations=WORK,
        tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),
        elapsed_seconds=time.monotonic()-start,source_evaluations=0))
    previous.update(module='test_adaptive_rational_exponents',operations=sum(r['operations'] for r in previous['runs']))
    path.write_text(json.dumps(previous,indent=2,sort_keys=True)+'\n')
    print('SYNTHETIC_WORK module=test_adaptive_rational_exponents operations='+str(WORK),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
