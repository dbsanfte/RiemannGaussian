"""Producer semantics on synthetic arithmetic; no production coefficient archive."""
from fractions import Fraction as Q
from pathlib import Path
import json
import time
import unittest

import periodic_normalization_search_040 as P


METER=P.SOURCE.Meter(cap=1_000_000,seconds=120)


def source(lattice=257,r=123,v=193):
    atom=lambda kind,shift:dict(kind=kind,shift=shift)
    return dict(lattice=lattice,channels=[
        dict(atoms=[atom('power',r),atom('mu',0),atom('mu',0)],weight=['3','0']),
        dict(atoms=[atom('power',r),atom('mu',0),atom('mu',v)],weight=['-3','0']),
        dict(atoms=[atom('power',r),atom('mu',v)],weight=['0','-1']),
        dict(atoms=[atom('mu',0)],weight=['-3','0'])])


def mobius(n):
    sign=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;sign=-sign
            if n%p==0:return 0
        p+=1
    return -sign if n>1 else sign


class PeriodicSearch(unittest.TestCase):
    def test_periodic_inverse_identity_for_composite_periods(self):
        for q in (2,4,6,17):
            primitive=P.periodic(q)
            c=int(primitive['step_coefficients'][1][1])
            for n in range(1,85):
                value=sum(mobius(d)*(1+c*int((n//d)%q==0))
                          for d in range(1,n+1) if n%d==0)
                self.assertEqual(value,int(n==1)-q*int(n==q))

    def test_rational_feasibility_without_denominator_whitelist(self):
        for theta,v in ((Q(2,3),Q(59,100)),(Q(134,257),Q(193,257)),
                        (Q(1000,1001),Q(501,1001)),(Q(2,3),Q(1,2))):
            h=P.hyperbola_search(theta,v)
            alpha=Q(h['selected_alpha']);sigma=Q(h['selected_exponent'])
            self.assertEqual(alpha,theta/(1+theta))
            self.assertGreaterEqual(sigma,max(alpha,theta*(1-alpha)))
            self.assertLessEqual(sigma,theta)
            self.assertEqual(h['absolute_shift_contraction'],v>Q(1,2))
            self.assertLess(sigma,Q(1,2))
        padded=P.hyperbola_search('2/3','59/100')
        self.assertEqual(padded['envelope_minimum'],'2/5')
        self.assertEqual(padded['selected_exponent'],'91/200')

    def test_source_denominator_propagates_and_no_bound_is_invented(self):
        result=P.search(source(),q_values=[4,6],scalar_bound='100',meter=METER)
        self.assertEqual(result['family']['r'],'123/257')
        self.assertEqual(result['hyperbola_search']['selected_alpha'],'134/391')
        self.assertEqual(result['selected'],dict(q=4,power=1))
        chosen=next(p for p in result['programs'] if p['q']==4 and p['power']==1)
        self.assertEqual(chosen['open_source_channels'],[0])
        self.assertLess(Q(chosen['reduction']['paid_remainder']['energy_power']),0)
        self.assertFalse(chosen['reduction']['new_target_bound_proved'])
        self.assertFalse(result['RH_proved'])

    def test_invalid_work_grammar_and_missing_source_unit(self):
        for kwargs in (dict(q_values=[]),dict(powers=[0,True,2]),dict(q_values=[True]),
                       dict(q_values=[2,2]),dict(scalar_bound='0')):
            with self.assertRaises(ValueError):P.search(source(),meter=METER,**kwargs)
        altered=source();altered['channels'].pop()
        with self.assertRaises(ValueError):P.search(altered,meter=METER)


if __name__=='__main__':
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(PeriodicSearch))
    record=dict(returncode=0 if result.wasSuccessful() else 1,tests=result.testsRun,
                operations=METER.operations,elapsed_seconds=time.monotonic()-started,
                failures=len(result.failures),errors=len(result.errors),
                exposure='synthetic source AST, finite generic Mobius inversion, exact rational exponent constraints only')
    path=Path(__file__).with_name('periodic_normalization_search_040_development.json')
    receipt=json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1',invocations=[])
    receipt['invocations'].append(record)
    receipt['cumulative_operations']=sum(r['operations'] for r in receipt['invocations'])
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print('SYNTHETIC_WORK '+json.dumps(record))
    raise SystemExit(record['returncode'])
