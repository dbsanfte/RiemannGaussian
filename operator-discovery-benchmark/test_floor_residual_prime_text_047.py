"""Large admitted rational output must work with Python's digit limit enabled."""
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
import time
import unittest
import floor_residual_prime_047 as P
import check_floor_residual_prime_047 as C

PM=P.Meter();CM=C.Meter(cap=10_000_000)


class ExactTextTests(unittest.TestCase):
    def test_large_program_and_energy_roundtrip_without_global_limit_change(self):
        initial=sys.get_int_max_str_digits()
        value=Q((1<<18000)+1, (1<<16000)+3)
        for v in (value,-value,Q(1<<24000)):
            text=P._text(v)
            self.assertEqual(C._rational(text,CM,bits=32768),v)
            self.assertEqual(P._value(text),v)
        p=P._program('synthetic_big',{2:value},meter=PM)
        zero=P._add('cancel',[(Q(1),p),(Q(-1),p)],PM)
        self.assertEqual(zero['coefficients'],[])
        energy=Q((1<<50000)+1,(1<<45000)+3)
        self.assertEqual(C._rational(P._text(energy),CM,bits=P.MAX_ENERGY_BITS),energy)
        self.assertEqual(sys.get_int_max_str_digits(),initial)

    def test_full_synthetic_source_still_independently_replays(self):
        request=dict(prime=2,parent_support=3,parent_values=['1','-2/3','5/7'],
                     child_values=['1','2/5','-1/2','3/7','1/11','-2/9'])
        certificate=P.build_prime_construction(request,PM)
        self.assertTrue(C.verify_prime_construction(request,certificate,CM)['verified'])


if __name__=='__main__':
    path=Path(__file__).with_name('floor_residual_prime_text_047_development.json')
    if path.exists():raise SystemExit('preserve exact text regression receipt')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ExactTextTests))
    receipt=dict(schema='prime-large-rational-output-regression-v1',invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1,tests=result.testsRun,
        failures=len(result.failures),errors=len(result.errors),seconds=time.monotonic()-started,
        operations=PM.operations+CM.operations)],scientific_source_or_norms_evaluated=False,
        python_integer_decimal_limit_changed=False)
    path.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
    raise SystemExit(0 if result.wasSuccessful() else 1)
