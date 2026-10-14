"""New dense synthetic regressions only; no selected source or norm study."""
from copy import deepcopy
import json
from pathlib import Path
import time
import unittest

import floor_residual_capacity_045 as C
import floor_residual_interval_044 as ORIGINAL_INTERVAL
import check_floor_residual_arguments_044 as ORIGINAL_CHECK

WORK = []


def dense(maximum, name='dense_capacity_toy'):
    return dict(id=name, constant='1', steps=[],
                coefficients=[dict(n=n, value=str(n)) for n in range(2, maximum+1)])


class CapacityRecoveryTests(unittest.TestCase):
    def test_old_instances_stay_unchanged_and_other_limits_stay_active(self):
        self.assertEqual(ORIGINAL_INTERVAL.MAX_SUPPORT, 2048)
        self.assertEqual(ORIGINAL_CHECK.MAX_SUPPORT, 2048)
        self.assertEqual(C.INTERVAL.MAX_SUPPORT, 3072)
        self.assertEqual(C.CHECK.MAX_SUPPORT, 3072)
        self.assertEqual(C.CHECK.MAX_RESULT_BITS, ORIGINAL_CHECK.MAX_RESULT_BITS)
        self.assertEqual(C.INTERVAL.MAX_INTEGER_BITS, ORIGINAL_INTERVAL.MAX_INTEGER_BITS)
        for backend in (C.INTERVAL.validate_program, C.CHECK.verify_program):
            with self.assertRaises(ValueError):
                backend(dense(3074))
            bad = dense(2)
            bad['coefficients'][0]['n'] = 4097
            with self.assertRaises(ValueError):
                backend(bad)

    def test_dense_norm_has_independent_replay_and_rejects_changed_source(self):
        program = dense(2052)
        with self.assertRaises(ValueError):
            ORIGINAL_CHECK.verify_program(program)
        meter = C.INTERVAL.Meter(cap=100_000_000)
        certificate = C.INTERVAL.certify(program, H=16, precision=192, meter=meter,
                                         kernel=C.INTERVAL.JordanKernel())
        replay = C.CHECK.Meter(cap=100_000_000)
        checked = C.CHECK.verify_norm(program, certificate, meter=replay)
        self.assertTrue(checked['verified'])
        self.assertTrue(checked['all_domain_included'])
        self.assertFalse(checked['convergence_proved'])
        self.assertEqual(certificate['support'], 2051)
        changed = deepcopy(program)
        changed['coefficients'][0]['value'] = '3'
        with self.assertRaises(ValueError):
            C.CHECK.verify_norm(changed, certificate, meter=replay)
        WORK.extend([meter.operations, replay.operations])

    def test_dense_refinement_keeps_unit_indicator_and_signed_identity(self):
        meter = C.CHECK.Meter(cap=100_000_000)
        certificate = C.CHECK.verify_family_refinement(dense(1026, 'toy_parent'),
                                                       dense(2052, 'toy_child'), 2, '-1', meter=meter)
        forcing = certificate['forcing_program']
        self.assertEqual(forcing['constant'], '1')
        self.assertEqual(forcing['steps'], [dict(q=2, value='-1')])
        self.assertTrue(certificate['signed_cross_preserved'])
        self.assertFalse(certificate['growing_family_convergence_proved'])
        self.assertGreater(len(forcing['coefficients'])+len(forcing['steps']), 2048)
        WORK.append(meter.operations)


if __name__ == '__main__':
    path = Path(__file__).with_name('floor_residual_capacity_045_development.json')
    if path.exists():
        raise SystemExit('retain prior focused receipt')
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(CapacityRecoveryTests))
    receipt = dict(schema='floor-capacity-recovery-tests-v1', invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1, tests=result.testsRun,
        failures=len(result.failures), errors=len(result.errors),
        elapsed_seconds=time.monotonic()-started, operations=sum(WORK))],
        scope='new dense synthetic support and full certificate/refinement regressions; no actual candidates')
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
