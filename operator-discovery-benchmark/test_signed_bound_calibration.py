"""Contract checks for the blind generic signed-bound workflow."""
from fractions import Fraction as Q
from pathlib import Path
import tempfile
import unittest
import signed_bound_calibration as c


class CalibrationContracts(unittest.TestCase):
    def signed_spec(self):
        return {'base':4,'weights':[1,1,-1,-1],'mode':'signed','delay':None}

    def fitted(self,spec):
        return next(x for x in c.local_candidates(c.response(spec,256)) if x['base']==spec['base'])

    def test_numeric_fit_and_all_integer_signed_certificate(self):
        spec=self.signed_spec();model=self.fitted(spec);proof=c.certificate(spec,model)
        self.assertTrue(proof['admitted'])
        # Check every residue and non-base-power dimension, not just scale powers.
        data=c.independent_response(spec,8196)
        rows=c.verify_numeric(model,data,list(range(1,2049)))['rows']
        self.assertTrue(all(r['moment_rule_pass'] and r['finite_bound_pass'] for r in rows))
        self.assertEqual(proof['uniform_signed_defect_bound'],'8')

    def test_delayed_control_passes_probe_but_fails_global_rule(self):
        spec={**self.signed_spec(),'mode':'delayed','delay':1024};model=self.fitted(spec)
        self.assertEqual(model['status'],'finite_rule_fit')
        self.assertEqual(model['moment_status'],'finite_rule_fit')
        proof=c.certificate(spec,model)
        self.assertFalse(proof['admitted'])
        self.assertEqual(proof['disposition'],'refuted_global_uniform_defect')
        w=proof['recurrence_counterexample']
        self.assertNotEqual(Q(w['child_value']),Q(w['predicted_child']))
        tested=c.verify_numeric(model,c.independent_response(spec,16388),[2048,3073,4096])
        self.assertTrue(all(not r['global_recurrence_sample_pass'] for r in tested['rows']))

    def test_positive_control_is_not_a_signed_certificate(self):
        spec={**self.signed_spec(),'mode':'positive','weights':[1,1,1,1]}
        proof=c.certificate(spec,self.fitted(spec))
        self.assertFalse(proof['admitted'])
        self.assertEqual(proof['disposition'],'refuted_global_uniform_defect')
        self.assertGreaterEqual(proof['positive_mass_multiplier'],2)

    def test_mutated_moment_rule_rejected_after_freeze(self):
        spec=self.signed_spec();model=self.fitted(spec)
        model['moment_rule']['residues'][1]='-1000000'
        proof=c.certificate(spec,model)
        self.assertFalse(proof['admitted'])
        self.assertEqual(proof['reason'],'learned_moment_coefficients_fail_symbolic_identity')

    def test_digit_regrouping_and_wrong_base(self):
        spec={'base':2,'weights':[1,-1],'mode':'signed','delay':None}
        proof=c.certificate(spec,next(x for x in c.local_candidates(c.response(spec,256)) if x['base']==4))
        self.assertTrue(proof['admitted'])
        self.assertFalse(c.global_digit_agreement(spec,3,[Q(1),Q(-1),Q(0)]))

    def test_complete_freeze_holdout_and_retained_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            result=c.run(Path(tmp)/'run')
            self.assertTrue(result['all_passed'])
            self.assertGreater(result['signed_instances_with_admitted_bound'],0)
            self.assertGreater(result['delayed_control_candidates_with_finite_probe_fit'],0)
            self.assertFalse(result['RH_proved'])
            self.assertFalse(result['actual_global_prime_signed_bound_proved'])
            self.assertTrue(result['every_candidate_missing_or_rejected_or_admitted_record_retained'])
            self.assertTrue(all(c.sha(Path(tmp)/'run'/n)==h for n,h in result['input_sha256'].items()))


if __name__=='__main__':
    unittest.main()
