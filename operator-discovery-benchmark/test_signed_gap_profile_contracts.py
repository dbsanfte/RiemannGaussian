"""Exact root schedules, free constants, full arithmetic and analytical scopes."""
import unittest
from fractions import Fraction as Q
import signed_gap_profile_grammar as g
from signed_gap_profile_analytic import difference_certificate,growth
from check_signed_gap_profiles import parameters,data,minimums,inference
from check_signed_control import independent_inverse


def template(schedule=None,law=None,L='0'):
    return {'arithmetic_model':'inverse_one','exponent_schedule':schedule or {'kind':'power','power':'1'},'constant_law':law or {'kind':'constant'},'log_power':L,'fitted_coefficient':'1'}


class Contracts(unittest.TestCase):
    def test_complete_actual_energy_independently_factor_derived(self):
        d=g.arithmetic([2,4,8,16]);mu,_=independent_inverse(d['cutoff']);self.assertEqual(d['rows'],data(mu,[2,4,8,16]))

    def test_square_cube_and_sixth_root_schedules(self):
        for s,q,X,root in [({'kind':'power','power':'1'},2,729,27),({'kind':'power','power':'1/2'},8,1000,10),({'kind':'factorial'},3,4096,4)]:self.assertEqual(g.evaluate(template(s),X,q)['root_ceiling'],root)

    def test_huge_denominator_keeps_exact_semantics(self):
        p=template({'kind':'fixed','epsilon':str(Q(1,10**100))});r=g.evaluate(p,8192,3);self.assertEqual(r['root_ceiling'],2);self.assertEqual(r,parameters(p,8192,3))

    def test_constant_and_exponent_are_independent(self):
        s={'kind':'power','power':'1/3'}
        for law in [{'kind':'constant'},{'kind':'factorial'},{'kind':'exponential','power':'2'},{'kind':'denominator_power','power':'1/6'}]:
            p=template(s,law);r=g.evaluate(p,1024,6);self.assertEqual(r['epsilon'],'1/2');self.assertEqual(r,parameters(p,1024,6))

    def test_unseen_free_constant_is_not_fit_from_final(self):
        p=template(law={'kind':'free_per_level'});p.pop('fitted_coefficient');p['fitted_constants']={'2':'1'};self.assertTrue(g.evaluate(p,4096,7)['missing']);self.assertEqual(g.evaluate(p,4096,2)['C'],'1')

    def test_noncofinal_fixed_schedule_not_RH_certificate(self):
        c=g.family_certificate(template({'kind':'fixed','epsilon':'1/6'}));self.assertTrue(c['admitted']);self.assertFalse(c['RH_if_global_half_gap'])

    def test_zero_root_growth_and_generic_inverse_rejected(self):
        self.assertFalse(g.family_certificate(template({'kind':'power','power':'0'}))['admitted']);p=template();p['arithmetic_model']='generic_inverse';self.assertFalse(g.family_certificate(p)['admitted'])

    def test_factorial_resource_limit_is_missing_not_semantic_cap(self):
        p=template({'kind':'factorial'});self.assertTrue(g.evaluate(p,8192,10**100)['missing']);self.assertFalse(g.schedule_certificate(p['exponent_schedule'])['semantic_denominator_cap'])

    def test_logarithmic_fractional_power_exact(self):
        p=template(L='1/6');r=g.evaluate(p,4096,3);self.assertEqual(r['log_ceiling'],2);self.assertEqual(r,parameters(p,4096,3))

    def test_anonymous_minimum_table_independent(self):
        self.assertEqual(g.min_response([3,4,5]),minimums([3,4,5]))

    def test_sparse_estimate_is_discovered_and_generically_certified(self):
        rows=g.min_response([4,5,6,7,8]);f=g.infer_polynomial(rows);self.assertEqual(f['retained_fits'],inference(rows,f['feature_dictionary'],4));self.assertTrue(difference_certificate(f['selected']['terms'])['admitted']);self.assertFalse(f['selected']['expected_formula_supplied'])

    def test_unanticipated_polynomial_supported(self):
        rows=[{'dimension':m,'mass':j,'anonymous_response':1+m*j} for m in [3,4,5] for j in range(m+1)];f=g.infer_polynomial(rows);self.assertEqual(f['selected']['exact_squared_residual'],'0');self.assertFalse(difference_certificate(f['selected']['terms'])['admitted'])

    def test_shifted_antiderivative_rejected_by_boundary(self):
        self.assertFalse(difference_certificate([[1,0,'1/6'],[2,0,'-1/2'],[3,0,'1/3'],[0,0,'1']])['admitted'])

    def test_growing_constants_can_still_force_simple_zeros(self):
        for r in ['1/6','1/3','1/2']:
            c=growth(template(law={'kind':'power','power':r}));self.assertTrue(c['would_force_simple_critical_zeros_if_global_bound_proved']);self.assertFalse(c['is_claim_about_actual_zero_multiplicities'])

    def test_fast_constants_do_not_impose_tested_finite_multiplicity_cap(self):
        for law in [{'kind':'exponential','power':'1'},{'kind':'factorial'},{'kind':'free_per_level'}]:self.assertIsNone(growth(template(law=law))['conditional_critical_zero_multiplicity_upper'])

    def test_exponent_speed_changes_constant_scope(self):
        p=template({'kind':'power','power':'1/6'},{'kind':'power','power':'1/3'});self.assertEqual(growth(p)['conditional_critical_zero_multiplicity_upper'],2)

    def test_log_loss_and_factorial_gaps_are_labelled(self):
        p=template({'kind':'factorial'},{'kind':'denominator_power','power':'1'},L='1');c=growth(p);self.assertEqual(c['conditional_critical_zero_multiplicity_upper'],2);self.assertTrue(c['reciprocal_pole_power_is_limit_allowing_subpolynomial_factors'])

    def test_finite_observation_keeps_exact_signed_gap(self):
        d=g.arithmetic([16,32]);p=g.fit(template(),d,[2,3]);rows=g.observations(p,d,[2,3])
        for row in rows:self.assertEqual(Q(row['exact_signed_nullspace_gap']),Q(row['parameters']['D'])*row['Q_4X']-row['actual_signed_defect']);self.assertFalse(row['global_signed_bound_proved'])


if __name__=='__main__':unittest.main()
