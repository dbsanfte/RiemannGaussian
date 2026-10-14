"""Synthetic exact calibrations and adversarial cutoff-work audits."""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import time
import unittest

import core_cutoff_work_search as PRODUCER
import core_cutoff_bound_planner as PLANNER
import check_core_cutoff_work_search as CHECK
from potential_candidate_language import Meter

START = time.monotonic()
WORK = Meter(50000000, deadline=START+180, max_cells=2000000)


def fixture():
    """Hand-written frozen-ancestry fixture; no prior search is rerun."""
    alpha, gamma = Q(1, 24), Q(1, 2)
    modes = [dict(name='B', coefficient='beta', p=2, q=0, positive_shift='1/3'),
        dict(name='U', coefficient='-beta', p=1, q=1, positive_shift='1/3'),
        dict(name='V', coefficient='-beta', p=1, q=0, positive_shift=None),
        dict(name='power', coefficient='-R_u', p=0, q=1, positive_shift='1/3')]
    cases = []
    for mode in modes:
        p, q = mode['p'], mode['q']; terms = []
        for total in range(64):
            for a in range(total+1):
                b = total-a; WORK.charge(5)
                if a*alpha+b*gamma >= 1: continue
                coefficient = (comb(p+a-1, a) if p else int(a == 0))*(comb(q+b-1, b) if q else int(b == 0))
                if coefficient: terms.append(dict(a=a, b=b, coefficient=str(coefficient)))
        cases.append(dict(mode=mode, program=dict(alpha=str(alpha), gamma=str(gamma), p=p, q=q, terms=terms)))
    source = dict(id=0, alpha=str(alpha), gamma=str(gamma), cases=cases,
        component_count=sum(len(c['program']['terms']) for c in cases), full_signed_bound_proved=False, RH_proved=False)
    bindings = [dict(parent_obligation_id='original_'+str(i), inherited_binding=dict(transport_program=dict(id=i, mesh_power='1/2')),
        whole_signed_bound_proved=False, RH_proved=False) for i in range(144)]
    parent = dict(schema='core-weighted-height-feedback-v1', status='open', selected_source_representation=source,
        generated_bound_obligations=bindings, retained_original_proof_frontier=[dict(id='full_core', status='open')],
        next_search_tasks=[dict(target_id='actual_signed_core', status='open')], whole_signed_bound_proved=False, RH_proved=False)
    join = CHECK._source(parent, WORK)
    terms = [t for t in join['collected_terms'] if t['powers'][2] == 1 and t['powers'][3] >= 2 and
        all(t['powers'][i] == 0 for i in (1, 4, 5, 6, 7))]
    old = []; weighted = []
    for term in terms:
        p, m = term['powers'][0], term['powers'][3]; ident = 'centered_A'+str(p)+'_E'+str(m)
        previous = dict(target_id=ident, p=p, m=m, theta='2/3', source_term=term, component_bound_proved=False)
        old.append(previous)
        target = dict(target_id=ident, p=p, m=m, theta='2/3', source_term=term, inherited_component_bound_proved=False,
            lines=[], selected_line=None, low_obligation=None, new_source_payment=False,
            centering=dict(kind='analytic_residue', M='A(theta)^p*E(theta)^m',
                centered_coefficient='K*A^p*E^m-(M/theta)*J_theta', retained_opposite_drift='source_coefficient*(M/theta)*J_theta',
                ordinary_moment_established_by_inherited_prefix_rule=Q(m-1, m) < Q(2, 3), ordinary_prefix_power=str(Q(m-1, m)),
                ordinary_convergence_required_for_this_route=False, unit_J_theta_1='1',
                continuous_small_x_tail='-(M/theta)*x^theta on 0<x<1', pole_at_1_removed_in_complete_E=True),
            source_head_identity=dict(domain='every integer 1<=n<=U', expression='(A^p*E^m)(n)', scalar='c^m',
                coefficient=dict(atom='One' if m >= p else 'mu', convolution_power=abs(m-p)), zero_power='delta',
                derivation='mu*One=delta on n<=U and E(n)=c', supplies_full_Gram_bound=False))
        if m == 3:
            sigma, theta, kappa, fraction = Q(9, 20), Q(2, 3), Q(2, 9), Q(1, 4)
            branches = []
            for j in range(m+1):
                r = p+j; height = theta-sigma-1+j*(1-2*sigma)+(j-2)*sigma*int(j >= 2)
                branches.append(dict(j=j, r=r, support_U_power=r,
                    coefficient_envelope=dict(multiplier=str(3**j), divisor_order=r, constant_polynomial=r == 0),
                    height_power=str(height), weight_U_power=str(r*(1-2*sigma))))
            epsilon = fraction*min(-Q(b['height_power']) for b in branches)
            tau = max([Q(b['r'])/kappa for b in branches]+[Q(b['weight_U_power'])/(-Q(b['height_power'])-epsilon) for b in branches])
            replay = [dict(j=b['j'], length_slack=str(tau*kappa-b['r']), tail_height_power=str(Q(b['height_power'])+epsilon),
                tail_U_power=str(Q(b['weight_U_power'])+tau*(Q(b['height_power'])+epsilon))) for b in branches]
            generic = 2*(p+m)*(1-sigma); error = 2*(p+m)*(1-theta); goal = (1-2*sigma)/alpha
            plan = dict(kappa=str(kappa), epsilon_fraction=str(fraction), epsilon=str(epsilon), tau=str(tau), branches=replay,
                within_tau_cap=True, high_U_power=str(max(Q(b['tail_U_power']) for b in replay)), high_energy_X_power=str(2*sigma-1),
                required_low_U_power=str(goal), generic_low_U_power=str(generic), generic_low_energy_X_power=str(2*sigma-1+alpha*generic),
                integer_error_U_power=str(error), integer_error_X_power=str(-1+alpha*error), high_auxiliary_proved=True,
                generic_complete_component_proved=False, low_obligation_status='open_actual_Mobius_bound')
            target['lines'] = [dict(sigma=str(sigma), branches=branches, plans=[plan], selected_plan=0, failed_premises=[])]
            target['selected_line'] = 0
            target['low_obligation'] = dict(kind='complete_zeta_weighted_low_Mellin_Gram',
                parameters=dict(p=p, m=m, theta=str(theta), sigma=str(sigma), alpha=str(alpha)),
                source_weights=dict(A='mu(n)*1_(n<=U)', c='sum_(n<=U)mu(n)/n', T='c*delta-A', E='delta+One*T', B_j='A^p*T^j'),
                height=dict(prefactor='2', U_power=str(tau), interval='abs(t)<H'), measure='dt/(2*pi)',
                kernel='abs(zeta(s+1-theta)/s)^2*zeta(s)^j*conj(zeta(s)^k)', finite_polynomial_product='B_j(s)*conj(B_k(s))',
                matrix_entries=[dict(j=j, k=k, contraction=str(comb(m, j)*comb(m, k))) for j in range(m+1) for k in range(m+1)],
                integer_pairs='all ordered d,e, with actual signed B_j(d)*B_k(e)', unweighted_Gaussian_substitution_allowed=False,
                diagonal_only_allowed=False, required_upper=dict(constant='C_low', U_power=str(goal), log_degree=0,
                    quantifier='every integer U>=1, one fixed finite C_low independent of U,X,N'),
                status='open_actual_Mobius_bound', generic_fallback_U_power=str(generic), complete_cross_terms_retained=True)
        weighted.append(target)
    parent['auxiliary_bound_targets'] = old; parent['weighted_height_targets'] = weighted
    parent['complete_source_reduction'] = dict(inherited_complete_signed_join=join, bindings=bindings,
        transport_error_retained='-e', whole_join_cross_terms_retained=True,
        common_horizon='N=4X-1 for BOTH blocks; same coefficients and cutoffs', new_paid_components=[])
    parent['proof_dependencies'] = [dict(id='reviewed', status='reviewed_and_imported', depends_on=[]),
        dict(id='complete_signed_complement', status='open', depends_on=['reviewed']),
        dict(id='actual_signed_core', status='open', depends_on=['complete_signed_complement'])]
    return parent


def _gadd(left, right): return left[0]+right[0], left[1]+right[1]
def _gmul(left, right): return left[0]*right[0]-left[1]*right[1], left[0]*right[1]+left[1]*right[0]
def _gpower(value, n):
    out = (Q(1), Q(0))
    for _ in range(n): out = _gmul(out, value)
    return out
def _gscale(value, scalar): return value[0]*scalar, value[1]*scalar
def evaluate(rows, values):
    out = (Q(0), Q(0))
    for row in rows:
        value = (Q(row['coefficient']), Q(0))
        for name in row['monomial']:
            if name.endswith('bar'):
                a, b = values[name[:-3]]; factor = (a, -b)
            else: factor = values[name]
            value = _gmul(value, factor)
        out = _gadd(out, value)
    return out


class IndependentCutoffWorkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent = fixture(); cls.result = PRODUCER.search(cls.parent, WORK)

    def target(self, value=None): return (self.result if value is None else value)['targets'][0]
    def selected(self, value=None):
        target = self.target(value); return target['programs'][target['selected_program']]
    def reject(self, mutate):
        result = deepcopy(self.result); mutate(result)
        with self.assertRaises((ValueError, KeyError, TypeError, IndexError)):
            CHECK.verify_search(self.parent, result, WORK)
    def reject_parent(self, mutate):
        parent = deepcopy(self.parent); mutate(parent)
        with self.assertRaises((ValueError, KeyError, TypeError, IndexError)):
            CHECK.verify_search(parent, PRODUCER.search(parent, WORK), WORK)

    def test_complete_compiler_and_source_degree23(self):
        audit = CHECK.verify_search(self.parent, self.result, WORK)
        self.assertEqual(audit['targets'], 1); self.assertEqual(audit['transition_programs'], 2)
        self.assertEqual(audit['bound_routes'], 11); self.assertEqual(audit['closed_low_goals'], 0)
        self.assertEqual(len(self.parent['weighted_height_targets']), 22)
        self.assertEqual(len(self.result['inherited_bindings']), 144)
        self.assertEqual(max(t['a'] for t in self.parent['selected_source_representation']['cases'][0]['program']['terms']), 23)
        self.assertFalse(audit['whole_signed_bound_proved'])

    def test_head_enumeration_normal_form_not_supplied_winner(self):
        for p, m in [(0, 2), (2, 3), (4, 2), (3, 3)]:
            got = PRODUCER.head_search(p, m, WORK); expected = CHECK.head_trials(p, m, WORK)
            self.assertEqual(got, expected); self.assertEqual(len(got['matched_indices']), 1)
            match = got['trials'][got['matched_indices'][0]]
            self.assertEqual(match['c_power'], m); self.assertEqual(match['multiplier'], '1')
            self.assertEqual(got['normal_form'], [dict(c_power=m, One_power=m-p, coefficient='1')])
            self.assertTrue(got['zero_power_atom_deduplicated'])
        self.assertEqual(len(self.target()['head_search']['trials']), 396)

    def test_generic_gaussian_rational_transition_all_three_signs(self):
        values = dict(A=(Q(1, 2), Q(1)), E=(Q(2), Q(-1, 3)), c=(Q(2, 3), Q(0)),
            D=(Q(-1), Q(1, 2)), z=(Q(1, 3), Q(-1)), a=(Q(1, 4), Q(0)),
            b=(Q(2), Q(1, 3)), v=(Q(-2), Q(0)))
        for p, m, head in [(0, 2, False), (2, 3, True), (4, 2, True)]:
            transition = PRODUCER.compile_transition(p, m, head, WORK)
            self.assertTrue(CHECK.verify_transition(p, m, head, transition, WORK)['verified'])
            old = _gmul(_gpower(values['A'], p), _gpower(values['E'], m))
            if head: old = _gadd(old, _gscale(_gmul(_gpower(values['c'], m), values['D']), -1))
            for sign in (-1, 0, 1):
                newA = _gadd(values['A'], _gscale(values['b'], sign))
                newE = _gadd(values['E'], _gscale(_gmul(values['z'], _gadd(values['a'], _gscale(values['b'], -1))), sign))
                newc = _gadd(values['c'], _gscale(values['a'], sign))
                newD = _gadd(values['D'], _gmul(values['v'], values['b']))
                child = _gmul(_gpower(newA, p), _gpower(newE, m))
                if head: child = _gadd(child, _gscale(_gmul(_gpower(newc, m), newD), -1))
                inc = (Q(0), Q(0)); work = (Q(0), Q(0))
                for i in range(3):
                    inc = _gadd(inc, _gscale(evaluate(transition['increment_sectors'][i], values), sign**i))
                    work = _gadd(work, _gscale(evaluate(transition['work_sectors'][i], values), sign**i))
                self.assertEqual(inc, _gadd(child, _gscale(old, -1)))
                self.assertEqual(work, (child[0]**2+child[1]**2-old[0]**2-old[1]**2, Q(0)))

    def test_zero_mu_branch_moves_finite_head_and_no_sector_has_sign(self):
        zero = self.selected()['transition']['increment_sectors'][0]
        self.assertEqual(zero, [dict(monomial=['b', 'c', 'c', 'c', 'v'], coefficient='-1')])
        self.assertTrue(self.selected()['transition']['work_sectors'][0])
        # For the inverse-divisor head, mu(4)=0 but (mu*mu)(4)=1.
        mu = {1:1, 2:-1, 4:0}
        v4 = sum(mu[d]*mu[4//d] for d in (1, 2, 4))
        self.assertEqual(v4, 1)
        inverse = PRODUCER.compile_transition(4, 2, True, WORK)
        self.assertEqual(inverse['increment_sectors'][0], [dict(monomial=['b', 'c', 'c', 'v'], coefficient='-1')])
        self.assertTrue(self.selected()['missing_work']['no_sector_sign_assumed'])

    def test_exact_kernel_constants_small_x_and_head_payment(self):
        head = self.target()['head_bound']
        self.assertEqual(head['kernel_global_norm_constant'], '100/13')
        self.assertEqual(head['global_squared_norm_constant'], '2560000/1573')
        self.assertEqual((head['global_U_power'], head['global_log_degree']), ('11/10', 0))
        self.assertEqual(head['centered_prefix_constant'], '12')
        self.assertEqual(head['physical_energy_X_power'], '-11/12')
        self.assertTrue(head['opposite_drift_retained']); self.assertTrue(head['full_unit_and_x_below_one_retained'])
        self.assertEqual(head['target_absorption'], dict(proved=True, multiplier='1', gap='13/10'))
        delta = CHECK.head_bound(3, 3, Q(3, 4), Q(1, 3), Q(1, 3), Q(1))
        self.assertEqual(delta, PRODUCER.head_certificate(3, 3, Q(3, 4), Q(1, 3), Q(1, 3), Q(1)))
        self.assertEqual((delta['global_U_power'], delta['global_log_degree'], delta['physical_energy_X_power']), ('0', 0, '-1'))

    def test_strict_log_absorption_and_equal_power_only_boundary(self):
        for power, logs, goal in [(Q(1), 2, Q(1)), (Q(2), 0, Q(1)), (Q(1), 0, Q(1)), (Q(1), 2, Q(3, 2))]:
            self.assertEqual(CHECK.absorption(power, logs, goal), PRODUCER.absorb(power, logs, goal))
        self.assertFalse(CHECK.absorption(Q(1), 2, Q(1))['proved'])
        self.assertTrue(CHECK.absorption(Q(1), 0, Q(1))['proved'])
        self.assertEqual(CHECK.absorption(Q(1), 2, Q(3, 2))['multiplier'], '36')

    def test_automatic_zero_sector_kernel_and_nonlinear_recovery(self):
        search = self.selected()['bound_search']; control = search['zero_sector_control']
        self.assertEqual((control['squared_norm_constant'], control['root_U_power']), ('6400/13', '-9/20'))
        route = search['routes'][search['selected_route']]
        self.assertEqual((route['method'], route['aggregation']), ('pay_zero_sector_by_energy_feedback', 'prefix'))
        self.assertEqual(route['recurrence']['feedback_envelope'], dict(U_power='11/10', log_degree='0'))
        self.assertEqual(route['nonnegative_cost'], dict(U_power='21/10', log_degree='0'))
        self.assertEqual(route['forcing']['R_q']['sectors'], [1, 2])
        self.assertEqual(route['status'], 'conditional_open_signed_work')
        self.assertFalse(search['goal_proved']); self.assertFalse(route['target_assumed_in_proof'])
        self.assertEqual(search['next_bound_targets'], [route['forcing']])

    def test_kernel_recognition_rejects_unbounded_state_and_pays_delta_zero(self):
        for rows, degree in [([dict(monomial=['A'], coefficient='1')], 1),
                             ([dict(monomial=['z'], coefficient='1')], 2)]:
            expected = CHECK.finite_shift_control(rows, degree, Q(2, 3), Q(9, 20), WORK)
            self.assertEqual(expected, PLANNER.finite_shift_control(rows, degree, Q(2, 3), Q(9, 20), WORK))
            self.assertFalse(expected['available'])
        rows = [dict(monomial=['b', 'c', 'v'], coefficient='-2')]
        zero = CHECK.finite_shift_control(rows, 0, Q(2, 3), Q(9, 20), WORK)
        self.assertTrue(zero['identically_zero']); self.assertEqual(zero['squared_norm_constant'], '0')
        self.assertEqual(zero, PLANNER.finite_shift_control(rows, 0, Q(2, 3), Q(9, 20), WORK))

    def test_summation_resonance_and_sublinear_maximum_without_target_assumption(self):
        for pair in [(Q(-1), Q(0)), (Q(-1), Q(1, 2)), (Q(-2), Q(3)), (Q(1, 5), Q(2))]:
            encoded = CHECK._envelope(pair)
            self.assertEqual(CHECK._envelope(CHECK._sum_envelope(pair)), PLANNER.summation(encoded))
        self.assertEqual(CHECK._sum_envelope((Q(-1), Q(0))), (Q(0), Q(1)))
        # Endpoint forcing can hide an arbitrarily large intermediate peak.
        forcing = [Q(100), Q(-100)]
        self.assertEqual(sum(forcing), 0); self.assertEqual(max(forcing[0], sum(forcing)), 100)
        rule = PLANNER.maximal_energy_rule(dict(U_power='-1', log_degree='0'),
            dict(U_power='0', log_degree='0'), dict(U_power='0', log_degree='0'), Q(1, 2))
        self.assertEqual(rule['feedback_envelope'], dict(U_power='0', log_degree='2'))
        self.assertFalse(rule['target_assumed_in_proof'])

    def test_generic_planner_can_prove_known_goal_or_leave_higher_degree_unpaid(self):
        program = deepcopy(self.selected()); head = deepcopy(self.target()['head_bound'])
        for degree, goal, generic in [(1, Q(6), Q(5)), (3, Q(12, 5), Q(11, 2))]:
            head['convolution_power'] = degree
            result = PLANNER.search_bounds(program, head, Q(2, 3), Q(9, 20), goal, generic, WORK)
            audit = CHECK.verify_bound_search(program, head, Q(2, 3), Q(9, 20), goal, generic, result, WORK)
            self.assertEqual(audit['goal_proved'], degree == 1)
            if degree == 3:
                self.assertTrue(all(r['status'] == 'unpaid_auxiliary_cost' for r in result['routes'] if r['method'] == 'pay_zero_sector_by_energy_feedback'))

    def test_inverse_head_must_be_repartitioned_before_zero_sector_payment(self):
        program = deepcopy(self.selected()); certificate = deepcopy(self.target()['head_bound'])
        certificate['atom'] = 'mu'; certificate['convolution_power'] = 2
        program['transition'] = PRODUCER.compile_transition(4, 2, True, WORK)
        result = PLANNER.search_bounds(program, certificate, Q(2, 3), Q(9, 20), Q(12, 5), Q(6), WORK)
        self.assertTrue(CHECK.verify_bound_search(program, certificate, Q(2, 3), Q(9, 20), Q(12, 5), Q(6), result, WORK)['verified'])
        self.assertFalse(result['zero_sector_control']['available'])
        self.assertTrue(all(r['method'] != 'pay_zero_sector_by_energy_feedback' for r in result['routes']))
        bad = deepcopy(result); bad['zero_sector_control']['available'] = True
        with self.assertRaises(ValueError):
            CHECK.verify_bound_search(program, certificate, Q(2, 3), Q(9, 20), Q(12, 5), Q(6), bad, WORK)

    def test_all_integer_prefix_dyadic_partial_and_stronger_consecutive_scope(self):
        routes = self.selected()['bound_search']['routes']
        prefix = next(r for r in routes if r.get('aggregation') == 'prefix')
        dyadic = next(r for r in routes if r.get('aggregation') == 'dyadic_max_partial')
        consecutive = next(r for r in routes if r.get('aggregation') == 'consecutive')
        self.assertIn('EVERY integer', dyadic['forcing']['quantifier'])
        self.assertFalse(dyadic['endpoint_samples_suffice'])
        self.assertEqual(prefix['relation_to_original_goal'], 'equivalent goal up to paid costs')
        self.assertEqual(consecutive['relation_to_original_goal'], 'optional stronger sufficient requirement; not equivalent')
        self.assertEqual(dyadic['dyadic_to_prefix_constant'], '11/6')

    def test_missing_head_trials_match_or_program_rejected(self):
        for mutate in (lambda r:self.target(r)['head_search']['trials'].pop(),
                       lambda r:self.target(r)['head_search'].update(matched_indices=[]),
                       lambda r:self.target(r)['head_search'].update(identity_scope='global identity'),
                       lambda r:self.target(r)['programs'].pop(),
                       lambda r:self.target(r).update(selected_program=0)):
            self.reject(mutate)

    def test_omitted_zero_sector_signed_cross_and_bad_conjugate_rejected(self):
        for mutate in (lambda r:self.selected(r)['transition']['increment_sectors'].__setitem__(0, []),
                       lambda r:self.selected(r)['transition']['work_sectors'][1].pop(),
                       lambda r:self.selected(r)['transition']['child'][0].update(coefficient='0'),
                       lambda r:self.selected(r)['transition']['work_sectors'][2][0].update(monomial=['unknownbar']),
                       lambda r:self.selected(r)['transition']['increment_sectors'].pop(1)):
            self.reject(mutate)

    def test_false_low_payment_closure_and_nonlinear_target_assumption_rejected(self):
        for mutate in (lambda r:self.selected(r).update(component_bound_proved=True),
                       lambda r:self.selected(r).update(new_source_payment=True),
                       lambda r:self.selected(r)['bound_search'].update(goal_proved=True),
                       lambda r:self.selected(r)['bound_search']['routes'][4]['recurrence'].update(target_assumed_in_proof=True),
                       lambda r:r.update(whole_signed_bound_proved=True),
                       lambda r:r.update(RH_proved=True)):
            self.reject(mutate)

    def test_costs_shell_child_length_and_finite_base_tampers_rejected(self):
        for mutate in (lambda r:self.target(r)['head_bound'].update(kernel_global_norm_constant='1'),
                       lambda r:self.selected(r)['moving_height_shell'].update(extended_kappa='1/4'),
                       lambda r:self.selected(r)['moving_height_shell']['parts'].pop(),
                       lambda r:self.selected(r)['initial_low_norm'].update(upper='1'),
                       lambda r:self.selected(r)['bound_search']['zero_sector_control'].update(squared_norm_constant='0')):
            self.reject(mutate)

    def test_endpoint_only_quantifier_sector_abs_values_and_dropped_next_leaf_rejected(self):
        for mutate in (lambda r:self.selected(r)['bound_search']['routes'][5].update(endpoint_samples_suffice=True),
                       lambda r:self.selected(r)['bound_search']['routes'][4]['forcing'].update(quantifier='terminal endpoint only'),
                       lambda r:self.selected(r)['bound_search']['routes'][4]['forcing']['R_q'].update(sectors=[1]),
                       lambda r:self.selected(r)['bound_search']['routes'][4]['forcing'].update(sector_signs_assumed=True),
                       lambda r:self.selected(r)['bound_search'].update(next_bound_targets=[])):
            self.reject(mutate)

    def test_source_inverse_unit_drift_transport_and_ordinary_convergence_rejected(self):
        def weighted(parent): return next(t for t in parent['weighted_height_targets'] if t['m'] == 3)
        for mutate in (lambda p:p['selected_source_representation']['cases'][0]['program']['terms'].pop(0),
                       lambda p:p['complete_source_reduction'].update(transport_error_retained='0'),
                       lambda p:weighted(p)['centering'].update(unit_J_theta_1='0'),
                       lambda p:weighted(p)['centering'].update(ordinary_moment_established_by_inherited_prefix_rule=True),
                       lambda p:weighted(p)['centering'].pop('retained_opposite_drift'),
                       lambda p:weighted(p)['low_obligation']['matrix_entries'].pop()):
            self.reject_parent(mutate)

    def test_dropped_binding_source_target_cycle_and_open_dependent_proof_rejected(self):
        for mutate in (lambda p:p['generated_bound_obligations'].pop(),
                       lambda p:p['weighted_height_targets'].pop(),
                       lambda p:p['proof_dependencies'][0].update(depends_on=['actual_signed_core']),
                       lambda p:p['proof_dependencies'][2].update(status='proved')):
            self.reject_parent(mutate)
        self.reject(lambda r:r['inherited_bindings'].pop())

    def test_selected_inherited_tau_epsilon_length_and_low_scope_rejected(self):
        def plan(p):
            target = next(t for t in p['weighted_height_targets'] if t['m'] == 3)
            return target['lines'][0]['plans'][0]
        for mutate in (lambda p:plan(p).update(kappa='1/4'), lambda p:plan(p).update(tau='1'),
                       lambda p:plan(p).update(epsilon='1'), lambda p:plan(p).update(required_low_U_power='1'),
                       lambda p:plan(p)['branches'].pop(0)):
            self.reject_parent(mutate)

    def test_feedback_retains_all_old_obligations_and_exposes_actual_open_signed_leaf(self):
        feedback = PRODUCER.feedback(self.parent, self.result, 'prior.json', 'immutable/search.json')
        self.assertTrue(CHECK.verify_feedback(self.parent, self.result, feedback, 'prior.json', 'immutable/search.json', WORK)['verified'])
        self.assertEqual(feedback['next_search_tasks'][0]['target_id'], 'actual_signed_core')
        self.assertEqual(len(feedback['weighted_height_targets']), 22)
        self.assertEqual(len(feedback['generated_bound_obligations']), 144)
        self.assertEqual(feedback['next_search_tasks'][1]['next_bound_targets'][0]['R_q']['sectors'], [1, 2])
        for mutate in (lambda f:f['next_search_tasks'].pop(0), lambda f:f['auxiliary_bound_targets'].pop(),
                       lambda f:f['weighted_height_targets'].pop(), lambda f:f['next_search_tasks'][1].update(next_bound_targets=[]),
                       lambda f:f.update(RH_proved=True)):
            bad = deepcopy(feedback); mutate(bad)
            with self.assertRaises(ValueError): CHECK.verify_feedback(self.parent, self.result, bad, 'prior.json', 'immutable/search.json', WORK)

    def test_no_arithmetic_observations_or_claim_supplied_identity_was_discovered(self):
        self.assertFalse(self.result['diagnostic_spec']['executed'])
        self.assertFalse(self.result['supplied_rules']['uniform_signed_work_proved'])
        self.assertEqual(self.result['supplied_rules']['arithmetic_head'], 'mu*One=delta for n<=U')
        self.assertEqual(self.result['model_calls_in_search'], 0)
        self.reject(lambda r:r['diagnostic_spec'].update(executed=True))
        self.reject(lambda r:r['supplied_rules'].update(uniform_signed_work_proved=True))


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_cutoff_work_search operations='+str(WORK.operations)+
          ' elapsed_seconds='+format(time.monotonic()-START, '.6f'))


if __name__ == '__main__': unittest.main()
