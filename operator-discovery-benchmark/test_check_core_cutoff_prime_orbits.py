"""Tiny synthetic numeric calibrations and adversarial orbit audits."""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import time
import unittest

from flint import arb, ctx
import core_cutoff_prime_orbits as PRODUCER
import check_core_cutoff_prime_orbits as CHECK
from potential_candidate_language import Meter

START = time.monotonic()
WORK = Meter(50000000, deadline=START+180, max_cells=2000000)
MU = [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0]


def abstract_samples():
    """Arbitrary signed work benchmark, not actual Mellin source data."""
    r = {10:8, 11:1, 13:-1, 14:2, 15:-8}
    records = []
    for q in range(2, 17):
        values = [dict(w1='0', w2=str(r.get(q, 0) if h == 0 else 0), zero='0', shell='0', energy='0') for h in range(7)]
        records.append(dict(q=q, mu=MU[q], mask_old=[True]*7, mask_new=[True]*7, values=values))
    return dict(schema='cutoff-work-samples-v1', start=2, end=16, precision=256, heights=CHECK.HEIGHTS,
        mu=MU, initial_energy=['0']*7, records=records, state={})


def discovery_cases():
    """Exact synthetic rank fixture, independent of source observations."""
    rows = []
    for program in CHECK.program_catalogue():
        for B in (64, 128, 256, 512):
            bits = 1 if program['id'] == 6 else 2 if program['id'] == 9 else 0
            rows.append(dict(program_id=program['id'], B=B, cancellation_bits=bits,
                             nontrivial_partition=program['lane'] != 'fixed'))
    return rows


def symbolic_parent():
    """Complete hand finite-source ancestry, with no arithmetic evaluations."""
    import check_core_cutoff_work_search as OLD_CHECK
    import core_cutoff_work_search as OLD_PRODUCER
    import check_core_weighted_height_search as W
    modes = [dict(name='B', coefficient='beta', p=2, q=0, positive_shift='1/3'),
        dict(name='U', coefficient='-beta', p=1, q=1, positive_shift='1/3'),
        dict(name='V', coefficient='-beta', p=1, q=0, positive_shift=None),
        dict(name='power', coefficient='-R_u', p=0, q=1, positive_shift='1/3')]
    alpha, gamma = Q(1, 24), Q(1, 2); cases = []
    for mode in modes:
        p, q = mode['p'], mode['q']; terms = []
        for total in range(48):
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
        next_search_tasks=[dict(target_id='actual_signed_core', priority=0, status='open')], whole_signed_bound_proved=False, RH_proved=False)
    join = OLD_CHECK._source(parent, WORK)
    terms = [t for t in join['collected_terms'] if t['powers'][2] == 1 and t['powers'][3] >= 2 and
        all(t['powers'][i] == 0 for i in (1, 4, 5, 6, 7))]
    old = []; weighted = []
    for term in terms:
        p, m = term['powers'][0], term['powers'][3]; ident = 'centered_A'+str(p)+'_E'+str(m)
        old.append(dict(target_id=ident, p=p, m=m, theta='2/3', source_term=term, component_bound_proved=False))
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
            sigma, theta, kappa, epsilon, tau = Q(9, 20), Q(2, 3), Q(2, 9), Q(1, 120), Q(45, 2)
            branches = W._branches(p, m, theta, sigma, WORK)
            replay = [dict(j=b['j'], length_slack=str(tau*kappa-b['r']), tail_height_power=str(Q(b['height_power'])+epsilon),
                tail_U_power=str(Q(b['weight_U_power'])+tau*(Q(b['height_power'])+epsilon))) for b in branches]
            plan = dict(kappa=str(kappa), epsilon_fraction='1/4', epsilon=str(epsilon), tau=str(tau), branches=replay,
                within_tau_cap=True, high_U_power='-1/16', high_energy_X_power='-1/10', required_low_U_power='12/5',
                generic_low_U_power='11/2', generic_low_energy_X_power='31/240', integer_error_U_power='10/3',
                integer_error_X_power='-31/36', high_auxiliary_proved=True, generic_complete_component_proved=False,
                low_obligation_status='open_actual_Mobius_bound')
            target['lines'] = [dict(sigma=str(sigma), branches=branches, plans=[plan], selected_plan=0, failed_premises=[])]
            target['selected_line'] = 0; target['low_obligation'] = W._low(p, m, theta, sigma, alpha, plan)
        weighted.append(target)
    parent['auxiliary_bound_targets'] = old; parent['weighted_height_targets'] = weighted
    parent['complete_source_reduction'] = dict(inherited_complete_signed_join=join, bindings=bindings,
        transport_error_retained='-e', whole_join_cross_terms_retained=True,
        common_horizon='N=4X-1 for BOTH blocks; same coefficients and cutoffs', new_paid_components=[])
    parent['proof_dependencies'] = [dict(id='reviewed', status='reviewed_and_imported', depends_on=[]),
        dict(id='complete_signed_complement', status='open', depends_on=['reviewed']),
        dict(id='actual_signed_core', status='open', depends_on=['complete_signed_complement'])]
    target = next(t for t in weighted if t['m'] == 3)
    result = dict(targets=[OLD_PRODUCER.compile_target(target, alpha, WORK)])
    return OLD_PRODUCER.feedback(parent, result, 'synthetic-prior.json', 'synthetic/search.json')


class IndependentPrimeOrbitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 192; cls.producer = PRODUCER.measure(MU, 2, 16, None, WORK)
        ctx.prec = 256; cls.checker = CHECK.measure(MU, 2, 16, None, WORK)
        cls.parent = symbolic_parent(); cls.binding = CHECK.bind_target(cls.parent, WORK)

    def setUp(self): ctx.prec = 256

    def test_independent_trial_factorization_and_complete_unit(self):
        self.assertTrue(CHECK.validate_mu(MU, WORK)['verified'])
        for q, value in [(0, 1), (1, 0), (4, -1), (6, -1), (9, 1), (15, -1)]:
            mu = list(MU); mu[q] = value
            with self.assertRaises(ValueError): CHECK.validate_mu(mu, WORK)
        with self.assertRaises(ValueError): CHECK.validate_mu([0, True], WORK)

    def test_counterfactual_norms_agree_with_all_hermitian_crosses(self):
        checked = CHECK.verify_samples(self.producer, self.checker, WORK)
        self.assertTrue(checked['verified']); self.assertEqual(checked['sampled_events'], 15)
        self.assertFalse(checked['continuous_Gram_proved'])
        self.assertEqual(self.checker['precision'], 256)

    def test_q2_strict_old_mask_and_child_moving_shell(self):
        first = self.checker['records'][0]
        self.assertEqual(first['mask_old'], [True, True, True, False, False, False, False])
        self.assertEqual(first['mask_new'], [True]*7)
        for h in (3, 4, 5, 6):
            self.assertEqual(arb(first['values'][h]['w1']), 0)
            self.assertTrue(arb(first['values'][h]['shell']).overlaps(arb(first['values'][h]['energy'])))
            self.assertGreater(arb(first['values'][h]['shell']), 0)
        self.assertTrue(all(arb(v['shell']) == 0 for r in self.checker['records'][1:] for v in r['values']))

    def test_zero_mu_event_retains_finite_head_change_separately(self):
        row = next(r for r in self.checker['records'] if r['q'] == 4)
        self.assertEqual(row['mu'], 0)
        self.assertTrue(any(not arb(v['zero']).contains(0) for v in row['values']))
        for value in row['values']:
            self.assertEqual(row['mu']*arb(value['w1'])+row['mu']**2*arb(value['w2']), 0)

    def test_own_continuation_abel_and_exact_harmonic_checkpoint(self):
        ctx.prec = 192; p1 = PRODUCER.measure(MU[:9], 2, 8, None, WORK)
        p2 = PRODUCER.measure(MU, 9, 16, p1['state'], WORK)
        ctx.prec = 256; c1 = CHECK.measure(MU[:9], 2, 8, None, WORK)
        c2 = CHECK.measure(MU, 9, 16, c1['state'], WORK)
        self.assertTrue(CHECK.verify_samples(p2, c2, WORK)['verified'])
        for a, b in zip(c2['records'], self.checker['records'][7:]):
            for va, vb in zip(a['values'], b['values']):
                for key in va: self.assertTrue(arb(va[key]).overlaps(arb(vb[key])))
        bad = deepcopy(c1['state']); bad['c'] = '0'
        with self.assertRaises(ValueError): CHECK.measure(MU, 9, 16, bad, WORK)
        with self.assertRaises(ValueError): CHECK.measure(MU, 9, 16, p1['state'], WORK)

    def test_numeric_omission_masks_shell_cross_and_unit_tampers_rejected(self):
        for mutate in (lambda s:s['records'].pop(), lambda s:s['mu'].__setitem__(1, 0),
                       lambda s:s['records'][0]['mask_old'].__setitem__(3, True),
                       lambda s:s['records'][0]['values'][3].update(shell='0'),
                       lambda s:s['records'][1]['values'][0].update(w1='0'),
                       lambda s:s['records'][2]['values'][0].update(zero='0'),
                       lambda s:s.update(heights=['0'])):
            bad = deepcopy(self.producer); mutate(bad)
            with self.assertRaises((ValueError, KeyError, TypeError)):
                CHECK.verify_samples(bad, self.checker, WORK)

    def test_wide_and_nonfinite_numeric_balls_are_unresolved_not_certificates(self):
        for text in ('nan', '[0 +/- 1]', '1e100'):
            bad = deepcopy(self.producer); bad['records'][1]['values'][0]['w1'] = text
            with self.assertRaises(ValueError): CHECK.verify_samples(bad, self.checker, WORK)

    def test_full_grammar_and_exact_fractional_prime_window_boundaries(self):
        catalogue = CHECK.program_catalogue(); self.assertEqual(catalogue, PRODUCER.program_catalogue())
        self.assertEqual(len(catalogue), 18)
        self.assertEqual([sum(p['lane'] == lane for p in catalogue) for lane in ('fixed', 'prefix', 'window')], [3, 5, 10])
        program = next(p for p in catalogue if p.get('lower') == '1/6' and p.get('upper') == '1/3')
        self.assertEqual(CHECK._program_primes(program, 64, WORK), [3])
        program = next(p for p in catalogue if p.get('lower') == '0' and p.get('upper') == '1/6')
        self.assertEqual(CHECK._program_primes(program, 64, WORK), [2])
        for B in (64, 128, 512):
            for p in catalogue: self.assertEqual(CHECK._program_primes(p, B, WORK), PRODUCER.selected_primes(p, B, WORK))

    def test_fixed_prime_dyadic_groups_are_structurally_singletons(self):
        for program in CHECK.program_catalogue()[:3]:
            for B in (2, 4, 8):
                case = CHECK.group_case(program, B, self.checker, WORK)
                self.assertTrue(all(size == 1 for _, size in case['group_sizes']))
                self.assertFalse(case['nontrivial_partition'])

    def test_group_cofactors_zero_events_and_every_partial_prefix(self):
        program = CHECK.program_catalogue()[6]; sample = abstract_samples()
        case = CHECK.group_case(program, 8, sample, WORK)
        self.assertEqual(case['primes'], [2, 3])
        self.assertEqual(case['group_sizes'], [[5, 2], [7, 1], [11, 1], [13, 1]])
        self.assertEqual(case['zero_events'], 3); self.assertTrue(case['nontrivial_partition'])
        self.assertEqual([arb(v) for v in case['partial_curve']], [arb(v) for v in (0, 8, 9, 9, 10, 12, 4, 4)])
        self.assertEqual(arb(case['grouped_peak_absolute']), 12); self.assertEqual(arb(case['grouped_endpoint_absolute']), 4)
        self.assertEqual(arb(case['ungrouped_absolute']), 20); self.assertEqual(case['cancellation_bits'], 0)
        self.assertEqual(arb(case['joined_total']), 2); self.assertEqual(arb(case['singleton_absolute']), 4)

    def test_group_columns_agree_with_online_producer_on_synthetic_and_numeric_work(self):
        for sample in (abstract_samples(), self.checker):
            for program in CHECK.program_catalogue():
                expected = CHECK.group_case(program, 8, sample, WORK)
                actual = PRODUCER.group_case(program, 8, sample, WORK)
                self.assertTrue(CHECK.verify_cases([actual], [expected], WORK)['verified'])

    def test_zero_baseline_has_no_empirical_cancellation_rank(self):
        sample = abstract_samples()
        for row in sample['records']:
            for value in row['values']: value.update(w1='0', w2='0')
        case = CHECK.group_case(CHECK.program_catalogue()[6], 8, sample, WORK)
        self.assertIsNone(case['cancellation_bits']); self.assertEqual(arb(case['ungrouped_absolute']), 0)

    def test_endpoint_only_missing_groups_zero_events_and_fake_rank_rejected(self):
        sample = abstract_samples(); program = CHECK.program_catalogue()[6]
        case = CHECK.group_case(program, 8, sample, WORK)
        for mutate in (lambda c:c['partial_curve'].pop(), lambda c:c.update(grouped_peak_absolute=c['grouped_endpoint_absolute']),
                       lambda c:c.update(cancellation_bits=2), lambda c:c['group_sizes'].pop(),
                       lambda c:c.update(zero_events=0), lambda c:c.update(odd_total='1')):
            bad = deepcopy(case); mutate(bad)
            with self.assertRaises(ValueError): CHECK.verify_cases([bad], [case], WORK)

    def test_lane_selection_uses_all_four_declared_blocks_and_ties_by_id(self):
        programs = CHECK.program_catalogue(); cases = discovery_cases()
        selected = CHECK.select(programs, cases)
        self.assertEqual(selected, PRODUCER.select(programs, cases))
        self.assertEqual(selected['selected'], [dict(lane='prefix', program_id=6, minimum_cancellation_bits=1),
            dict(lane='window', program_id=9, minimum_cancellation_bits=2)])
        # The evaluation block cannot alter the already declared selection.
        heldout = [dict(program_id=p['id'], B=1024, cancellation_bits=20, nontrivial_partition=True) for p in programs]
        self.assertEqual(CHECK.select(programs, cases+heldout), selected)
        altered = deepcopy(cases)
        next(c for c in altered if c['program_id'] == 6 and c['B'] == 512)['cancellation_bits'] = 0
        self.assertEqual(CHECK.select(programs, altered)['selected'][0]['program_id'], 3)

    def test_missing_degenerate_and_zero_discovery_cases_remain_rejections(self):
        programs = CHECK.program_catalogue(); cases = discovery_cases()
        cases = [c for c in cases if (c['program_id'], c['B']) != (3, 512)]
        next(c for c in cases if (c['program_id'], c['B']) == (4, 64))['cancellation_bits'] = None
        selected = CHECK.select(programs, cases); rejected = {c['program_id']:c['reason'] for c in selected['rejected']}
        self.assertEqual(rejected[0], 'degenerate_partition'); self.assertEqual(rejected[3], 'missing_discovery_case')
        self.assertEqual(rejected[4], 'zero_baseline')
        with self.assertRaises(ValueError): CHECK.select(programs[:-1], cases)
        with self.assertRaises(ValueError): CHECK.select(programs, cases+[cases[0]])

    def test_complete_source_current_target_and_signed_sector_binding(self):
        self.assertEqual(self.binding, PRODUCER.bind_target(self.parent, WORK))
        self.assertEqual(self.binding['inherited_bound']['R_q']['sectors'], [1, 2])
        self.assertEqual(self.binding['source_scalar'], '18')
        self.assertEqual(len(self.parent['generated_bound_obligations']), 144)
        self.assertFalse(self.binding['whole_signed_bound_proved'])

    def test_source_unit_drift_binding_and_current_component_tampers_rejected(self):
        for mutate in (lambda p:p['selected_source_representation']['cases'][0]['program']['terms'].pop(0),
                       lambda p:p['generated_bound_obligations'].pop(),
                       lambda p:p['complete_source_reduction'].update(transport_error_retained='0'),
                       lambda p:p['cutoff_work_targets'][0].update(m=2),
                       lambda p:p['cutoff_work_targets'][0]['programs'][1]['centering'].update(all_opposite_drifts_retained=False),
                       lambda p:p['cutoff_work_targets'][0]['programs'][1]['transition']['work_sectors'][1].pop()):
            parent = deepcopy(self.parent); mutate(parent)
            with self.assertRaises((ValueError, KeyError, TypeError)): CHECK.bind_target(parent, WORK)

    def test_feedback_preserves_old_tasks_and_uses_stronger_complete_continuous_scope(self):
        cases = discovery_cases(); selection = CHECK.select(CHECK.program_catalogue(), cases)
        output = PRODUCER.feedback(self.parent, self.binding, selection, cases, 'immutable/orbits.json')
        checked = CHECK.verify_feedback(self.parent, self.binding, selection, cases, output, 'immutable/orbits.json', WORK)
        self.assertTrue(checked['verified']); self.assertFalse(checked['uniform_bound_proved'])
        self.assertEqual(output['next_search_tasks'][0], self.parent['next_search_tasks'][0])
        self.assertEqual(output['next_search_tasks'][-1], self.parent['next_search_tasks'][-1])
        target = output['next_search_tasks'][1]
        self.assertIn('integral_R sum_r abs', target['expression'])
        self.assertIn('H(q-1)', target['rho_q']); self.assertFalse(target['finite_samples_establish_bound'])
        self.assertEqual(target['status'], 'open')
        for mutate in (lambda o:o['next_search_tasks'][1].update(status='proved'),
                       lambda o:o['next_search_tasks'][1].update(quantifier='only B=1024'),
                       lambda o:o['next_search_tasks'][1].update(rho_q='no moving window'),
                       lambda o:o['next_search_tasks'][1].update(finite_samples_establish_bound=True),
                       lambda o:o['next_search_tasks'].pop(0), lambda o:o['generated_bound_obligations'].pop(),
                       lambda o:o.update(RH_proved=True)):
            bad = deepcopy(output); mutate(bad)
            with self.assertRaises(ValueError): CHECK.verify_feedback(self.parent, self.binding, selection, cases, bad, 'immutable/orbits.json', WORK)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_cutoff_prime_orbits operations='+str(WORK.operations)+
          ' elapsed_seconds='+format(time.monotonic()-START, '.6f'))


if __name__ == '__main__': unittest.main()
