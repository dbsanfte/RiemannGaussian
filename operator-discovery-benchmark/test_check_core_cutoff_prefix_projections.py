"""Synthetic complete-prefix calibrations and independent proof tamper audits.

No archived source work, zeta evaluation, or previous test suite is executed.
"""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import time
import unittest

from flint import arb, ctx
import core_cutoff_prefix_projections as PRODUCER
import check_core_cutoff_prefix_projections as CHECK
from potential_candidate_language import Meter

START = time.monotonic()
WORK = Meter(50000000, deadline=START+180, max_cells=2000000)
MU = [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0]


def abstract_samples(work=None):
    r = {2:10, 3:-6, 5:8, 6:5, 7:-2, 10:-8, 11:1, 13:-1, 14:2, 15:3} if work is None else work
    records = []
    for q in range(2, 17):
        values = [dict(w1=str(r.get(q, 0)*MU[q] if h == 0 else 0), w2='0', zero='0', shell='0', energy='0') for h in range(7)]
        records.append(dict(q=q, mu=MU[q], mask_old=[True]*7, mask_new=[True]*7, values=values))
    return dict(schema='cutoff-work-samples-v1', start=2, end=16, precision=256,
        heights=CHECK.HEIGHTS, mu=list(MU), initial_energy=['0']*7, records=records, state={})


def discovery_cases():
    return [dict(program_id=p['id'], B=B, grouped_peak_absolute='50', ungrouped_absolute='100',
                 nontrivial_partition=True, cancellation_bits=1)
            for p in CHECK.program_catalogue() for B in (64,128,256,512)]


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_cutoff_prefix_projections operations='+str(WORK.operations)+
          ' elapsed_seconds='+str(time.monotonic()-START), flush=True)


def symbolic_cutoff_parent():
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


class IndependentPrefixProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import check_core_cutoff_prime_orbits as OLD_CHECK
        import core_cutoff_prime_orbits as OLD_PRODUCER
        ctx.prec = 256
        cutoff_parent = symbolic_cutoff_parent()
        binding = OLD_CHECK.bind_target(cutoff_parent, WORK)
        selection = OLD_CHECK.select(OLD_CHECK.program_catalogue(), [])
        cls.parent = OLD_PRODUCER.feedback(cutoff_parent, binding, selection, [], 'synthetic/prior-search.json')
        cls.binding = CHECK.source_binding(cls.parent, WORK)
        cls.proof = PRODUCER.proof_search(cls.parent, cls.binding, WORK)
        cls.programs = CHECK.program_catalogue()

    def setUp(self): ctx.prec = 256

    def reject_proof(self, mutate):
        bad = deepcopy(self.proof); mutate(bad)
        with self.assertRaises((ValueError, KeyError, TypeError)):
            CHECK.verify_proof_search(self.parent, self.binding, bad, WORK)

    def test_full_catalogue_factor_labels_and_exact_prime_boundaries(self):
        self.assertEqual(self.programs, PRODUCER.program_catalogue())
        self.assertEqual(len(self.programs), 36)
        self.assertEqual([p['id'] for p in self.programs], list(range(36)))
        self.assertEqual([sum(p['lane'] == lane for p in self.programs) for lane in
            ('fixed:rough','fixed:smooth','prefix:rough','prefix:smooth','window:rough','window:smooth')], [3,3,5,5,10,10])
        window = next(p for p in self.programs if p['projection'] == 'rough' and
            p['prime_program'].get('lower') == '1/6' and p['prime_program'].get('upper') == '1/3')
        self.assertEqual(CHECK._program_primes(window['prime_program'], 64, WORK), [3])
        labels = CHECK._labels(30, [2,3], [0,1,-1,-1,0,-1,1]+[0]*23+[-1], WORK)
        self.assertEqual(labels, dict(rough=5, smooth=6))

    def test_complete_rough_prefix_golden_signed_columns_and_metadata(self):
        case = CHECK.group_case(self.programs[0], 8, abstract_samples(), WORK)
        self.assertEqual(case['group_sizes'], [[1,1],[3,2],[5,2],[7,2],[11,1],[13,1],[15,1]])
        self.assertEqual([arb(x) for x in case['partial_curve']], [arb(x) for x in (21,13,14,14,15,13,16,16)])
        self.assertEqual(arb(case['initial_grouped_absolute']), 21)
        self.assertEqual(arb(case['grouped_peak_absolute']), 21)
        self.assertEqual(arb(case['ungrouped_absolute']), 46)
        self.assertEqual(arb(case['joined_total']), 12)
        self.assertEqual(arb(case['singleton_absolute']), 15)
        self.assertEqual((case['zero_events'], case['cross_scale_groups'], case['groups_with_opposite_mu'],
            case['prime_composite_groups']), (5,2,3,3))
        self.assertEqual(case['prefix_start'], 2); self.assertEqual(case['cancellation_bits'], 1)

    def test_complete_smooth_prefix_and_previous_scale_interactions(self):
        case = CHECK.group_case(self.programs[1], 8, abstract_samples(), WORK)
        self.assertEqual(case['group_sizes'], [[1,6],[2,4]])
        self.assertEqual([arb(x) for x in case['partial_curve']], [arb(x) for x in (15,7,8,8,7,9,12,12)])
        self.assertEqual(arb(case['initial_grouped_absolute']), 15)
        self.assertEqual((case['cross_scale_groups'],case['groups_with_opposite_mu'],case['prime_composite_groups']), (2,2,2))
        self.assertEqual(arb(case['singleton_absolute']), 0)

    def test_initial_endpoint_excluded_from_declared_peak_and_unit_base(self):
        sample = abstract_samples({3:100,5:-100})
        case = CHECK.group_case(self.programs[1], 4, sample, WORK)
        self.assertEqual(arb(case['initial_grouped_absolute']), 100)
        self.assertTrue(all(arb(x) == 0 for x in case['partial_curve']))
        self.assertEqual(arb(case['grouped_peak_absolute']), 0)
        self.assertEqual(arb(case['ungrouped_absolute']), 200)
        first = CHECK.group_case(self.programs[0], 1, sample, WORK)
        self.assertEqual(arb(first['initial_grouped_absolute']), 0)
        self.assertEqual(first['zero_events'], 0); self.assertEqual(len(first['partial_curve']), 1)

    def test_online_producer_and_independent_group_first_columns_agree(self):
        sample = abstract_samples()
        for program in self.programs:
            checker = CHECK.group_case(program, 8, sample, WORK)
            producer = PRODUCER.group_case(program, 8, sample, WORK)
            self.assertTrue(CHECK.verify_cases([producer], [checker], WORK)['verified'])
        # Odd/even cross cancellation must occur before taking absolute values.
        for row in sample['records']:
            for value in row['values']: value.update(w1='1', w2=str(-row['mu']))
        case = CHECK.group_case(self.programs[1], 8, sample, WORK)
        self.assertEqual(arb(case['ungrouped_absolute']), 0)
        self.assertIsNone(case['cancellation_bits'])
        self.assertTrue(arb(case['odd_total']) != 0)
        self.assertEqual(arb(case['joined_total']), 0)

    def test_coarsening_refinement_and_empty_prime_calibrations(self):
        sample = abstract_samples()
        rough2 = CHECK.group_case(self.programs[0], 8, sample, WORK)
        rough23 = CHECK.group_case(self.programs[12], 8, sample, WORK)
        smooth2 = CHECK.group_case(self.programs[1], 8, sample, WORK)
        smooth23 = CHECK.group_case(self.programs[13], 8, sample, WORK)
        self.assertEqual(rough23['primes'], [2,3])
        for a,b in zip(rough23['partial_curve'], rough2['partial_curve']): self.assertLessEqual(arb(a),arb(b))
        for a,b in zip(smooth23['partial_curve'], smooth2['partial_curve']): self.assertGreaterEqual(arb(a),arb(b))
        empty_rough = CHECK.group_case(self.programs[6], 2, sample, WORK)
        empty_smooth = CHECK.group_case(self.programs[7], 2, sample, WORK)
        self.assertEqual(empty_rough['primes'], [])
        self.assertTrue(all(size == 1 for _,size in empty_rough['group_sizes']))
        self.assertEqual(empty_smooth['group_sizes'], [[1,2]])
        self.assertFalse(empty_smooth['nontrivial_partition'])

    def test_case_tampers_missing_prefix_crosses_unit_and_wide_intervals(self):
        expected = CHECK.group_case(self.programs[0], 8, abstract_samples(), WORK)
        for mutate in (lambda c:c['partial_curve'].pop(), lambda c:c.update(prefix_start=9),
            lambda c:c.update(cross_scale_groups=0), lambda c:c.update(groups_with_opposite_mu=0),
            lambda c:c.update(prime_composite_groups=0), lambda c:c.update(zero_events=3),
            lambda c:c.update(initial_grouped_absolute='0'), lambda c:c.update(grouped_peak_absolute='16'),
            lambda c:c.update(ungrouped_absolute='20'), lambda c:c.update(joined_total='nan'),
            lambda c:c.update(singleton_absolute='[0 +/- 1]')):
            bad = deepcopy(expected); mutate(bad)
            with self.assertRaises(ValueError): CHECK.verify_cases([bad],[expected],WORK)
        for mutate in (lambda s:s['mu'].__setitem__(1,0), lambda s:s['records'].pop(0),
            lambda s:s['records'][0].update(mu=1), lambda s:s['records'][0]['values'].pop(),
            lambda s:s.update(start=9)):
            sample = abstract_samples(); mutate(sample)
            with self.assertRaises((ValueError, KeyError)): CHECK.group_case(self.programs[0],8,sample,WORK)

    def test_exact_ratio_ranking_resolves_same_diagnostic_bits(self):
        cases = discovery_cases()
        for row in cases:
            if row['program_id'] == 2: row['grouped_peak_absolute'] = '45'
        selection = CHECK.select(self.programs,cases,WORK)
        self.assertEqual(selection['selected'][0],dict(lane='fixed:rough',program_id=2))
        self.assertEqual(selection['undominated_by_lane']['fixed:rough'],[2])
        self.assertEqual(selection,PRODUCER.select(self.programs,cases,WORK))
        for row in cases: row['cancellation_bits'] = 20 if row['program_id'] == 0 else 0
        self.assertEqual(selection,CHECK.select(self.programs,cases,WORK))

    def test_worst_validation_ratio_and_heldout_cannot_reselect(self):
        cases = discovery_cases()
        for row in cases:
            if row['program_id'] == 2: row['grouped_peak_absolute'] = '45' if row['B'] != 512 else '60'
        selection = CHECK.select(self.programs,cases,WORK)
        self.assertEqual(selection['selected'][0]['program_id'],0)
        for p in self.programs:
            cases.append(dict(program_id=p['id'],B=1024,ungrouped_absolute='100',grouped_peak_absolute='0',
                              nontrivial_partition=True,cancellation_bits=20))
        self.assertEqual(selection,CHECK.select(self.programs,cases,WORK))

    def test_interval_dominance_keeps_unresolved_ties_explicit(self):
        cases = discovery_cases()
        narrow = CHECK._ball(arb(50, arb(2)**-120))
        for row in cases:
            if row['program_id'] == 2: row['grouped_peak_absolute'] = narrow
            if row['program_id'] == 4: row['grouped_peak_absolute'] = '60'
        selection = CHECK.select(self.programs,cases,WORK)
        self.assertEqual(selection['undominated_by_lane']['fixed:rough'],[0,2])
        self.assertEqual(selection['selected'][0]['program_id'],0)
        self.assertEqual(selection,PRODUCER.select(self.programs,cases,WORK))

    def test_selection_rejection_reasons_and_duplicate_cases(self):
        cases = discovery_cases(); cases = [r for r in cases if not(r['program_id']==0 and r['B']==128)]
        next(r for r in cases if r['program_id']==1)['ungrouped_absolute']='0'
        next(r for r in cases if r['program_id']==2)['nontrivial_partition']=False
        selection = CHECK.select(self.programs,cases,WORK)
        self.assertEqual(selection['rejected'][:3], [dict(program_id=0,reason='missing_discovery_case'),
            dict(program_id=1,reason='zero_baseline'),dict(program_id=2,reason='degenerate_partition')])
        with self.assertRaises(ValueError): CHECK.select(self.programs,cases+[cases[0]],WORK)
        with self.assertRaises(ValueError): CHECK.select(self.programs[:-1],cases,WORK)

    def test_independent_complete_source_replay_and_all_conditional_routes(self):
        self.assertEqual(self.binding,PRODUCER.source_binding(self.parent,WORK))
        verified = CHECK.verify_proof_search(self.parent,self.binding,self.proof,WORK)
        self.assertTrue(verified['verified']); self.assertEqual(verified['conditional_Gram_routes'],252)
        self.assertEqual(verified['new_uniform_signed_arithmetic_estimates'],0)
        self.assertEqual(self.proof['common_window']['cost_B_power'],'21/10')
        self.assertEqual(self.proof['common_window']['gap_to_goal'],'3/10')
        self.assertEqual(self.proof['programs'][0]['gram_auxiliaries'][0]['kernel_mass_constant'],'100/13')

    def test_harmonic_boundary_and_fixed_prime_mass_not_growing_window_mass(self):
        fixed = CHECK.mass_rule(self.programs[1],'1'); generic = CHECK.mass_rule(self.programs[7],'1')
        self.assertEqual((fixed['B_power'],fixed['log_degree'],fixed['constant']),('0',0,'2'))
        self.assertEqual((generic['B_power'],generic['log_degree'],generic['constant']),('0',1,'1'))
        self.assertEqual(CHECK.mass_rule(self.programs[7],'3/2')['constant'],'3')
        self.assertEqual(CHECK._sum_power('-1'),dict(B_power='0',log_degree=1))
        self.assertEqual(CHECK._sum_power('-3/2'),dict(B_power='0',log_degree=0))
        critical = self.proof['programs'][7]['gram_auxiliaries'][5]
        self.assertEqual(critical['sufficient_bound']['log_degree'],-1)
        self.assertEqual(critical['sufficient_bound']['B_power'],'24/5')
        # Independent finite weighted Cauchy calibration, including a signed cross.
        eta = [Q(1),Q(1,2)]; g = [Q(3),Q(-2)]
        left = sum(abs(x) for x in g)**2
        right = sum(eta)*sum(x*x/w for x,w in zip(g,eta))
        self.assertLessEqual(left,right)
        self.assertEqual((Q(5)+Q(-4))**2,1)
        self.assertEqual(Q(5)**2+Q(-4)**2,41)  # Diagonal-only is a different Gram.

    def test_common_window_own_tail_scope_mutations_rejected(self):
        for key,value in [('event_domain','B<q<=V<=2B'),('virtual_c_bound','2'),('cost_B_power','11/10'),
                          ('length_ratio','q comparable with B'),('paid',False),('unit_event','dropped')]:
            with self.subTest(key=key): self.reject_proof(lambda p:p['common_window'].__setitem__(key,value))
        self.reject_proof(lambda p:p['common_window']['summed_powers']['finite_head_full_norm'].update(B_power='11/10'))

    def test_gram_cross_weight_log_and_false_provider_mutations_rejected(self):
        mutations = [lambda p:p['programs'].pop(),lambda p:p['programs'][0]['gram_auxiliaries'].pop(),
            lambda p:p['programs'][7]['gram_auxiliaries'][5]['sufficient_bound'].update(log_degree=0),
            lambda p:p['programs'][7]['gram_auxiliaries'][5].update(mass=CHECK.mass_rule(self.programs[1],'1')),
            lambda p:p['programs'][0]['gram_auxiliaries'][0].update(ordered_pairs='diagonal only'),
            lambda p:p['programs'][0]['gram_auxiliaries'][0].update(W_sectors_are_unweighted=False),
            lambda p:p['programs'][0]['gram_auxiliaries'][0].update(kappa='abs(zeta(s+1/3)/s)^4'),
            lambda p:p['programs'][0]['gram_auxiliaries'][0].update(cached_weighted_samples_are_not_a_Gram_estimate=False),
            lambda p:p['programs'][0]['gram_auxiliaries'][0].update(higher_moment_provider_available=True),
            lambda p:p['programs'][0]['gram_auxiliaries'][0].update(status='proved'),
            lambda p:p['programs'][0].update(closed_uniform_bound=True),lambda p:p.update(RH_proved=True)]
        for i,mutate in enumerate(mutations):
            with self.subTest(mutation=i): self.reject_proof(mutate)

    def test_source_binding_rejects_dropped_inverse_channel_drift_and_unit(self):
        mutations = [lambda p:p['selected_source_representation']['cases'][0]['program']['terms'].pop(),
            lambda p:p['generated_bound_obligations'].pop(),
            lambda p:p['complete_source_reduction'].update(transport_error_retained='0'),
            lambda p:p['prime_orbit_search']['binding']['inherited_bound'].update(power='0'),
            lambda p:p.update(whole_signed_bound_proved=True)]
        for mutate in mutations:
            parent = deepcopy(self.parent); mutate(parent)
            with self.assertRaises((ValueError,KeyError)): CHECK.source_binding(parent,WORK)

    def test_feedback_preserves_full_core_source_and_open_uniform_scope(self):
        cases = discovery_cases(); selection = CHECK.select(self.programs,cases,WORK)
        artifact = 'synthetic/new/search.json'
        output = PRODUCER.feedback(self.parent,self.binding,self.proof,selection,cases,artifact)
        self.assertTrue(CHECK.verify_feedback(self.parent,self.binding,self.proof,selection,cases,output,artifact,WORK)['verified'])
        self.assertEqual(output['next_search_tasks'][0]['target_id'],'actual_signed_core')
        self.assertEqual(output['next_search_tasks'][0]['priority'],0)
        for mutate in (lambda p:p['next_search_tasks'].pop(0),lambda p:p['generated_bound_obligations'].pop(),
            lambda p:p['prefix_projection_search'].update(numeric_Gram_estimates_used=True),
            lambda p:p['next_search_tasks'][1].update(finite_score_proves_uniform_bound=True),
            lambda p:p.update(RH_proved=True)):
            bad = deepcopy(output); mutate(bad)
            with self.assertRaises(ValueError):
                CHECK.verify_feedback(self.parent,self.binding,self.proof,selection,cases,bad,artifact,WORK)


if __name__ == '__main__': unittest.main()
