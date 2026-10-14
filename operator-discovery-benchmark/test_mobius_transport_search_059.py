"""Synthetic plan algebra and search gates; no059 scientific source values."""
import copy
from fractions import Fraction as Q
import unittest

import mobius_transport_search_059 as S

METER = S.Meter()


def token(d, sign, magnitude, profile='P', kernel_sign=1):
    return {'d':d,'sign':sign,'magnitude':magnitude,'profile':profile,
        'kernel_sign':kernel_sign,'mu':sign*kernel_sign}


class TransportSearchTests(unittest.TestCase):
    def test_bound_can_retain_cancellation_without_equaling_target(self):
        tokens = [token(d,s,v) for d,s,v in [(1,1,9),(7,-1,8),(11,-1,2),(13,1,1)]]
        policy = {'steps':[S._scan('profile')]}
        plan = S.build_plan(31,tokens,policy,METER)
        self.assertEqual(S.plan_cost(tokens,plan,METER),2)
        self.assertEqual(sum(t['sign']*t['magnitude'] for t in tokens),0)
        self.assertEqual(plan['unmatched'],[])

    def test_second_pass_pairs_residuals_without_discarding_any_term(self):
        tokens = [token(1,1,9,'P'),token(7,-1,8,'Q'),token(11,1,2,'P')]
        first = S.build_plan(31,tokens,{'steps':[S._scan('profile')]},METER)
        complete = S.build_plan(31,tokens,{'steps':[S._scan('profile'),S._scan()]},METER)
        self.assertEqual(len(first['unmatched']),3)
        self.assertEqual(len(complete['unmatched']),1)
        self.assertLessEqual(S.plan_cost(tokens,complete,METER),S.plan_cost(tokens,first,METER))
        self.assertEqual(sorted(sum(complete['pairs'],[])+complete['unmatched']),[1,7,11])

    def test_prime_edges_are_not_a_fixed_small_prime_whitelist(self):
        tokens = [token(1,1,9),token(17,-1,8),token(19,-1,3),token(323,1,1)]
        policy = {'steps':[{'kind':'prime_ratio','group':'profile','order':'asc'}]}
        plan = S.build_plan(31,tokens,policy,METER)
        self.assertEqual(len(plan['pairs']),2)
        self.assertTrue(all(max(a,b)//min(a,b) in (17,19) for a,b in plan['pairs']))
        self.assertLessEqual(S.plan_cost(tokens,plan,METER),21)

    def test_pair_choice_never_reads_magnitudes_or_input_order(self):
        tokens = [token(1,1,9,'Q'),token(7,-1,8),token(11,1,2,'D')]
        changed = copy.deepcopy(tokens[::-1])
        for i,t in enumerate(changed): t['magnitude']=1000/(i+1)
        policies=[{'steps':[S._scan()]},{'steps':[S._scan('profile_residue',modulus=3),S._scan()]}]
        policies += [{'steps':[{'kind':'kernel_scan','kernels':S.source_kernel_expressions(3,5),
                      'order':order,'method':method},S._scan()]}
                     for order in ('asc','desc') for method in ('stack','fifo')]
        for policy in policies:
            self.assertEqual(S.build_plan(31,tokens,policy,METER),S.build_plan(31,changed,policy,METER))

    def test_kernel_expression_normalization_merges_scaled_arguments(self):
        a,key=S.normalize_kernel([[3,'1']]);b,key2=S.normalize_kernel([[5,'1']])
        self.assertEqual((a,b),(3,5));self.assertEqual(key,key2)
        self.assertEqual(S.normalize_kernel([[6,'1'],[10,'-1']])[1],
                         S.normalize_kernel([[3,'1'],[5,'-1']])[1])
        self.assertNotEqual(key,S.normalize_kernel([[3,'1'],[5,'-1']])[1])
        # Exact arguments 3*7 and5*1 reorder the profiles without weights.
        tokens=[token(1,-1,10,'Q'),token(7,1,3,'P'),token(11,-1,2,'D')]
        step={'kind':'kernel_scan','kernels':S.source_kernel_expressions(3,5),'order':'asc','method':'stack'}
        plan=S.build_plan(31,tokens,{'steps':[step]},METER)
        self.assertEqual(plan['pairs'],[[7,1]]);self.assertEqual(plan['unmatched'],[11])
        # Raw index order would pair 7 with 11; kernel arguments require 5.
        reordered=[token(5,1,4,'Q'),token(7,1,5,'P'),token(11,-1,3,'P')]
        plan=S.build_plan(31,reordered,{'steps':[step]},METER)
        self.assertEqual(plan['pairs'],[[5,11]]);self.assertEqual(plan['unmatched'],[7])
        programs=S.grammar(kernels=S.source_kernel_expressions(3,5))
        self.assertTrue(any(r['family']=='shared_kernel_scan' for r in S.profile_dominance(programs)['scored']))

    def test_sorted_profile_optimum_and_reverse_can_differ(self):
        tokens = [token(1,1,9),token(7,-1,8),token(11,1,7)]
        costs = {}
        for order in ('asc','desc'):
            for method in ('stack','fifo'):
                policy={'steps':[S._scan('profile',order,method)]}
                costs[order,method]=S.plan_cost(tokens,S.build_plan(31,tokens,policy,METER),METER)
        self.assertEqual(costs['asc','stack'],8)
        self.assertEqual(costs['asc','fifo'],8)
        self.assertGreater(costs['desc','stack'],8)

    def test_general_fractional_blocks_and_grammar_budget(self):
        self.assertEqual(S.floor_power(81,'3/4',METER),27)
        self.assertEqual(S.floor_power(257,'2/7',METER),4)
        self.assertEqual(S.floor_power(31,'1/257',METER),1)
        programs = S.grammar(kernels=S.source_kernel_expressions(3,5))
        self.assertLess(len(programs),512)
        self.assertTrue(any(any(s.get('theta')=='1/257' for s in r['policy']['steps']) for r in programs))
        for r in programs: S.validate_policy(r['policy'])
        with self.assertRaises(ValueError): S.floor_power(31,'-1/2',METER)
        with self.assertRaises(OverflowError): S.floor_power(31,'1/1000001',METER)

    def test_dominance_never_rejects_cross_profile_policies(self):
        programs = S.grammar(kernels=S.source_kernel_expressions(3,5)); gate = S.profile_dominance(programs)
        by_id = {r['id']:r for r in programs}
        self.assertTrue(gate['excluded'])
        for r in gate['excluded']:
            self.assertTrue(all(s['group']!='all' for s in by_id[r['id']]['policy']['steps']))
            self.assertFalse(r['uniform_growth_bound_proved'])
        self.assertIn(gate['reference_id'],{r['id'] for r in gate['scored']})
        self.assertTrue(any(r['family']=='prime_ratio' for r in gate['scored']))
        self.assertTrue(any(r['family']=='shared_kernel_scan' for r in gate['scored']))

    def test_missing_duplicate_wrong_sign_and_extra_policy_fields_rejected(self):
        tokens = [token(1,1,9),token(7,-1,8),token(11,1,7)]
        for plan in ({'pairs':[[1,7]],'unmatched':[]},
                     {'pairs':[[1,7]],'unmatched':[1,11]},
                     {'pairs':[[1,11]],'unmatched':[7]}):
            with self.assertRaises(ValueError): S.plan_cost(tokens,plan,METER)
        with self.assertRaises(ValueError): S.validate_policy({'steps':[dict(S._scan(),cost_oracle=True)]})

    def test_fixed_claim_selection_preserves_open_uniform_status(self):
        scored = S.profile_dominance(S.grammar(kernels=S.source_kernel_expressions(3,5)))['scored']
        families=('unmatched_control','global_scan','profile_scan','shared_kernel_scan','arithmetic_partition','prime_ratio')
        programs=[next(r for r in scored if r['family']==name) for name in families]
        observations = {n:{'absolute_sum':float(n),'costs':[{'id':r['id'],'cost':n**0.5*(i+1)}
            for i,r in enumerate(programs)]} for n in (64,256)}
        rows = S.hypotheses(programs,observations)
        before = copy.deepcopy(rows); selected = S.select(rows,programs)
        self.assertEqual(before,rows)
        self.assertTrue(selected)
        self.assertTrue(all(not r['uniform_bound_proved'] for r in selected))
        self.assertTrue(any(r['claim']['C']=='0' for r in selected))
        self.assertTrue(all(Q(r['claim']['beta']) in map(Q,S.BETAS) for r in selected))
        self.assertEqual({r['family'] for r in selected},set(families))


if __name__ == '__main__': unittest.main()
