import unittest
from fractions import Fraction as Q
from unittest.mock import patch

import mobius_count_control_076 as P
import check_mobius_count_control_076 as C


class Producer(unittest.TestCase):
    def test_grammar_has_variable_fractional_powers_without_duplicate_directs(self):
        spec = dict(grid=80, theta=['1/2','3/4'], multipliers=[2,6])
        atoms = P.grammar(spec,['1/2','8/13','1/2'],'joint')
        self.assertEqual(atoms,[dict(column=0,gamma='1/2'),dict(column=0,gamma='8/13'),
                                dict(column=1,gamma='0'),dict(column=2,gamma='0')])
        with self.assertRaises(ValueError):P.admit_atoms(atoms+atoms[:1],spec)

    def test_rational_cauchy_budget_with_repeated_signed_atoms(self):
        spec = dict(grid=80,theta=['1/2','3/4'],multipliers=[2])
        atoms=[dict(column=0,gamma='1/2'),dict(column=0,gamma='7/11'),dict(column=1,gamma='0')]
        coefficients=[Q(1,10),Q(-1,11),Q(1,12)]
        paid=P.structural_weights(spec,atoms,coefficients,64)
        self.assertEqual(sum((a*a/b for a,b in zip(paid['column_mass'],paid['beta']) if b),Q(0)),1)
        self.assertLessEqual(paid['rho'],paid['exposure']**2)
        self.assertTrue(C.structural_cauchy([P.atom_key(a) for a in atoms],coefficients,paid['beta'],1))

    def test_exact_signed_intervals_match_independent_checker(self):
        row=dict(components=[-11,7],counts=[7,1])
        atoms=[dict(column=0,gamma='17/31'),dict(column=0,gamma='101/97'),dict(column=1,gamma='0')]
        a=[Q(-3,7),Q(2,9),Q(-1,4)]
        self.assertEqual(P.operator_enclosure(atoms,a,row,12),C.operator_interval(row,[P.atom_key(x) for x in atoms],a,12))
        self.assertEqual(P.squared_interval(Q(-2),Q(3)),(0,9))

    def test_lp_learns_signed_control_and_preserves_exact_budget(self):
        spec=dict(grid=80,theta=['1/2','3/4'],multipliers=[2,3])
        rows=[dict(u=80+i,z=Q(x-y,8),components=[0,x,y],counts=[0,1,1])
              for i,(x,y) in enumerate([(1,0),(0,1),(1,1),(3,-2),(-4,-1)])]
        data=dict(spec=spec,rows=rows)
        atoms=P.grammar(spec,['1/2'],'direct_only')
        result=P.fit_operator(data,atoms,'1','1/2',64,P.S.Meter())
        self.assertEqual(result['status'],'PROPOSED')
        self.assertEqual(result['coefficients'],['1/8','-1/8'])
        self.assertLessEqual(Q(result['exposure']),Q(1,2))

    def test_small_budget_rescale_is_exact(self):
        spec=dict(grid=80,theta=['1/2','3/4'],multipliers=[2])
        atoms=[dict(column=1,gamma='0')]
        data=dict(spec=spec,rows=[dict(u=80,z=100,components=[0,100],counts=[0,1])])
        result=P.fit_operator(data,atoms,'1','1/3',64,P.S.Meter())
        self.assertLessEqual(Q(result['exposure']),Q(1,3))
        self.assertTrue(all(Q(x).denominator>0 for x in result['coefficients']))

    def test_imported_feedback_really_changes_atoms_and_proof_mode(self):
        spec=dict(grid=80,theta=['1/2','3/4'],multipliers=[2])
        record=dict(id='x',shape=['1','-1'])
        controls=[P.F.normalized_control(record,spec,g,64) for g in ('1/3','17/31')]
        feedback=dict(schema='coherent-prime-control-feedback-v1',source_spec=spec,controls=controls)
        imported=P.imported_operators(feedback,spec)
        self.assertEqual([x['mode'] for x in imported],['arithmetic_claim','structural_cauchy'])
        self.assertEqual(imported[1]['atoms'],[dict(column=0,gamma='17/31'),dict(column=1,gamma='0')])

    def test_byte_cache_does_not_retain_oversized_entries(self):
        cache=P.ByteCache(2048)
        for i in range(20):
            value=cache.get((i,Q(17,31)),lambda:Q(2**300+i,7))
            self.assertGreater(value,0)
            self.assertLessEqual(cache.bytes,2048)
        before=cache.bytes
        cache.get((100,Q(1)),lambda:Q(2**100000))
        self.assertEqual(cache.bytes,before)
        self.assertNotIn((100,Q(1)),cache.values)

    def test_feature_cache_bypasses_unbounded_inherited_lru(self):
        # A distinct076 cache miss uses the underlying exact operation;
        # it must not add an entry to the inherited entry-count cache.
        before=P.F.count_power_bounds.cache_info()
        P.count_bounds(113,Q(19,23),13)
        self.assertEqual(P.F.count_power_bounds.cache_info(),before)


if __name__=='__main__':unittest.main()
