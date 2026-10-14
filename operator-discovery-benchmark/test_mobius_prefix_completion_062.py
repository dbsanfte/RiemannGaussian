"""Synthetic compiler and optimizer tests; no scientific062 source values."""
from fractions import Fraction as Q
from math import gcd
import unittest

import mobius_prefix_completion_062 as S
import check_mobius_prefix_completion_062 as C

METER=S.Meter()
PARAMS={'alpha':'1/257','gamma':'1/3','tau':'3/4','primes':[2,7],'p':2,'q':7}


def checked(cert):
    cm=C.Meter();out=C.verify_completion(cert,cm);METER.charge(cm.operations);return out


class CompletionSearchTests(unittest.TestCase):
    def test_ordinary_inverse_coefficients_and_indicator_primitive(self):
        mu=S.ordinary_mu(16,METER)
        self.assertEqual(mu[:11],[0,1,-1,-1,0,-1,1,-1,0,0,1])
        for T in (7,17,29):
            H=4;mu=S.ordinary_mu(T//(H+1),METER)
            for d in range(H+1,T+5):
                self.assertEqual(sum(mu[l]*(T//(l*d)) for l in range(1,len(mu))),int(d<=T))
                METER.charge(len(mu)*8)

    def test_grouped_indicator_expansion_has_correct_cutoff(self):
        Z,y,H=57,19,4;groups=S.indicators(Z,y,H,METER)
        for d in range(H+1,Z+3):
            self.assertEqual(sum(a for T,a in groups.items() if d<=T),(Z//d if d<=y else 0))
            METER.charge(10*len(groups))

    def test_generic_completion_with_nonzero_short_remainder(self):
        base=S.inverse_completion(31,23,5,PARAMS,METER)
        cert=S.exact_certificate(31,23,5,PARAMS,base['endpoints'],METER)
        verdict=checked(cert)
        self.assertTrue(verdict['finite_prefix_bound_proved'])
        self.assertTrue(any(Q(x['short_residual_l1']) for x in verdict['endpoint_costs']))
        self.assertFalse(verdict['uniform_N_growth_proved'])

    def test_empty_completion_and_full_short_residual(self):
        base=S.inverse_completion(31,5,5,PARAMS,METER)
        cert=S.exact_certificate(31,5,5,PARAMS,base['endpoints'],METER)
        self.assertEqual(cert['horizons'],[]);checked(cert)

    def test_added_horizon_exits_are_not_dropped(self):
        with self.assertRaisesRegex(ValueError,'exact tail'):
            S.exact_certificate(8,3,1,PARAMS,[{20:Q(1)},{20:Q(1)}],METER)

    def test_lp_produces_exact_bound_and_optimizes_joined_channels(self):
        N,y,H=29,17,5;base=S.inverse_completion(N,y,H,PARAMS,METER)
        baseline=S.exact_certificate(N,y,H,PARAMS,base['endpoints'],METER)
        horizons=S.dictionary(N,y,H,PARAMS,base,METER)
        result=S.lp_completion(N,y,H,PARAMS,horizons,METER)
        self.assertTrue(result['admitted'],result)
        cert=result['certificate'];checked(cert)
        self.assertLessEqual(Q(cert['budget']),Q(baseline['budget']))
        self.assertFalse(result['objective_optimality_proved'])
        self.assertGreater(max(horizons),4*N//PARAMS['p'])

    def test_moment_balanced_candidate_replays_and_pays_unit(self):
        N,y,H=23,15,4;base=S.inverse_completion(N,y,H,PARAMS,METER)
        horizons=S.dictionary(N,y,H,PARAMS,base,METER)
        result=S.lp_completion(N,y,H,PARAMS,horizons,METER,balanced=True)
        self.assertTrue(result['admitted'],result);cert=result['certificate'];v=checked(cert)
        for row in cert['coefficients']:
            self.assertEqual(sum((X*Q(c) for X,c in zip(cert['horizons'],row)),Q(0)),0)
        self.assertTrue(v['completion']['unit_in_short_residual'])

    def test_row_compression_keeps_all_coprime_short_integers(self):
        rows,targets,short,shape=S.constraint_rows(29,17,10,PARAMS,[1,7,17,58,79],METER)
        self.assertEqual(len(short),len([d for d in range(1,11) if gcd(d,14)==1]))
        self.assertEqual(shape['tail_checked_through'],79)
        self.assertLessEqual(len(rows),79)

    def test_failed_rationalization_is_not_a_proof(self):
        N,y,H=29,17,5;base=S.inverse_completion(N,y,H,PARAMS,METER)
        horizons=S.dictionary(N,y,H,PARAMS,base,METER)
        result=S.lp_completion(N,y,H,PARAMS,horizons,METER,max_denominator=1)
        self.assertFalse(result['admitted']);self.assertNotIn('certificate',result)

    def test_search_selects_only_exact_admitted_candidates(self):
        result=S.search_one(19,13,4,PARAMS,METER)
        self.assertFalse(result['source_mu_signs_or_prefix_values_used'])
        budgets=[Q(c['certificate']['budget']) for c in result['candidates'] if c['admitted']]
        self.assertEqual(Q(result['selected_budget']),min(budgets))
        for candidate in result['candidates']:
            if candidate['admitted']:checked(candidate['certificate'])


if __name__=='__main__':unittest.main()
