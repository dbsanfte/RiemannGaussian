"""New synthetic flow/compiler tests; no061 scientific source evaluated."""
from copy import deepcopy
from fractions import Fraction as Q
from math import exp,gamma,log
import unittest

import mobius_fractional_flow_061 as F
import mobius_mass_conservation_060 as M
from mobius_transport_search_059 import source_kernel_expressions

METER=F.Meter()
PARAMS={'alpha':'1/257','gamma':'1/3','tau':'3/4','primes':[2,7],'p':2,'q':7}


def fixture():
    return source_kernel_expressions(2,7),M.signature(PARAMS,METER)


def tokens():
    return [{'d':1,'profile':'P','mu':1,'kernel_sign':1,'sign':1},
            {'d':3,'profile':'Q','mu':-1,'kernel_sign':1,'sign':-1},
            {'d':5,'profile':'Q','mu':-1,'kernel_sign':1,'sign':-1}]


class FlowTests(unittest.TestCase):
    def test_inferred_columns_and_positive_kernel_cone(self):
        kernels,compiled=fixture();flow=F.infer_masses(PARAMS,kernels,compiled,METER)
        self.assertEqual([c['base'] for c in flow['columns']],[2,7])
        self.assertEqual(flow['columns'][0]['identity']['profile_coefficients'],['1','0','1','1'])
        self.assertEqual(flow['columns'][1]['identity']['profile_coefficients'],['0','1','-1','1'])
        self.assertEqual(flow['positive_prefixes']['D'],['1','0'])
        self.assertEqual(Q(flow['head_coefficient']),Q(84)/(3-Q(1,257)))

    def test_cutoff_search_uses_proved_powers(self):
        kernels,compiled=fixture();result=F.discover(PARAMS,kernels,compiled,12,METER)
        self.assertIn('1/257',result['cutoff_grid'])
        self.assertEqual(result['selected']['head_theta'],'1/2')
        self.assertEqual(result['selected']['exit_rho'],'3/4')
        self.assertTrue(any(not row['admissible_square_root_components'] for row in result['cutoff_rows']))
        self.assertFalse(result['source_values_used'])
        with self.assertRaises(OverflowError):F.discover(PARAMS,kernels,compiled,32,METER)

    def test_bad_kernel_conservation_or_positivity_rejected(self):
        kernels,compiled=fixture();bad=deepcopy(kernels);bad['S']=[[2,'2'],[7,'1']]
        with self.assertRaisesRegex(ValueError,'conservation'):F.infer_masses(PARAMS,bad,compiled,METER)
        bad=deepcopy(kernels);bad['D']=[[2,'-1'],[7,'1']]
        with self.assertRaisesRegex(ValueError,'prefix cone'):F.infer_masses(PARAMS,bad,compiled,METER)

    def test_fractional_primal_dual_and_nonterminal_leftover(self):
        exact=F.rational_transport([1,2,4],['3/2','-1','-1/2'],['1','1/2','1/4'],METER)
        self.assertEqual(exact['prefix_cost'],'7/8');self.assertEqual(exact['leftover_mass'],'0')
        unbalanced=F.rational_transport([1,2],['2','-1'],['1','1/2'],METER)
        self.assertEqual(unbalanced['prefix_cost'],'3/2')
        self.assertEqual(unbalanced['leftover_cost'],'1');self.assertEqual(unbalanced['terminal_term'],'1/2')
        empty=F.rational_transport([],[],[],METER);self.assertEqual(empty['prefix_cost'],'0')

    def test_exact_prefixes_and_distinct_root_ratios(self):
        kernels,_=fixture();table=F.prefix_table(tokens(),kernels,METER)
        self.assertEqual([r['coefficients'] for r in table['rows']],[[1,0],[1,-1],[1,-2]])
        self.assertEqual(F.root_ratios(table,METER),[Q(1,2)])
        extra={'rows':[{'coefficients':[1,-3]},{'coefficients':[-2,4]},{'coefficients':[1,1]}]}
        self.assertEqual(F.root_ratios(extra,METER),[Q(1,3),Q(1,2)])

    def test_piecewise_quadrature_against_independent_scalar_integral(self):
        from scipy.integrate import quad
        kernels,_=fixture()
        result=F.evaluate_saved_tokens(64,PARAMS,kernels,tokens(),'1/2','3/4',16,METER)
        alpha=float(Q(PARAMS['alpha']));lo=64**(-1/3);hi=0.75
        root=log(2)/log(7/2)
        def scalar(t):
            a,b=2**(-t),7**(-t)
            variation=a*(1-3**(-t))+abs(a-b)*(3**(-t)-5**(-t))+abs(a-2*b)*5**(-t)
            METER.charge(256)
            return (1-2**(-t))*(1-7**(-t))*variation*t**(-1-alpha)/gamma(1-alpha)
        reference=quad(scalar,lo,hi,points=[root],epsabs=1e-13,epsrel=1e-12)[0]
        self.assertAlmostEqual(result['total_float'],reference,places=12)
        self.assertEqual(result['interior_breakpoints'],1)
        self.assertAlmostEqual(sum(result[k] for k in ('head_float','core_float','exit_float','terminal_float')),reference,places=12)

    def test_empty_band_empty_source_and_rational_cuts(self):
        kernels,_=fixture()
        empty=F.evaluate_saved_tokens(2,dict(PARAMS,tau='1/2'),kernels,tokens()[:1],'1/257','2/7',meter=METER)
        self.assertTrue(empty['empty_band']);self.assertEqual(empty['total_float'],0)
        empty=F.evaluate_saved_tokens(64,PARAMS,kernels,[],'1/257','2/7',meter=METER)
        self.assertTrue(empty['empty_source']);self.assertEqual(empty['total_float'],0)

    def test_independent_compiled_certificate_admission(self):
        import check_mobius_fractional_flow_061 as C
        kernels,compiled=fixture();cert=F.discover(PARAMS,kernels,compiled,4,METER)['selected']
        cm=C.Meter();verdict=C.verify_fractional_flow(cert,cm)
        self.assertTrue(verdict['head_bound_proved']);self.assertTrue(verdict['exit_residual_bound_proved'])
        self.assertFalse(verdict['core_prefix_bound_proved'])
        bad=deepcopy(cert);bad['exit_coefficient']='0'
        with self.assertRaises(ValueError):C.verify_fractional_flow(bad,cm)
        METER.charge(cm.operations)


if __name__=='__main__':unittest.main()
