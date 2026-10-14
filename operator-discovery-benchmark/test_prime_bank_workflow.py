"""Proof-scope, exact support and signed reporting tests; tiny synthetic data."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest
from flint import arb,ctx

import prime_bank_language as L
import prime_bank_measurements as M
import run_prime_bank_search as W

METERS=[]


class Meter:
    def __init__(self):self.operations=0;METERS.append(self)
    def charge(self,n=1):
        if type(n) is not int or n<0:raise ValueError('strict charge')
        self.operations+=n


def obligation():
    return json.loads((Path(__file__).resolve().parent/'candidate10_prime_bank_obligation.json').read_text())


def synthetic():
    # Large cancelling signed atoms and a nonzero independently supplied R.
    out=dict(H=31,theta='3/4')
    out.update({k:[arb(0)]*32 for k in ('K','L0','Lu','Lv','reduced','R','main')})
    for n in range(1,32):
        out['K'][n]=arb(2*n);out['L0'][n]=arb(3*n);out['Lu'][n]=arb(n+1)
        out['Lv'][n]=arb(n%2);out['main'][n]=arb(1)
        out['reduced'][n]=arb(0);out['R'][n]=arb(n%2)
    return out


def tearDownModule():
    print('SYNTHETIC_WORK module=test_prime_bank_workflow operations='+str(sum(m.operations for m in METERS)))


class WorkflowTests(unittest.TestCase):
    def setUp(self):ctx.prec=128

    def test_generic_fractional_exponents_and_scope(self):
        m=Meter()
        for b,theta,power,regime in (
            ('2/3','3/4','0','bounded_block_energy'),
            ('2/3','4/5','-1/15','finite_critical_integral'),
            ('3/4','2/3','0','bounded_block_energy'),
            ('1/6','5/6','13/18','positive_power_remaining'),
            ('0','1/2','1','positive_power_remaining')):
            cert=L.bank_bound(b,theta,'7',m)
            self.assertEqual(cert['energy_power'],power);self.assertEqual(cert['regime'],regime)
            self.assertTrue(L.verify_bound(cert,m));self.assertFalse(cert['complete_target_proved'])
            altered=deepcopy(cert);altered['energy_power']='-9'
            with self.assertRaises(ValueError):L.verify_bound(altered,m)
        for args in (('1','3/4','9'),('1/3','1/3','9'),('1/3','3/4','0'),('2/6','3/4','9')):
            with self.assertRaises(ValueError):L.bank_bound(*args,meter=m)

    def test_factor_search_and_full_cutoff_cancellation(self):
        m=Meter()
        fact=L.factor_unit_difference([['0','a','1'],['1/6','a','-2'],['1/3','a','1']],m)
        self.assertEqual(fact['multiplicity'],2);self.assertEqual(fact['step'],'1/6')
        self.assertEqual(fact['quotient'],[['0','a','1']])
        fact=L.factor_unit_difference([['0','a','1'],['1/2','a','1']],m)
        self.assertEqual(fact['multiplicity'],0)
        self.assertEqual(L.cutoff_change(['K','-L0','Lu','Lv','-main'],m),['0','0','0'])
        self.assertEqual(L.cutoff_change(['K','-L0','Lu','-main'],m),['0','0','1'])
        self.assertNotEqual(L.cutoff_change(['-L0','Lu','-main'],m),['0','0','1'])
        with self.assertRaises(ValueError):L.cutoff_change(['K','K'],m)

    def test_obligation_drives_exhaustive_branch_selection(self):
        m=Meter();compiled=L.catalogue(obligation(),list(reversed(W.MENU)),m)
        self.assertEqual(L.select_regimes(compiled,m),['3/4','4/5'])
        for p in compiled['programs']:
            self.assertEqual(len(p['elimination_search']),7)
            for cert in p['bounds'].values():self.assertTrue(L.verify_bound(cert,m))
            self.assertEqual(p['paid_branches'],['Lv'] if Q(p['theta'])>=Q(3,4) else [])
            self.assertFalse(p['complete_uniform_bound_proved'])
        self.assertEqual(compiled['source_factorization']['multiplicity'],1)
        self.assertFalse(compiled['source_factorization']['uniform_improvement_proved'])
        altered=obligation();altered['scope']['source']='random signs'
        with self.assertRaises(ValueError):L.catalogue(altered,W.MENU,m)
        altered=obligation();altered['operator']['formula']='another operator'
        with self.assertRaises(ValueError):L.catalogue(altered,W.MENU,m)
        altered=obligation();altered['definitions']['z_u']='0'
        with self.assertRaises(ValueError):L.catalogue(altered,W.MENU,m)
        self.assertTrue(compiled['finite_evidence_cannot_discharge_uniform_premises'])

    def test_generic_low_smooth_prefix_and_critical_norm(self):
        m=Meter()
        cert=L.smooth_prefix_bound('1/6','5/6','9',m)
        self.assertEqual(cert['critical_integral_factor'],'39/16')
        self.assertTrue(cert['cofinal_padding'])
        critical=L.smooth_prefix_bound('1/2','3/4','9',m)
        self.assertEqual(critical['energy_power'],'0');self.assertIsNone(critical['critical_integral_factor'])
        self.assertFalse(L.smooth_prefix_bound('2/3','3/4','9',m)['cofinal_padding'])
        with self.assertRaises(ValueError):L.smooth_prefix_bound('2/3','1/2','9',m)

    def test_cofactor_moment_transfer_retains_its_proof_premise(self):
        m=Meter()
        rule=L.weighted_moment_bank_bound('2/3','3/4','2/3',m)
        self.assertEqual(rule['energy_power'],'0');self.assertEqual(rule['pointwise_log_degree'],-1)
        self.assertTrue(rule['finite_critical_integral']);self.assertTrue(rule['conditional_on_cofactor_moment'])
        self.assertFalse(rule['complete_target_proved'])
        # Changing the supplied cofactor growth genuinely changes the conclusion.
        costly=L.weighted_moment_bank_bound('2/3','3/4','1',m)
        self.assertEqual(costly['energy_power'],'1/6');self.assertFalse(costly['finite_critical_integral'])
        derived=L.difference_cofactor_moment('1/6','1/2','1/3','6',m)
        self.assertEqual(derived['B']['rational_factor'],'18')
        self.assertFalse(derived['full_signed_source_bound_assumed'])
        with self.assertRaises(ValueError):L.difference_cofactor_moment('2/3','1/3','1/3','9/2',m)
        with self.assertRaises(ValueError):L.weighted_moment_bank_bound('0','3/4','1',m)

    def test_exact_support_kernel_against_direct_indicator_intersections(self):
        m=Meter()
        def largest(n):
            return max(p for p in (2,3,5,7,11,13,17,19) if n%p==0)
        for text in ('1/2','2/3','3/4','4/5','5/6'):
            theta=Q(text)
            for X in (1,2,5,8):
                for h in range(2,17):
                    r=largest(h)
                    for q in (2,3,5,7,11):
                        for k in (2,3,4):
                            expected=0
                            for n in range(X,2*X):
                                m.charge(6)
                                expected+=int(h<=n and r**theta.denominator<=n**theta.numerator and
                                              q*k<=n and q**theta.denominator>n**theta.numerator)
                            actual=L.overlap_kernel(X,h,r,q,k,text,m)
                            self.assertEqual(actual,expected,(X,h,q,k,text))
                            if actual:self.assertGreater(q,r);self.assertLess(k,q);self.assertNotEqual(h%q,0)
                            if q==r:self.assertEqual(actual,0)

    def test_gram_keeps_all_signed_cross_terms_and_child_boundaries(self):
        m=Meter();values=synthetic();self.assertEqual(M.check_identity(values,m),31)
        row=M.measure(values,8,m);numeric=row['numeric']
        self.assertEqual(len(numeric),65)
        for prefix,X in (('parent',8),('child',16)):
            direct=Q(sum(n%2 for n in range(X,2*X)),X*X)
            self.assertTrue(numeric[prefix+'.energy_R'].contains(arb(direct.numerator)/direct.denominator))
            self.assertEqual(numeric[prefix+'.energy_reduced'],0)
            self.assertLess(numeric[prefix+'.signed_cross'],0)
            self.assertGreater(numeric[prefix+'.energy_diagonal'],numeric[prefix+'.energy_R'])
            squares=lambda t:t*(t+1)*(2*t+1)//6
            expected=Q(-6*(squares(2*X-1)-squares(X-1)),X*X)
            self.assertTrue(numeric[prefix+'.G_0_1'].contains(arb(expected.numerator)/expected.denominator))
        self.assertTrue(numeric['drift_R']<0)
        self.assertFalse(row['uniform_signed_bound_proved']);self.assertIsNone(row['fitted_constant'])
        with self.assertRaises(ValueError):M.measure(values,9,m)
        values['R'][23]+=1
        with self.assertRaises(ArithmeticError):M.check_identity(values,m)

    def test_independent_comparison_rejects_missing_wide_or_changed_data(self):
        m=Meter();current=M.measure(synthetic(),4,m);saved=M.encode(current)
        self.assertEqual(M.compare(saved,current,m),65)
        for field,value in (('parent.energy_R','999'),('parent.energy_R','[0 +/- 999]')):
            altered=deepcopy(saved);altered['numeric'][field]=value
            with self.assertRaises(ArithmeticError):M.compare(altered,current,m)
        altered=deepcopy(saved);del altered['numeric']['gram_drift_0_1']
        with self.assertRaises(ValueError):M.compare(altered,current,m)
        altered=deepcopy(saved);altered['uniform_signed_bound_proved']=True
        with self.assertRaises(ValueError):M.compare(altered,current,m)

    def test_coverage_is_strict_and_feedback_preserves_open_target(self):
        m=Meter()
        self.assertEqual(M.coverage('3/4',256,257,m)['necessary_cofactor_max_first'],3)
        self.assertEqual(M.coverage('3/4',257,258,m)['necessary_cofactor_max_first'],4)
        compiled=L.catalogue(obligation(),W.MENU,m);target=W.feedback(compiled)
        self.assertEqual(target['status'],'open');self.assertFalse(target['complete_uniform_bound_proved'])
        self.assertEqual(target['equivalence_class'],obligation()['id'])
        self.assertIn('K',target['energy_atoms']);self.assertIn('-main',target['energy_atoms'])
        self.assertEqual(target['selected_theta'],['3/4','4/5'])


if __name__=='__main__':unittest.main()
