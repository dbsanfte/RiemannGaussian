"""Symbolic046 guard and analytic scope mutations; no source/norm data."""
from copy import deepcopy
from fractions import Fraction as Q
import time,unittest
from prime_bank_candidates import Meter as ExternalMeter
import floor_residual_global_rate_guard_046 as P
import check_floor_residual_global_rate_guard_046 as C
import floor_residual_drift_045 as DRIFT_P

M=ExternalMeter(cap=50000000,seconds=180)
PM=P.Meter(cap=50000000,seconds=180)
DM=DRIFT_P.Meter(cap=50000000,seconds=180)
START=time.monotonic()

def request(theta='3/4',eta='1/2',q=2,b='1/2',domain='all_integer',terms=None):
    return {'recipe':{'id':'symbolic_toy','base':{'kind':'drift_mixture','a':'2/7','theta':theta,
       'terms':[{'rate':r,'weight':w} for r,w in (terms or [('1','2'),('2','-1')])]},'auxiliary':None},
      'q':q,'b':b,'domain':{'kind':domain,'minimum':8},'rounding':deepcopy(C.ROUNDING),'bound':{'A':'1/4','eta':eta}}
def fixture(r):return P.build_guard(r,PM)
def verify(r,cert):return C.verify_guard(r,cert,M)
def add(z,w):return z[0]+w[0],z[1]+w[1]
def mul(z,w):return z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0]
def div(z,w):
    d=w[0]*w[0]+w[1]*w[1]
    return (z[0]*w[0]+z[1]*w[1])/d,(z[1]*w[0]-z[0]*w[1])/d

def power(z,d):
    ans=(Q(1),Q(0))
    for _ in range(d):ans=mul(ans,z)
    return ans

class GlobalRateAdmission(unittest.TestCase):
    def test_supported_actual_source_rate_is_refuted_without_RH_claim(self):
        r=request();out=verify(r,fixture(r))
        self.assertTrue(out['verified']);self.assertTrue(out['advertised_uniform_rate_refuted'])
        self.assertEqual(out['refuted_eta_strictly_above'],'1/4')
        self.assertEqual(out['formal_boundary_layer_halfwidth'],'1/6')
        self.assertFalse(out['RH_proved']);self.assertFalse(out['RH_refuted'])
        self.assertFalse(out['actual_lower_constant_and_threshold_computed'])

    def test_geometric_chain_composite_dilation_and_signed_parent(self):
        for q,b in ((3,'-1'),(4,'3/2'),(6,'-2'),(7,'0')):
            r=request(q=q,b=b,domain='geometric_chain');cert=fixture(r);verify(r,cert)
            self.assertEqual(cert['exact_conditions']['contraction_margin_q_minus_b_squared'],str(q-Q(b)**2))
            self.assertEqual(cert['rate_contradiction']['uniform_domain_refuted'],r['domain'])
            self.assertEqual(cert['beta_transfer']['child_level_gap_upper_bound'],(q-1).bit_length())

    def test_arbitrary_denominators_exact_strict_margins(self):
        r=request(theta='193/257',eta='65/257');r['recipe']['base']['a']='123/257'
        r['recipe']['base']['terms']=[{'rate':'1/257','weight':'1'}]
        cert=fixture(r);out=verify(r,cert)
        self.assertEqual(out['refuted_eta_strictly_above'],'64/257')
        self.assertEqual(cert['exact_conditions']['rate_gap_eta_minus_beta_power'],'1/257')
        self.assertEqual(cert['exact_conditions']['rmin'],'1/257')

    def test_theta_half_or_below_is_not_licensed_by_imported_tail_rule(self):
        for theta in ('1/2','123/257','1/3'):
            r=request(theta=theta);cert=fixture(r);out=verify(r,cert)
            self.assertEqual(out['status'],'UNSUPPORTED');self.assertFalse(out['advertised_uniform_rate_refuted'])
            bad=fixture(request());bad['request']=r
            with self.assertRaises(ValueError):verify(r,bad)

    def test_eta_equality_and_slower_rates_remain_open(self):
        for eta in ('1/4','1/257'):
            r=request(eta=eta);cert=fixture(r);out=verify(r,cert)
            self.assertEqual(out['status'],'UNSUPPORTED')
            self.assertEqual(cert['unpaid_rate_status'],'OPEN')
        r=request(eta='65/257',theta='193/257');verify(r,fixture(r))

    def test_external_taper_product_and_auxiliary_never_stripped(self):
        r=request();original=deepcopy(r['recipe']['base'])
        bases=[{'kind':'product','left':original,'right':{'kind':'unit'}},
          {'kind':'taper','coordinate':'cutoff','alpha':'2/7','gamma':'1'}]
        for base in bases:
            rr=deepcopy(r);rr['recipe']['base']=base
            self.assertEqual(verify(rr,fixture(rr))['status'],'UNSUPPORTED')
        rr=deepcopy(r);rr['recipe']['auxiliary']={'channel':'one','coefficient':'1','envelope':{}}
        self.assertEqual(verify(rr,fixture(rr))['status'],'UNSUPPORTED')
        with self.assertRaises(ValueError):verify(rr,fixture(r))

    def test_high_moment_cancellation_cannot_evade_global_beta_window(self):
        r=request();s=DRIFT_P.synthesize_mixture(['1','2','3','4'],a='2/7',theta='3/4',meter=DM)
        r['recipe']['base']=s;cert=fixture(r);verify(r,cert)
        local=DRIFT_P.mixture_certificate(s,DM)
        self.assertEqual(local['order'],4);self.assertEqual(local['energy_rate'],'2')
        self.assertEqual(cert['exact_conditions']['beta_power'],'1/4')
        self.assertFalse(cert['proof_guards']['moment_cancellation_required_for_lower_rate'])
        # Exact simple-zero rational boundary profile; no zero is evaluated.
        terms=[(Q(t['rate']),Q(t['weight'])) for t in s['terms']]
        for z in (Q(0),Q(1,257),Q(3,2)):
            f=1-z*sum(w/(r+z) for r,w in terms)
            denominator=Q(1)
            for j in (1,2,3,4):denominator*=z+j
            self.assertEqual(f,24/denominator);M.charge(1000)

    def test_boundary_layer_is_nonzero_for_arbitrary_multiplicities(self):
        r=request();out=verify(r,fixture(r));delta=Q(out['formal_boundary_layer_halfwidth'])
        terms=[(Q(t['rate']),Q(t['weight'])) for t in r['recipe']['base']['terms']]
        for d in (1,2,3,9):
            for v in (Q(0),delta,-delta,delta/2):
                z=(Q(0),v);correction=(Q(0),Q(0))
                for rate,weight in terms:
                    ratio=div(power(z,d),power((rate,v),d))
                    correction=add(correction,(weight*ratio[0],weight*ratio[1]))
                self.assertLessEqual(correction[0]**2+correction[1]**2,Q(1,4));M.charge(2000)

    def test_moving_child_ceiling_is_recomputed_not_identified_with_parent(self):
        s=request()['recipe']['base'];s['a']='1'
        parent=C.DRIFT.beta(s['a'],s['theta'],8,M);child=C.DRIFT.beta(s['a'],s['theta'],16,M)
        self.assertNotEqual(parent,child)
        r=request();cert=fixture(r)
        for key,value in (('child_recomputed',False),('child_beta_ratio','beta_(qN)=beta_N'),('child_level_gap_upper_bound',0)):
            bad=deepcopy(cert);bad['beta_transfer'][key]=value
            with self.assertRaises(ValueError):verify(r,bad)

    def test_complete_mellin_harmonic_virtual_unit_and_parent_crosses_required(self):
        r=request();cert=fixture(r)
        changes=[('target','[1-zeta(s)*A_N(s)]/s'),('forcing','child only'),
          ('unit','unit discarded'),('indicator_and_signed_parent_child_terms_retained',False)]
        for key,value in changes:
            bad=deepcopy(cert);bad['whole_mellin'][key]=value
            with self.assertRaises(ValueError):verify(r,bad)
        bad=deepcopy(cert);del bad['RH_true_branch']['paid_harmonic']
        with self.assertRaises(ValueError):verify(r,bad)

    def test_imported_theorem_cannot_be_changed_or_promoted_unconditional(self):
        r=request();cert=fixture(r)
        for key,value in (('hypothesis','none'),('location','Theorem2'),('primary_source','https://example.com'),('imported_not_discovered',False)):
            bad=deepcopy(cert);bad['RH_true_branch']['imported_theorem'][key]=value
            with self.assertRaises(ValueError):verify(r,bad)
        bad=deepcopy(cert);bad['RH_true_branch']['imported_theorem']['bound']='|M(x)|<=C sqrt(x)'
        with self.assertRaises(ValueError):verify(r,bad)

    def test_all_infinite_tail_and_beta_inverse_loss_required(self):
        r=request();cert=fixture(r)
        mutations=[('exact_formula','sum_(N<n<=2N) only'),('bound','O(exp(-beta log N))'),
          ('monotonicity','decreases for every y>1'),('scope','z on Re=1/2'),
          ('series_scope','reciprocal zeta series converges at rho'),
          ('uniformity','global critical-line tail energy bound proved')]
        for key,value in mutations:
            bad=deepcopy(cert);bad['RH_true_branch']['tail'][key]=value
            with self.assertRaises(ValueError):verify(r,bad)

    def test_zero_multiplicity_no_RH_assumption_circularity_or_analytic_refutation(self):
        r=request();cert=fixture(r)
        bad=deepcopy(cert);bad['RH_true_branch']['zero_simplicity_assumed']=True
        with self.assertRaises(ValueError):verify(r,bad)
        bad=deepcopy(cert);bad['RH_false_branch']['no_source_tail_or_RH_assumption']=False
        with self.assertRaises(ValueError):verify(r,bad)
        for key in ('RH_proved','RH_refuted','norms_evaluated','source_values_evaluated'):
            bad=deepcopy(cert);bad[key]=True
            with self.assertRaises(ValueError):verify(r,bad)

    def test_no_computed_lower_constant_threshold_or_finite_norm_licensing(self):
        r=request();cert=fixture(r)
        for key in ('numerical_lower_constant_claimed','explicit_failing_support_claimed'):
            bad=deepcopy(cert);bad[key]=True
            with self.assertRaises(ValueError):verify(r,bad)
        bad=deepcopy(cert);bad['unconditional_lower_bound']['constants']='c=1,N_star=64 from samples'
        with self.assertRaises(ValueError):verify(r,bad)
        bad=deepcopy(cert);bad['proof_guards']['global_truncation_energy_paid']=True
        with self.assertRaises(ValueError):verify(r,bad)

    def test_changed_source_rate_domain_and_exact_prices_rejected(self):
        r=request();cert=fixture(r)
        for mutate in ('source','request','eta','margin','weights','ratio','domain','A'):
            bad=deepcopy(cert)
            if mutate=='source':bad['source_binding']['source']='arbitrary signs'
            elif mutate=='request':bad['request']['recipe']['base']['a']='1'
            elif mutate=='eta':bad['exact_conditions']['rate_gap_eta_minus_beta_power']='1'
            elif mutate=='margin':bad['exact_conditions']['contraction_margin_q_minus_b_squared']='2'
            elif mutate=='weights':bad['exact_conditions']['sum_abs_weights']='1'
            elif mutate=='ratio':bad['exact_conditions']['squared_recurrence_ratio']='0'
            elif mutate=='domain':bad['rate_contradiction']['uniform_domain_refuted']['kind']='finite_training'
            else:bad['rate_contradiction']['constant_A_over_a']='0'
            with self.assertRaises(ValueError):verify(r,bad)

    def test_unstable_parent_wrong_rounding_or_nonunit_profile_unsupported(self):
        variants=[]
        r=request(q=4,b='2');variants.append(r)
        r=request();r['rounding']['bits_multiplier']=8;variants.append(r)
        r=request();r['recipe']['base']['terms'][0]['weight']='1';variants.append(r)
        r=request();r['recipe']['base']['terms'][1]['rate']='1';variants.append(r)
        r=request();r['recipe']['base']['terms'][0]['rate']='0';variants.append(r)
        r=request();r['recipe']['base']['terms'][0]['weight']='0';variants.append(r)
        for r in variants:
            self.assertEqual(verify(r,fixture(r))['status'],'UNSUPPORTED')

    def test_malformed_float_bool_alias_inputs_never_refute(self):
        variants=[]
        for field,value in (('q',True),('b',0.5),('b','2/4')):
            r=request();r[field]=value;variants.append(r)
        r=request();r['domain']['minimum']=True;variants.append(r)
        r=request();r['bound']['A']='0';variants.append(r)
        r=request();r['bound']['eta']='0';variants.append(r)
        for r in variants:self.assertEqual(verify(r,fixture(r))['status'],'UNSUPPORTED')
        r=request(theta='1/2');bad=fixture(r);bad['advertised_uniform_rate_refuted']=True
        with self.assertRaises(ValueError):verify(r,bad)

    def test_charge_only_meter_and_operation_cap(self):
        class ChargeOnly:
            def __init__(self):self.operations=0
            def charge(self,n=1):self.operations+=n
        r=request();cert=fixture(r);m=ChargeOnly();out=C.verify_guard(r,cert,m)
        self.assertTrue(out['verified']);self.assertGreater(m.operations,0);M.charge(m.operations)
        with self.assertRaises(OverflowError):C.verify_guard(r,cert,C.Meter(cap=1))

def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_floor_residual_global_rate_guard_046 operations='+str(M.operations+PM.operations+DM.operations)+
      ' checker_operations='+str(M.operations)+' fixture_operations='+str(PM.operations+DM.operations)+
      ' elapsed_seconds='+str(time.monotonic()-START),flush=True)
if __name__=='__main__':unittest.main()
