"""Synthetic signed-mixture and source-rate mutation tests; no norm data."""
import time,unittest
from copy import deepcopy
from fractions import Fraction as Q
from math import factorial,prod
from prime_bank_candidates import Meter
from flint import arb,ctx
import floor_residual_drift_045 as P
import check_floor_residual_drift_045 as C
import floor_residual_rate_review_044 as OLD_P

M=Meter(cap=50000000,seconds=180)
PM=P.Meter(cap=50000000,seconds=180)
RM=OLD_P.Meter(cap=50000000,seconds=180)
START=time.monotonic()
def spec(terms=(('1','2'),('2','-1')),a='1',theta='1/2'):
    return {'kind':'drift_mixture','a':a,'theta':theta,'terms':[{'rate':r,'weight':w} for r,w in terms]}
def old_taper(alpha='1'):
    return {'kind':'taper','coordinate':'log','alpha':alpha,'gamma':'1'}
def recipe(base):return {'id':'synthetic_drift','base':base,'auxiliary':None}
def row(n,nu,poly,mu=-1):
    terms=[{'rational':str(c),'log_n_power':str(a),'log_2_power':str(b)} for (a,b),c in sorted(poly.items())]
    terms=OLD_P.canonical_terms(terms,n)
    expansion={'status':'leading' if terms else 'flat','rate':str(nu) if terms else None,
      'coefficient':terms,'cancellation_barrier':None,'reason':'independently specified synthetic coefficient'}
    license=OLD_P.license_nonzero(terms,n,meter=RM) if terms else None
    return {'index':n,'mu':mu,'auxiliary_arithmetic':None,'expansion':expansion,
      'coefficient_limit_is_compatible':True,'status':'certified_rate_obstruction' if terms else 'OPEN',
      'nonzero_license':license,'witness':OLD_P.generate_witness(n,RM),
      'energy_rate':str(2*nu) if terms else None,
      'asymptotic_norm_lower':'liminf L^(2*nu)*norm_squared >= leading_coefficient^2/witness.denominator' if terms else None}

class DriftAdmission(unittest.TestCase):
    def test_unique_moment_synthesis_from_arbitrary_rational_rates(self):
        for rates in (['1/7','2/3','123/257'],['1','2','3','4'],['3/257']):
            s=P.synthesize_mixture(rates,theta='123/257',meter=PM)
            sorted_rates=sorted(map(Q,rates))
            for term,r in zip(s['terms'],sorted_rates):
                expected=prod((t/(t-r) for t in sorted_rates if t!=r),start=Q(1))
                self.assertEqual(Q(term['weight']),expected)
            out=C.verify_certificate(s,P.mixture_certificate(s,PM),M)
            self.assertEqual(out['order'],len(rates));self.assertTrue(out['raw_range_proved'])

    def test_nonmaximal_signed_and_positive_mixtures_keep_taylor_only(self):
        for s in (spec((('1','1/2'),('3','1/2'))),spec((('1','-1'),('2','2')))):
            cert=P.mixture_certificate(s,PM);out=C.verify_certificate(s,cert,M)
            self.assertEqual(out['order'],1);self.assertFalse(out['raw_range_proved'])
            self.assertEqual(cert['kernel_certificate']['status'],'NOT_CERTIFIED')
            bound=P.coefficient_error_bound(s,17,8,PM);C.verify_coefficient_bound(s,17,8,bound,M)
            self.assertIsNone(bound['simplex_error_bound'])

    def test_exact_ceiling_at_boundary_and_between_integers(self):
        self.assertEqual(C.beta('1','1/2',8,M),Q(1,2))
        self.assertEqual(C.beta('1','1/2',16,M),Q(3,5))
        self.assertEqual(C.beta('1/7','1/2',3,M),Q(1,2))
        for a,theta,N in (('2/7','123/257',9),('17/13','2/3',31),('1','1/257',3)):
            b=C.beta(a,theta,N,M);L=N.bit_length();z=int(b*L);u,v=Q(theta).numerator,Q(theta).denominator
            rhs=Q(a)**v*L**u
            self.assertLess((z-1)**v,rhs);self.assertGreaterEqual(z**v,rhs);M.charge(1000)

    def test_exact_dyadic_floor_boundaries_and_unit(self):
        self.assertEqual(C.rounded_twist(4,Q(1,2),8,M),Q(1,2))
        self.assertEqual(C.rounded_twist(1,Q(123,257),8,M),1)
        for n,e in ((2,Q(1,3)),(3,Q(7,5)),(7,Q(1,257))):
            p=8;value=C.rounded_twist(n,e,p,M);k=int(value*2**p);u,v=e.numerator,e.denominator
            self.assertLessEqual(k**v*n**u,2**(p*v))
            self.assertGreater((k+1)**v*n**u,2**(p*v));M.charge(1000)

    def test_compiler_signed_sum_and_all_positive_index_domain(self):
        s=spec()
        for n,N in ((1,8),(2,8),(4,8),(9,8),(257,8),(3,16)):
            cert=P.compile_mixture(s,n,N,PM);out=C.verify_compilation(s,n,N,cert,M)
            value=2*Q(cert['terms'][0]['rounded_value'])-Q(cert['terms'][1]['rounded_value'])
            self.assertEqual(Q(out['value']),value)
            C.verify_compilation(s,n,N,str(value),M)
        # Arbitrary denominator is a genuine exponent, not an alias of an old root.
        s=spec((('1/257','1'),),theta='1/257')
        C.verify_compilation(s,2,3,P.compile_mixture(s,2,3,PM),M)

    def test_compiler_mutations_ceiling_tail_sign_and_rounding_rejected(self):
        s=spec();cert=P.compile_mixture(s,3,8,PM)
        for mutation in ('ceiling','lowerstrict','term','sign','rounding','range','domain','value'):
            bad=deepcopy(cert)
            if mutation=='ceiling':bad['beta_certificate']['ceiling']='3'
            elif mutation=='lowerstrict':bad['beta_certificate']['comparison']['lower_is_strict']=False
            elif mutation=='term':bad['terms'].pop()
            elif mutation=='sign':bad['terms'][1]['weight']='1'
            elif mutation=='rounding':bad['rounding_error_bound']='0'
            elif mutation=='range':bad['exact_rounded_range_claim']=['0','1']
            elif mutation=='domain':bad['N']=16
            else:bad['value']='1'
            with self.assertRaises(ValueError):C.verify_compilation(s,3,8,bad,M)

    def test_certificate_moments_first_nonzero_and_sign_not_nominated(self):
        s=P.synthesize_mixture(['1','2','3'],a='2/7',theta='5/7',meter=PM)
        cert=P.mixture_certificate(s,PM);out=C.verify_certificate(s,cert,M)
        self.assertEqual(cert['leading_moment'],'6');self.assertEqual(cert['leading_error_coefficient']['rational'],'8/343')
        self.assertEqual(out['coefficient_rate'],'6/7');self.assertEqual(out['energy_rate'],'12/7')
        for mutate in ('order','moment','sign','rate','vanishing','source','scope'):
            bad=deepcopy(cert)
            if mutate=='order':bad['order']=2
            elif mutate=='moment':bad['moments'][1]['value']='1'
            elif mutate=='sign':bad['leading_error_coefficient']['rational']='-8/343'
            elif mutate=='rate':bad['energy_rate']='2'
            elif mutate=='vanishing':bad['vanishing_orders']=[]
            elif mutate=='source':bad['spec']['a']='1'
            else:bad['whole_signed_norm_proved']=True
            with self.assertRaises(ValueError):C.verify_certificate(s,bad,M)

    def test_kernel_rational_identity_all_summands_and_raw_scope(self):
        s=spec();cert=P.mixture_certificate(s,PM);kernel=cert['kernel_certificate']
        self.assertEqual(kernel['numerator_polynomial_ascending'],['2','0'])
        self.assertEqual(kernel['denominator_polynomial_ascending'],['2','3','1'])
        for mutate in ('cross','denominator','range','rounded'):
            bad=deepcopy(cert);k=bad['kernel_certificate']
            if mutate=='cross':k['numerator_summands_ascending'].pop()
            elif mutate=='denominator':k['denominator_polynomial_ascending'][1]='2'
            elif mutate=='range':k['raw_range']=['-1','1']
            else:k['rounded_range_proved']=True
            with self.assertRaises(ValueError):C.verify_certificate(s,bad,M)

    def test_uniform_scalar_bound_and_small_unit_not_global_norm(self):
        for s in (spec(),spec((('1','1/2'),('2','1/2')))):
            for n in (1,2,3,17,257):
                bound=P.coefficient_error_bound(s,n,8,PM);out=C.verify_coefficient_bound(s,n,8,bound,M)
                value=C.mixture_value(s,n,8,M)
                self.assertLessEqual(abs(1-value),Q(out['total_error_bound']))
                self.assertFalse(out['whole_signed_norm_proved']);self.assertFalse(out['norm_convergence_proved'])
                if n==1:self.assertEqual(out['total_error_bound'],'0')
        s=spec();bound=P.coefficient_error_bound(s,3,8,PM)
        for key in ('raw_error_bound','total_error_bound','rounding_error_bound','taylor_error_bound'):
            bad=deepcopy(bound);bad[key]='0'
            with self.assertRaises(ValueError):C.verify_coefficient_bound(s,3,8,bad,M)

    def test_local_leading_calibration_in_real_exponential_parameter(self):
        # 2exp(-u)-exp(-2u) = 1-(1-exp(-u))^2, hence (1-P)/u² ->1.
        # This is a generic scalar calibration, not a Mobius norm measurement.
        with ctx.workprec(256):
            for denominator in (16,128,1024):
                u=arb(1)/denominator;value=2*(-u).exp()-(-2*u).exp();ratio=(1-value)/(u*u)
                self.assertTrue(ratio>1-2*u);self.assertTrue(ratio<1);M.charge(256*12)
        cert=P.mixture_certificate(spec(),PM)
        self.assertEqual(cert['leading_error_coefficient'],{'rational':'1','log_n_power':'2'})

    def test_source_bound_rate_n3_and_exact_higher_columns(self):
        s=spec();r=recipe(s);candidate=row(3,Q(1),{(Q(2),Q(0)):Q(-1)})
        out=C.verify_rate_candidate(r,3,candidate,meter=M)
        self.assertEqual(out['energy_rate'],'2');self.assertFalse(out['uniform_upper_bound_proved'])
        alpha,den=C.OLD.verify_witness(candidate['witness'],M)
        self.assertEqual(den,20)
        for n in (4,7,257,10000):
            self.assertEqual(sum(a*Q(k%n,n) for k,a in alpha.items()),0);M.charge(100)
        self.assertEqual(sum(a for k,a in alpha.items() if k>=2),0)

    def test_n2_logs_normalized_and_mobius_square_zero(self):
        r=recipe(spec())
        n2=row(2,Q(1),{(Q(2),Q(0)):Q(-1)})
        C.verify_rate_candidate(r,2,n2,meter=M)
        self.assertEqual(n2['expansion']['coefficient'][0]['log_n_power'],'0')
        n4=row(4,Q(1),{},mu=0);out=C.verify_rate_candidate(r,4,n4,meter=M)
        self.assertIsNone(out['energy_rate'])
        bad=deepcopy(n4);bad['status']='certified_rate_obstruction';bad['energy_rate']='2'
        with self.assertRaises(ValueError):C.verify_rate_candidate(r,4,bad,meter=M)

    def test_product_with_old_taper_retains_all_signed_leading_terms(self):
        r=recipe({'kind':'product','left':spec(),'right':old_taper()})
        candidate=row(3,Q(1),{(Q(1),Q(-1)):Q(-1),(Q(2),Q(0)):Q(-1)})
        C.verify_rate_candidate(r,3,candidate,meter=M)
        self.assertEqual(len(candidate['expansion']['coefficient']),2)
        bad=deepcopy(candidate);bad['expansion']['coefficient'].pop()
        with self.assertRaises(ValueError):C.verify_rate_candidate(r,3,bad,meter=M)
        r=recipe({'kind':'product','left':spec(),'right':old_taper('1/3')})
        candidate=row(3,Q(1,3),{(Q(1,3),Q(-1,3)):Q(-1)})
        self.assertEqual(C.verify_rate_candidate(r,3,candidate,meter=M)['energy_rate'],'2/3')

    def test_source_swaps_missing_unit_tail_and_false_payment_rejected(self):
        r=recipe(spec());candidate=row(3,Q(1),{(Q(2),Q(0)):Q(-1)})
        for mutate in ('sign','mu','power','rate','tail','unit','source','auxiliary','scope'):
            bad=deepcopy(candidate);rr=deepcopy(r)
            if mutate=='sign':bad['expansion']['coefficient'][0]['rational']='1'
            elif mutate=='mu':bad['mu']=1
            elif mutate=='power':bad['expansion']['coefficient'][0]['log_n_power']='1'
            elif mutate=='rate':bad['energy_rate']='1'
            elif mutate=='tail':bad['witness']['cells'][0]['alpha']='-2'
            elif mutate=='unit':bad['witness']['constant']='1'
            elif mutate=='source':rr['base']['a']='2'
            elif mutate=='auxiliary':rr['auxiliary']={'channel':'one','coefficient':'1','envelope':{}}
            else:bad['status']='uniform_upper_bound_proved'
            with self.assertRaises(ValueError):C.verify_rate_candidate(rr,3,bad,meter=M)

    def test_arbitrary_denominator_local_order_and_external_charge_only(self):
        r=recipe(spec((('1/257','1'),),a='2/7',theta='123/257'))
        # P-1 leading coefficient is -(2/1799)*logn, nu134/257.
        candidate=row(3,Q(134,257),{(Q(1),Q(0)):Q(-2,1799)})
        class ChargeOnly:
            def __init__(self):self.operations=0
            def charge(self,n=1):self.operations+=n
        meter=ChargeOnly();out=C.verify_rate_candidate(r,3,candidate,meter=meter);M.charge(meter.operations)
        self.assertEqual(out['energy_rate'],'268/257');self.assertGreater(meter.operations,0)

    def test_old_ordinary_candidate_delegation_preserves_old_scope(self):
        r=recipe(old_taper('1/3'));candidate=OLD_P.review_recipe(r,max_index=3,meter=RM)['target_candidates'][1]
        self.assertEqual(C.verify_rate_candidate(r,3,candidate,meter=M)['energy_rate'],'2/3')

    def test_schema_bool_float_alias_and_resource_limits_fail_closed(self):
        for mutate in ('a','theta','rates','unit','weight','count','alias'):
            s=spec()
            if mutate=='a':s['a']='0'
            elif mutate=='theta':s['theta']='1'
            elif mutate=='rates':s['terms'][1]['rate']='1'
            elif mutate=='unit':s['terms'][0]['weight']='1'
            elif mutate=='weight':s['terms'][0]['weight']='0'
            elif mutate=='count':s['terms']=s['terms']*5
            else:s['a']='2/2'
            with self.assertRaises(ValueError):C.verify_spec(s,M)
        for N in (True,2.0,1):
            with self.assertRaises(ValueError):C.beta('1','1/2',N,M)
        with self.assertRaises(ValueError):C.rounded_twist(2,Q(1,1000000),8,M)
        with self.assertRaises(ValueError):C.beta('1','1/1000000',8,M)
        with self.assertRaises(OverflowError):C.verify_spec(spec(),Meter(cap=1,seconds=180))

    def test_symbolic_obstruction_explicitly_requires_source_cell_proof(self):
        s=spec();out=C.verify_obstruction(s,P.mixture_certificate(s,PM),M)
        self.assertTrue(out['actual_source_obstruction_requires_cell_witness'])
        self.assertTrue(out['fixed_index_coefficient_order_only']);self.assertFalse(out['RH_refuted'])


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_floor_residual_drift_045 operations='+str(M.operations+PM.operations+RM.operations)+
      ' checker_operations='+str(M.operations)+' fixture_operations='+str(PM.operations+RM.operations)+
      ' elapsed_seconds='+str(time.monotonic()-START),flush=True)
if __name__=='__main__':unittest.main()
