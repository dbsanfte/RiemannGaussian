"""Synthetic ASTs and independently justified coefficient-rate attacks."""
import time
import unittest
from copy import deepcopy
from fractions import Fraction as F
from prime_bank_candidates import Meter
import check_floor_residual_rates_044 as V
import floor_residual_rate_review_044 as P

METER=Meter(cap=50000000,seconds=180)
FIXTURE_METER=P.Meter(cap=50000000,seconds=180)
START=time.monotonic()

def unit():return {'kind':'unit'}
def taper(alpha='1/3',gamma='1',coordinate='log'):
    return {'kind':'taper','coordinate':coordinate,'alpha':alpha,'gamma':gamma}
def twist(rate='1',level=1):return {'kind':'vanishing_twist','rate':rate,'level_power':level}
def difference(left,right):return {'kind':'difference','left':left,'right':right}
def recipe(base=None,envelope=None,channel='one',coefficient='1',id='synthetic'):
    return {'id':id,'base':unit() if base is None else base,'auxiliary':None if envelope is None else
      {'channel':channel,'coefficient':coefficient,'envelope':envelope}}
def rule(r,q=2,b='1/2',eta='1',stratum='synthetic'):
    return {'family':r['id'],'q':q,'b':b,'finite_log_bound':{'A':'1/4','eta':eta},'stratum':stratum}
def selected(r,rules=None):return {'recipes':[r],'rules':[rule(r)] if rules is None else rules}
def fixture(s,max_index=6):return P.audit_selected(s,max_index=max_index,meter=FIXTURE_METER)
def verify(s,p):return V.verify(s,p,meter=METER)
def rho_cells(c,steps,k):return 1-sum(v*F(k%n,n) for n,v in c.items())-sum(v for q,v in steps.items() if k>=q)

class IndependentRateAdmission(unittest.TestCase):
    def test_log_one_third_yields_strict_two_thirds_energy_cap(self):
        r=recipe(taper());s=selected(r);p=fixture(s);out=verify(s,p)
        review=p['reviews'][0];n3=review['target_candidates'][1]
        self.assertEqual(n3['energy_rate'],'2/3')
        forcing=review['rule_reviews'][0]['forcing_candidates'][1]
        self.assertEqual(forcing['status'],'analytically_refuted')
        self.assertEqual(forcing['step_response'],'0')
        self.assertEqual(forcing['candidate']['witness']['denominator'],'20')
        self.assertTrue(out['verified']);self.assertFalse(out['convergence_proved']);self.assertFalse(out['RH_refuted'])

    def test_rate_equality_and_slower_claim_are_not_refuted_or_proved(self):
        r=recipe(taper());rules=[rule(r,eta='2/3',stratum='boundary'),rule(r,eta='1/2',stratum='slower')]
        s=selected(r,rules);p=fixture(s);verify(s,p)
        for review in p['reviews'][0]['rule_reviews']:
            self.assertEqual(review['status'],'OPEN');self.assertEqual(review['strict_eta_rejections'],[])
            self.assertFalse(review['equality_or_smaller_eta_proved'])
        bad=deepcopy(p);bad['reviews'][0]['rule_reviews'][0]['forcing_candidates'][1]['strict_rejection']=True
        with self.assertRaises(ValueError):verify(s,bad)

    def test_cell_recovery_all_columns_unit_and_steps(self):
        r=recipe(taper());p=fixture(selected(r),max_index=8)
        c={2:F(3,7),3:F(-2,5),4:F(8,11),7:F(-3,13),19:F(2,17),1000:F(-1,3)}
        steps={2:F(1,7),3:F(-2,9),5:F(3,11)}
        for row in p['reviews'][0]['target_candidates']:
            w=row['witness'];alpha,den=V.verify_witness(w,meter=METER);n=row['index']
            left=sum((a*rho_cells(c,steps,k) for k,a in alpha.items()),F(0))
            response=sum((v*sum((a for k,a in alpha.items() if k>=q),F(0)) for q,v in steps.items()),F(0))
            self.assertEqual(left,c.get(n,0)+V.arithmetic('mu',n,meter=METER)-response)
            norm_cells=sum((rho_cells(c,steps,k)**2/F(k*(k+1)) for k in alpha),F(0))
            self.assertGreaterEqual(norm_cells,left*left/den);METER.charge(2000)

    def test_witness_tail_slope_missing_column_and_unit_rejected(self):
        r=recipe(taper());s=selected(r);p=fixture(s)
        for mutate in ('slope','column','unit','denominator','scope'):
            bad=deepcopy(p);w=bad['reviews'][0]['target_candidates'][1]['witness']
            if mutate=='slope':w['cells'][0]['alpha']='-2'
            elif mutate=='column':w['cells'].pop(1)
            elif mutate=='unit':w['constant']='1'
            elif mutate=='denominator':w['denominator']='10'
            else:w['identity']='finite tested rows suffice'
            with self.assertRaises(ValueError):verify(s,bad)

    def test_arithmetic_channels_from_independent_local_formulas(self):
        def local_mu(n):
            count=0;p=2
            while p*p<=n:
                if n%p==0:
                    n//=p;count+=1
                    if n%p==0:return 0
                p+=1
            if n>1:count+=1
            return (-1)**count
        for n in (2,3,4,6,8,9,12,18,25,30):
            conv=sum(local_mu(d)*local_mu(n//d) for d in range(1,n+1) if n%d==0)
            self.assertEqual(V.arithmetic('mu_convolution_mu',n,meter=METER),conv)
            for channel in V.CHANNELS:
                r=recipe(unit(),{'kind':'log_amplitude','power':'1/3','weight':unit()},channel=channel)
                row=P.coefficient_error(r,n,meter=FIXTURE_METER)
                self.assertEqual(F(row['auxiliary_arithmetic']),V.arithmetic(channel,n,meter=METER))
            METER.charge(n*40)

    def test_cutoff_power_amplitude_and_moving_band_are_log_flat(self):
        envelopes=[{'kind':'power_amplitude','power':'1/257','weight':twist()},
          {'kind':'moving_band','cutoff_power':'123/257','weight':taper()}]
        for envelope in envelopes:
            r=recipe(taper(coordinate='cutoff'),envelope);s=selected(r);p=fixture(s);verify(s,p)
            for row in p['reviews'][0]['target_candidates']:
                self.assertEqual(row['expansion']['status'],'flat');self.assertIsNone(row['energy_rate'])
            self.assertEqual(p['reviews'][0]['rule_reviews'][0]['status'],'OPEN')

    def test_product_uses_minimum_rate_and_sums_tied_signed_constants(self):
        r=recipe({'kind':'product','left':taper('1'),'right':twist('2/7',1)})
        s=selected(r);p=fixture(s);verify(s,p)
        row=p['reviews'][0]['target_candidates'][1]
        self.assertEqual(row['energy_rate'],'2')
        self.assertEqual(len(row['expansion']['coefficient']),2)
        self.assertEqual(row['nonzero_license']['method'],'structural_sign')
        r=recipe({'kind':'product','left':taper('1/257'),'right':twist()})
        s=selected(r);p=fixture(s);verify(s,p)
        self.assertEqual(p['reviews'][0]['target_candidates'][1]['energy_rate'],'2/257')

    def test_exact_rounded_log_taper_calibration_at_power_two(self):
        # At n=2,N=2^j, log ratio=1/j; the unrounded alpha=gamma=1
        # coefficient error is exactly -1/j. Dyadic rounding contributes
        # <=2^(-4j), flat against every inverse logarithmic power.
        r=recipe(taper('1'));series=V.coefficient_series(r,2,meter=METER)
        self.assertEqual(series[1],1);self.assertEqual(series[2],{(F(0),F(0)):F(-1)})
        for j in (3,7,31,127):
            D=1<<(4*j);t=F(D//j,D);weight=1-t;error=weight-1
            self.assertLessEqual(abs(error+F(1,j)),F(1,D))
            scaled=(j+1)*error
            self.assertLessEqual(abs(scaled+1),F(1,j)+(j+1)*F(1,D));METER.charge(1000)

    def test_first_order_cancellation_remains_unresolved(self):
        r=recipe(taper(),difference(taper(),unit()),channel='mu',coefficient='1')
        s=selected(r);p=fixture(s);verify(s,p)
        row=p['reviews'][0]['target_candidates'][1]
        self.assertEqual(row['expansion']['status'],'UNRESOLVED')
        self.assertEqual(row['expansion']['cancellation_barrier'],'1/3')
        self.assertIsNone(row['energy_rate'])
        self.assertEqual(p['reviews'][0]['rule_reviews'][0]['forcing_candidates'][1]['status'],'UNRESOLVED')

    def test_uncompiled_barrier_cannot_be_bypassed_by_later_term(self):
        cancel=difference(taper(),taper())
        r=recipe(twist(),cancel);s=selected(r);p=fixture(s);verify(s,p)
        self.assertEqual(p['reviews'][0]['target_candidates'][1]['expansion']['status'],'UNRESOLVED')
        r=recipe(taper('1/6'),cancel);s=selected(r);p=fixture(s);verify(s,p)
        self.assertEqual(p['reviews'][0]['target_candidates'][1]['energy_rate'],'1/3')

    def test_n2_log_dependencies_normalized_before_license(self):
        # At n2, log n/log2=1, so this first-order coefficient cancels.
        envelope={'kind':'log_amplitude','power':'1/3','weight':unit()}
        r=recipe(taper(),envelope,channel='one',coefficient='1');s=selected(r);p=fixture(s);verify(s,p)
        self.assertEqual(p['reviews'][0]['target_candidates'][0]['expansion']['status'],'UNRESOLVED')
        self.assertEqual(p['reviews'][0]['target_candidates'][1]['nonzero_license']['method'],'Arb')

    def test_mixed_sign_nonzero_license_replayed_from_elementary_logs(self):
        r=recipe(unit(),difference(taper('1'),twist()));s=selected(r);p=fixture(s);verify(s,p)
        row=p['reviews'][0]['target_candidates'][1]
        self.assertEqual(row['nonzero_license']['method'],'Arb');self.assertEqual(row['nonzero_license']['sign'],-1)
        bad=deepcopy(p);license=bad['reviews'][0]['target_candidates'][1]['nonzero_license']
        license['enclosure']={'ball':'1','lower_dyadic':['1',0],'upper_dyadic':['1',0]};license['sign']=1
        with self.assertRaises(ValueError):verify(s,bad)

    def test_divisible_forcing_and_parent_sum_are_not_claimed_paid(self):
        r=recipe(taper());s=selected(r);p=fixture(s);verify(s,p)
        rows=p['reviews'][0]['rule_reviews'][0]['forcing_candidates']
        self.assertEqual(rows[0]['status'],'UNRESOLVED')
        self.assertEqual(rows[2]['status'],'UNRESOLVED')
        s=selected(r,[rule(r,b='0')]);p=fixture(s);verify(s,p)
        self.assertEqual(p['reviews'][0]['rule_reviews'][0]['forcing_candidates'][0]['status'],'analytically_refuted')

    def test_altered_expansion_arithmetic_constant_and_rate_rejected(self):
        r=recipe(taper());s=selected(r);p=fixture(s)
        for mutate in ('sign','power','rate','mu','arithmetic','barrier'):
            bad=deepcopy(p);row=bad['reviews'][0]['target_candidates'][1]
            if mutate=='sign':row['expansion']['coefficient'][0]['rational']='1'
            elif mutate=='power':row['expansion']['coefficient'][0]['log_n_power']='2/3'
            elif mutate=='rate':row['energy_rate']='1/3'
            elif mutate=='mu':row['mu']=1
            elif mutate=='arithmetic':row['auxiliary_arithmetic']='1'
            else:row['expansion']['cancellation_barrier']='1'
            with self.assertRaises(ValueError):verify(s,bad)

    def test_changed_recipe_rule_source_and_missing_witness_rejected(self):
        r=recipe(taper());s=selected(r);p=fixture(s)
        for mutate in ('recipe','rule','missing','strongest','step'):
            bad=deepcopy(p)
            if mutate=='recipe':bad['reviews'][0]['recipe']['base']['alpha']='1/2'
            elif mutate=='rule':bad['reviews'][0]['rule_reviews'][0]['rule']['q']=3
            elif mutate=='missing':bad['reviews'][0]['target_candidates'].pop()
            elif mutate=='strongest':bad['reviews'][0]['strongest_target_rate_obstruction']=None
            else:bad['reviews'][0]['rule_reviews'][0]['forcing_candidates'][1]['step_response']='1'
            with self.assertRaises(ValueError):verify(s,bad)

    def test_duplicate_alias_and_scope_claims_rejected(self):
        r=recipe(taper());s=selected(r);p=fixture(s)
        duplicate=deepcopy(s);duplicate['rules'].append(deepcopy(duplicate['rules'][0]))
        with self.assertRaises(ValueError):verify(duplicate,p)
        alias=deepcopy(s);alias['rules'][0]['b']='2/4'
        with self.assertRaises(ValueError):verify(alias,p)
        for key in ('RH_proved','RH_refuted','source_arrays_read','additional_norms_evaluated'):
            bad=deepcopy(p);bad[key]=True
            with self.assertRaises(ValueError):verify(s,bad)

    def test_frontier_license_exact_eta_partitions_and_null_scope(self):
        recipes=[recipe(taper(),id='slow'),recipe(unit(),id='flat')];etas=['1/2','2/3','1']
        p=P.review_frontier(recipes,etas,max_index=6,meter=FIXTURE_METER)
        out=V.verify_frontier(recipes,etas,p,max_index=6,meter=METER)
        self.assertEqual(p['rows'][0]['refuted_etas'],['1'])
        self.assertIsNone(p['rows'][1]['strongest_target_rate_obstruction'])
        self.assertFalse(out['omitted_witness_scan_optimality_verified'])
        self.assertTrue(out['OPEN_means_no_obstruction_supplied_or_licensed_at_this_rate'])
        bad=deepcopy(p);bad['rows'][0]['refuted_etas']=['2/3','1'];bad['rows'][0]['OPEN_etas']=['1/2']
        with self.assertRaises(ValueError):V.verify_frontier(recipes,etas,bad,max_index=6,meter=METER)

    def test_arbitrary_fractional_source_rate_and_frontier_binding(self):
        r=recipe(taper('123/257'));etas=['246/257','1'];p=P.review_frontier([r],etas,max_index=4,meter=FIXTURE_METER)
        V.verify_frontier([r],etas,p,max_index=4,meter=METER)
        self.assertEqual(p['rows'][0]['refuted_etas'],['1'])
        changed=deepcopy(r);changed['base']['gamma']='2'
        with self.assertRaises(ValueError):V.verify_frontier([changed],etas,p,max_index=4,meter=METER)
        with self.assertRaises(ValueError):V.verify_frontier([r],['1','1'],p,max_index=4,meter=METER)

    def test_generic_guards_invalid_powers_and_bool_floats(self):
        for badbase in (taper('2/6'),taper('0'),twist(level=True),{'kind':'assume_RH'}):
            with self.assertRaises(ValueError):V.coefficient_series(recipe(badbase),3,meter=METER)
        for envelope in ({'kind':'moving_band','cutoff_power':'1','weight':unit()},
                         {'kind':'log_amplitude','power':'-1','weight':unit()}):
            with self.assertRaises(ValueError):V.coefficient_series(recipe(unit(),envelope),3,meter=METER)
        r=recipe(taper());s=selected(r);p=fixture(s)
        bad=deepcopy(s);bad['rules'][0]['q']=True
        with self.assertRaises(ValueError):verify(bad,p)
        bad=deepcopy(s);bad['rules'][0]['finite_log_bound']['eta']=.5
        with self.assertRaises(ValueError):verify(bad,p)

    def test_charge_only_external_meter_and_cancelled_not_refuted(self):
        class ChargeOnly:
            def __init__(self):self.operations=0
            def charge(self,n=1):self.operations+=n
        m=ChargeOnly();out=V.coefficient_series(recipe(taper()),3,meter=m)
        self.assertEqual(out[1],F(1,3));self.assertGreater(m.operations,0);METER.charge(m.operations)

def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_floor_residual_rates_044 operations='+str(METER.operations+FIXTURE_METER.operations)+
      ' checker_operations='+str(METER.operations)+' fixture_operations='+str(FIXTURE_METER.operations)+
      ' elapsed_seconds='+str(time.monotonic()-START),flush=True)

if __name__=='__main__':unittest.main()
