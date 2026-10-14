"""Signed synthetic vectors, exact period calibrations and certificate attacks."""
import time
import unittest
from copy import deepcopy
from fractions import Fraction as F
from math import gcd,lcm
from flint import ctx
from prime_bank_candidates import Meter
import check_floor_residual_arguments_044 as V
import floor_residual_interval_044 as P

METER=Meter(cap=100000000,seconds=180)
FIXTURE_METER=P.Meter(cap=100000000,seconds=180)
START=time.monotonic()

def program(C=1,coefficients=(),steps=(),id='synthetic'):
    return {'id':id,'constant':str(C),'coefficients':[{'n':n,'value':str(c)} for n,c in coefficients],
      'steps':[{'q':q,'value':str(c)} for q,c in steps]}

def basis(n,x):
    if not 0<x<=1:return F(0)
    u=1/x;v=1/(n*x)
    return F(u.numerator//u.denominator,n)-v.numerator//v.denominator

def value(p,x):
    if not 0<x<=1:return F(0)
    return F(p['constant'])-sum(F(row['value'])*basis(row['n'],x) for row in p['coefficients'])-sum(
      F(row['value']) for row in p['steps'] if x<=F(1,row['q']))

def cell(p,k):
    return F(p['constant'])-sum(F(row['value'])*(k%row['n'])/row['n'] for row in p['coefficients'])-sum(
      F(row['value']) for row in p['steps'] if k>=row['q'])

def direct_head(p,H):
    METER.charge(80*H*max(1,len(p['coefficients'])+len(p['steps'])))
    return sum((cell(p,k)**2/F(k*(k+1)) for k in range(1,H+1)),F(0))

def fixture(p,H=64):return P.certify(p,H=H,meter=FIXTURE_METER)
def verify(p,c):return V.verify_norm(p,c,meter=METER)
def dyadic(pair):return F(int(pair[0]))*F(2)**pair[1]

class SignedFloorAdmission(unittest.TestCase):
    def test_target_role_requires_original_constant_and_no_steps(self):
        for p in (program(0,[(2,F(1,3))]),program(2,[(2,F(1,3))]),program(1,[],[(2,F(1,3))])):
            with self.assertRaises(ValueError):V.verify_program(p,meter=METER)
            out=V.verify_program(p,target=False,meter=METER)
            self.assertFalse(out['mellin']['target_zero_obstruction_available'])
        out=V.verify_program(program(1,[(2,F(-3,7))]),meter=METER)
        self.assertTrue(out['mellin']['target_zero_obstruction_available']);self.assertFalse(out['RH_proved'])

    def test_zero_auxiliary_and_constant_only_global_norms(self):
        for C in (F(0),F(1),F(-3,7)):
            p=program(C);c=fixture(p,17);out=verify(p,c)
            self.assertLessEqual(F(out['global_fixed_norm_squared_lower']),C*C)
            self.assertGreaterEqual(F(out['global_fixed_norm_squared_upper']),C*C)
            self.assertEqual(out['target_zero_guard_available'],C==1)
            self.assertEqual(F(c['periodic_energy']['V']),C*C)
        out=verify(program(0),fixture(program(0),0))
        self.assertEqual(out['global_fixed_norm_squared_upper'],'0')

    def test_arbitrary_denominator_signed_constant_head_replay(self):
        p=program(F(-19,257),[(2,F(3,7)),(5,F(-1,13))],[(3,F(2,11))],id='pipeline_signed')
        c=fixture(p,128);out=verify(p,c);head=direct_head(p,128)
        self.assertLessEqual(dyadic(c['head']['enclosure']['lower_dyadic']),head)
        self.assertGreaterEqual(dyadic(c['head']['enclosure']['upper_dyadic']),head)
        self.assertTrue(out['display_ball_is_diagnostic_only']);self.assertFalse(out['convergence_proved'])

    def test_signed_auxiliary_difference_and_polarization_cross(self):
        p=program(1,[(2,F(3,7)),(3,F(-2,5))]);q=program(1,[(2,F(1,9)),(5,F(7,11))])
        diff=program(0,[(2,F(3,7)-F(1,9)),(3,F(-2,5)),(5,F(-7,11))])
        sumvec=program(2,[(2,F(3,7)+F(1,9)),(3,F(-2,5)),(5,F(7,11))])
        for k in range(1,31):
            self.assertEqual(cell(diff,k),cell(p,k)-cell(q,k))
            self.assertEqual(cell(sumvec,k)**2-cell(diff,k)**2,4*cell(p,k)*cell(q,k));METER.charge(140)
        self.assertTrue(verify(diff,fixture(diff,50))['verified'])
        with self.assertRaises(ValueError):V.verify_program(diff,meter=METER)

    def test_complete_period_mean_and_signed_gcd_covariance(self):
        for p in (program(F(3,7),[(2,F(3,2)),(3,F(-2,5)),(6,F(7,3))],[(5,F(-3,7))]),
                  program(0,[(2,F(2)),(4,F(-4))])):
            out=V.periodic_energy(p,meter=METER)
            period=lcm(*(row['n'] for row in p['coefficients']))
            shift=max([0]+[row['q'] for row in p['steps']]);start=period*((shift+period)//period)
            samples=[cell(p,k) for k in range(start,start+period)]
            mean=sum(samples,F(0))/period;Vdirect=sum((x*x for x in samples),F(0))/period
            covariance=sum((F(m['value'])*F(n['value'])*F(gcd(m['n'],n['n'])**2-1,12*m['n']*n['n'])
              for m in p['coefficients'] for n in p['coefficients']),F(0))
            self.assertEqual(out['mean'],mean);self.assertEqual(out['V'],Vdirect)
            self.assertEqual(out['variance'],covariance);self.assertEqual(Vdirect,mean*mean+covariance)
            self.assertEqual(out['pair_count'],len(p['coefficients'])**2);METER.charge(period*200+1000)

    def test_zero_signed_divisor_sum_is_retained_before_square(self):
        p=program(0,[(2,F(2)),(4,F(-4))]);c=fixture(p,32);out=verify(p,c)
        rows=c['periodic_energy']['jordan_divisor_sums']
        self.assertEqual(rows[0],{'d':2,'J2':'3','weighted_sum':'0'})
        self.assertEqual(F(c['periodic_energy']['mean']),1)
        self.assertEqual(F(c['periodic_energy']['variance']),1)
        self.assertEqual(F(out['periodic_energy']),2)
        bad=deepcopy(c);bad['periodic_energy']['jordan_divisor_sums'].pop(0)
        with self.assertRaises(ValueError):verify(p,bad)

    def test_jordan_weights_and_sparse_support_calibration(self):
        p=program(F(5,13),[(6,F(11,17)),(10,F(-7,19)),(15,F(2,23))])
        out=V.periodic_energy(p,meter=METER);D=out['D']
        weighted={row['n']:F(row['value'])*D/row['n'] for row in p['coefficients']}
        for row in out['jordan_divisor_sums']:
            d=row['d'];J2=sum(1 for a in range(1,d+1) for b in range(1,d+1) if gcd(gcd(a,b),d)==1)
            self.assertEqual(int(row['J2']),J2)
            self.assertEqual(int(row['weighted_sum']),sum((w for n,w in weighted.items() if n%d==0),F(0)))
            METER.charge(20*d*d)

    def test_dual_large_sieve_block_bound_including_zero_frequency(self):
        p=program(F(7,3),[(2,F(3,2)),(3,F(-7,5)),(4,F(1,7))],[(2,F(2,3))])
        out=V.periodic_energy(p,meter=METER)
        for start in (2,7,37):
            for L in (1,2,5,13,48):
                total=sum((cell(p,k)**2 for k in range(start,start+L)),F(0))
                self.assertLessEqual(total,(L+out['K']**2)*out['V']);METER.charge(100*L)
        const=program(2);self.assertEqual(V.periodic_energy(const,meter=METER)['V'],4)

    def test_exact_safe_tail_factor_and_partial_tail_calibration(self):
        p=program(0,[(2,F(2)),(4,F(-4))]);H=80;c=fixture(p,H);verify(p,c)
        a=H+1;factor=F(1,a)+F(16,a*(a+1));Vperiod=F(c['periodic_energy']['V'])
        self.assertEqual(F(c['imported_large_sieve']['weighted_tail_factor']),factor)
        self.assertEqual(F(c['tail']['large_sieve_upper']),Vperiod*factor)
        self.assertEqual(c['tail']['chosen_provider'],'large_sieve')
        partial=sum((cell(p,k)**2/F(k*(k+1)) for k in range(a,601)),F(0))
        self.assertLessEqual(partial,F(c['tail']['upper']));METER.charge(100000)
        self.assertFalse(c['imported_large_sieve']['minus_one_sharpening_used'])

    def test_step_activation_and_constant_component_tail(self):
        p=program(1,[],[(7,F(1))]);c=fixture(p,7);out=verify(p,c)
        self.assertEqual(c['periodic_energy']['V'],'0');self.assertEqual(c['tail']['upper'],'0')
        self.assertLessEqual(F(out['global_fixed_norm_squared_lower']),F(6,7))
        self.assertGreaterEqual(F(out['global_fixed_norm_squared_upper']),F(6,7))
        bad=deepcopy(c);bad['H']=6
        with self.assertRaises(ValueError):verify(p,bad)

    def test_coefficient_lift_and_full_residual_dilation_are_distinct(self):
        p=program(F(-3,7),[(2,F(3,7)),(5,F(-2,3))],[(3,F(4,9))])
        for q in (2,3,4):
            lifted=V.compile_dilation(p,q,meter=METER);full=V.compile_residual_dilation(p,q,meter=METER)
            self.assertEqual(full['constant'],'0')
            for k in range(1,43):
                x=F(1,k)
                self.assertEqual(value(full,x),value(p,q*x))
                self.assertEqual(value(full,x),value(lifted,x)+F(p['constant'])*(x<=F(1,q)))
                METER.charge(150)

    def test_refinement_complete_forcing_and_signed_cross(self):
        parent=program(1,[(2,F(4,3)),(3,F(-1,7))],id='parent')
        child=program(1,[(2,F(3,5)),(5,F(-2,3))],id='child')
        for b in ('-1','-1/2','0','1/2','1'):
            out=V.verify_family_refinement(parent,child,3,b,meter=METER);h=out['forcing_program']
            self.assertEqual(h['constant'],'1');self.assertEqual(out['endpoint_restatement'],b=='0')
            for k in range(1,33):
                x=F(1,k);hv=value(h,x);old=value(parent,3*x);new=value(child,x)
                self.assertEqual(new,hv+F(b)*old)
                self.assertEqual(new**2,hv**2+F(b)**2*old**2+2*F(b)*hv*old);METER.charge(150)
            self.assertTrue(verify(h,fixture(h,40))['verified'])

    def test_unit_target_guard_and_refinement_cannot_use_auxiliary(self):
        with self.assertRaises(ValueError):V.verify_family_refinement(program(0),program(1),2,'1',meter=METER)
        with self.assertRaises(ValueError):V.verify_family_refinement(program(1),program(1,[],[(2,F(1))]),2,'1',meter=METER)
        out=V.fixed_stencil_guard([2,3],[2],meter=METER)
        self.assertIn('constant-one',out['scope']);self.assertFalse(out['growing_dictionary_refuted'])
        p=program(1,[(2,F(-3,7)),(3,F(2,9))],[(2,F(-1,3))]);one,M,end=out['cells']
        self.assertEqual(cell(p,one)+cell(p,M)-cell(p,end),1)

    def test_missing_mean_cross_jordan_and_spacing_rejected(self):
        p=program(0,[(2,F(2)),(4,F(-4))]);c=fixture(p,32)
        for mutate in ('mean','cross','jordan','spacing','sharpening','provider'):
            bad=deepcopy(c)
            if mutate=='mean':bad['periodic_energy']['mean']='0'
            elif mutate=='cross':bad['periodic_energy']['all_signed_pairs_retained']=False
            elif mutate=='jordan':bad['periodic_energy']['jordan_divisor_sums'][1]['J2']='0'
            elif mutate=='spacing':bad['imported_large_sieve']['frequency_spacing_lower']='1/4'
            elif mutate=='sharpening':bad['imported_large_sieve']['minus_one_sharpening_used']=True
            else:bad['periodic_energy']['provider']='empirical_period_average'
            with self.assertRaises(ValueError):verify(p,bad)

    def test_underpriced_head_tail_whole_and_changed_source_rejected(self):
        p=program(F(-19,257),[(2,F(3,7)),(5,F(-1,13))],[(3,F(2,11))]);c=fixture(p,36)
        for mutate in ('head','tail','whole','constant','unit','step'):
            bad=deepcopy(c)
            if mutate=='head':bad['head']['enclosure']={'ball':'0','lower_dyadic':['0',0],'upper_dyadic':['0',0]}
            elif mutate=='tail':bad['tail']['upper']='0'
            elif mutate=='whole':bad['norm_squared']=deepcopy(c['head']['enclosure'])
            elif mutate=='constant':bad['program']['constant']='1'
            elif mutate=='unit':bad['lattice']['R_zero']='0'
            else:bad['lattice']['step_events']=[]
            with self.assertRaises(ValueError):verify(p,bad)

    def test_interval_display_is_diagnostic_not_the_price(self):
        p=program(F(-3,7),[(2,F(3,7)),(5,F(-1,13))],[(3,F(2,11))]);c=fixture(p,128)
        self.assertTrue(verify(p,c)['verified'])
        with ctx.workprec(300):
            changed=deepcopy(c);bounds=c['head']['enclosure'];mid=(dyadic(bounds['lower_dyadic'])+dyadic(bounds['upper_dyadic']))/2
            from flint import arb
            changed['head']['enclosure']['ball']=(arb(mid.numerator)/mid.denominator).str(80)
        self.assertTrue(verify(p,changed)['verified'])
        changed['norm_squared']['ball']='1000'
        with self.assertRaises(ValueError):verify(p,changed)

    def test_no_finite_norm_can_claim_convergence_or_RH(self):
        p=program(0,[(2,F(1,3))]);c=fixture(p,16)
        for key in ('convergence_as_support_increases_proved','RH_proved','RH_refuted',
                    'source_coefficient_recovery_claimed','general_vector_is_automatically_RH_bearing'):
            bad=deepcopy(c);bad[key]=True
            with self.assertRaises(ValueError):verify(p,bad)
        bad=deepcopy(c);bad['target_role_requires_constant1_and_no_steps']=0
        with self.assertRaises(ValueError):verify(p,bad)

    def test_support_expansion_and_resource_caps_are_explicit(self):
        p=program(0,[(n,F((-1)**n,257)) for n in range(2,2050)])
        self.assertTrue(V.verify_program(p,target=False,meter=METER)['verified'])
        self.assertEqual(len(p['coefficients']),2048)
        p['coefficients'].append({'n':2050,'value':'1'})
        with self.assertRaises(ValueError):V.verify_program(p,target=False,meter=METER)
        with self.assertRaises(ValueError):V.verify_program(program(0,[(4097,F(1))]),target=False,meter=METER)
        p=program(0,[(2,F(1,3))]);c=fixture(p,4);c['H']=V.MAX_H+1
        with self.assertRaises(ValueError):verify(p,c)
        with self.assertRaises(OverflowError):V.periodic_energy(program(0,[(2,F(1,3))]),meter=V.Meter(0))

    def test_logarithmic_forcing_exact_fractional_cost_and_global_leaf(self):
        for q,b,eta in ((2,'1','123/257'),(3,'-1/2','1'),(5,'0','1/5')):
            out=V.verify_log_forcing_gate(q,b,'1/4',eta,meter=METER);t=F(b)**2/q
            self.assertEqual(out['rho'],str(F(0) if not t else (1+t)/2))
            if t:
                y=F(out['young_parameter'])
                self.assertEqual((1+y)*t,F(out['rho']))
                self.assertEqual((1+1/y)*F('1/4'),F(out['forcing_multiplier']))
            self.assertEqual(out['leaf']['status'],'OPEN');self.assertFalse(out['convergence_proved'])
            self.assertEqual(out['endpoint_restatement'],b=='0')
        zero=V.verify_log_forcing_gate(2,'1','0','1',meter=METER)
        self.assertTrue(zero['zero_forcing_excluded_for_linear_support'])
        guard=V.geometric_rate_guard();self.assertTrue(guard['uniform_geometric_contraction_excluded'])
        self.assertFalse(guard['growing_support_convergence_refuted'])

    def test_invalid_provider_rationals_bool_and_step_roles_fail_closed(self):
        for args in ((2,'2','1','1'),(2,'1','-1','1'),(2,'1','1','0'),(2,'1','1','2'),
                     (True,'1','1','1'),(2,.5,'1','1'),(2,'1','1','2/6')):
            with self.assertRaises(ValueError):V.verify_log_forcing_gate(*args,meter=METER)
        with self.assertRaises(ValueError):V.verify_log_forcing_gate(2,'1','1','1/3',provider_status='PROVED',meter=METER)
        for key,value_ in (('constant',0.0),('constant','2/6'),('RH_proved',True)):
            bad=program();bad[key]=value_
            with self.assertRaises(ValueError):V.verify_program(bad,meter=METER)

    def test_external_charge_only_meter_is_sufficient(self):
        class ChargeOnly:
            def __init__(self):self.operations=0
            def charge(self,n=1):self.operations+=n
        m=ChargeOnly();out=V.periodic_energy(program(0,[(2,F(2)),(4,F(-4))]),meter=m)
        self.assertEqual(out['V'],2);self.assertGreater(m.operations,0);METER.charge(m.operations)

def tearDownModule():
    operations=METER.operations+FIXTURE_METER.operations
    print('SYNTHETIC_WORK module=test_check_floor_residual_arguments_044 operations='+str(operations)+
      ' checker_operations='+str(METER.operations)+' fixture_operations='+str(FIXTURE_METER.operations)+
      ' elapsed_seconds='+str(time.monotonic()-START),flush=True)

if __name__=='__main__':unittest.main()
