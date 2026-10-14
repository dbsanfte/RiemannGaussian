"""Independent synthetic floor functions and adversarial proof admissions.

No original arithmetic-source array or increasing-support search is run.
"""
import time
import unittest
from copy import deepcopy
from fractions import Fraction as F
from flint import arb,ctx
from prime_bank_candidates import Meter
import check_floor_residual_arguments_043 as V
import floor_residual_interval_043 as P

METER=Meter(cap=50000000,seconds=180)
FIXTURE_METER=P.Meter(cap=50000000,seconds=180)
START=time.monotonic()

def program(coefficients=(),steps=(),id='synthetic'):
    return {'id':id,'coefficients':[{'n':n,'value':str(c)} for n,c in coefficients],
      'steps':[{'q':q,'value':str(c)} for q,c in steps]}

def floor(v):return v.numerator//v.denominator

def basis(n,x):
    return F(floor(1/x),n)-floor(1/(n*x)) if 0<x<=1 else F(0)

def value(p,x):
    return sum(F(row['value'])*basis(row['n'],x) for row in p['coefficients'])+sum(
      F(row['value']) for row in p['steps'] if 0<x<=F(1,row['q']))

def residual(p,x):return (1-value(p,x)) if 0<x<=1 else F(0)

def exact_head(p,H):
    METER.charge(40*H*max(1,len(p['coefficients'])+len(p['steps'])))
    return sum((residual(p,F(1,k))**2/F(k*(k+1)) for k in range(1,H+1)),F(0))

def dyadic(pair):return F(int(pair[0]))*F(2)**pair[1]

def fixture(p,H=64):return P.certify(p,H=H,meter=FIXTURE_METER)

class FloorProofAdmission(unittest.TestCase):
    def test_typed_target_excludes_indicators_and_keeps_zero_response(self):
        p=program([(2,F(3,7)),(5,F(-1,13))])
        out=V.verify_program(p,meter=METER)
        self.assertTrue(out['mellin']['target_zero_obstruction_available'])
        self.assertEqual(out['mellin']['zero_response'],'1/rho')
        self.assertFalse(out['norm_sequence_convergence_proved']);self.assertFalse(out['RH_proved'])
        forcing=program([(2,F(3,7))],[(3,F(2,11))])
        with self.assertRaises(ValueError):V.verify_program(forcing,meter=METER)
        out=V.verify_program(forcing,target=False,meter=METER)
        self.assertFalse(out['mellin']['target_zero_obstruction_available'])

    def test_floor_cells_jumps_and_zero_extension(self):
        for n in (2,3,7,13):
            for k in range(1,31):
                for x in (F(1,k),(F(1,k)+F(1,k+1))/2):
                    self.assertEqual(basis(n,x),F(k%n,n));METER.charge(20)
            self.assertEqual(basis(n,F(7,4)),0)

    def test_mellin_formula_at_initial_absolute_domain(self):
        with ctx.workprec(256):
            for n in (2,5):
                for s in (2,3):
                    H=80
                    head=sum((F(k%n,n)*(F(1,k**s)-F(1,(k+1)**s))/s for k in range(1,H+1)),F(0))
                    tail=F(n-1,n*s*(H+1)**s)
                    exact=(arb(1)/n-arb(n)**(-s))*arb(s).zeta()/s
                    self.assertGreaterEqual(V._arb_endpoint(exact.lower()),head)
                    self.assertLessEqual(V._arb_endpoint(exact.upper()),head+tail)
                    METER.charge(H*40)

    def test_dilation_identity_including_indicator_and_composite_q(self):
        p=program([(2,F(3,7)),(5,F(-2,3))],[(3,F(4,9))])
        for q in (2,3,4):
            lift=V.compile_dilation(p,q,meter=METER)
            for k in range(1,53):
                for x in (F(1,k),(F(1,k)+F(1,k+1))/2,F(5,4)):
                    self.assertEqual(value(lift,x),value(p,q*x));METER.charge(80)

    def test_dilation_whole_cell_measure_scaling(self):
        p=program([(2,F(7,5)),(3,F(-2,7))])
        for q in (2,3,5):
            L=13;H=q*(L+1)-1
            result=sum((residual(p,F(q,k))**2/F(k*(k+1)) for k in range(1,H+1)),F(0))
            self.assertEqual(result,exact_head(p,L)/q);METER.charge(H*80)

    def test_refinement_full_signed_pointwise_and_cross_identity(self):
        parent=program([(2,F(4,3)),(3,F(-1,7))],id='parent')
        child=program([(2,F(3,5)),(5,F(-2,3))],id='child')
        for b in ('-1','-1/2','0','1/2','1'):
            result=V.verify_family_refinement(parent,child,3,b,meter=METER);h=result['forcing_program']
            self.assertEqual(result['endpoint_restatement'],b=='0')
            for k in range(1,45):
                x=F(1,k);e=residual(parent,3*x);hv=residual(h,x);c=residual(child,x)
                self.assertEqual(c,hv+F(b)*e)
                self.assertEqual(c*c,hv*hv+F(b)**2*e*e+2*F(b)*hv*e);METER.charge(100)
            self.assertEqual(h['steps'],[] if b=='0' else [{'q':3,'value':b}])

    def test_fixed_stencil_gap_is_actual_function_identity(self):
        p=program([(2,F(12,7)),(3,F(-8,5)),(7,F(1,9))],[(2,F(3,2)),(5,F(-2,7))])
        out=V.fixed_stencil_guard([2,3,7],[2,5],meter=METER)
        one,M,last=out['cells'];values=[residual(p,F(1,k)) for k in (one,M,last)]
        self.assertEqual(values[0]+values[1]-values[2],1)
        cells=sum((v*v/F(k*(k+1)) for k,v in zip((one,M,last),values)),F(0))
        self.assertGreaterEqual(cells,F(out['forcing_norm_squared_lower']))
        self.assertFalse(out['growing_dictionary_refuted']);self.assertFalse(out['RH_refuted'])
        METER.charge(2000)

    def test_empty_and_growing_stencil_scope(self):
        empty=V.fixed_stencil_guard([],[],meter=METER)
        self.assertEqual(empty['cells'],[1,2,3])
        a=V.fixed_stencil_guard([2],[2],meter=METER)
        b=V.fixed_stencil_guard([2,3,5],[2],meter=METER)
        self.assertLess(F(b['forcing_norm_squared_lower']),F(a['forcing_norm_squared_lower']))
        self.assertFalse(b['growing_dictionary_refuted'])

    def test_independent_heap_head_vs_direct_rational_cells(self):
        for p,H in ((program(),0),(program([(2,F(3,2)),(3,F(-2,5)),(6,F(7,3))],[(2,F(1,2)),(5,F(-3,7))]),79)):
            c=fixture(p,H);out=V.verify_norm(p,c,meter=METER)
            head=exact_head(p,H)
            self.assertLessEqual(dyadic(c['head']['enclosure']['lower_dyadic']),head)
            self.assertGreaterEqual(dyadic(c['head']['enclosure']['upper_dyadic']),head)
            self.assertGreaterEqual(F(out['global_fixed_norm_squared_upper']),head+F(out['tail_upper']))
            self.assertTrue(out['all_domain_included']);self.assertFalse(out['convergence_proved'])

    def test_pipeline_display_rounding_regression(self):
        p=program([(2,F(3,7)),(5,F(-1,13))],[(3,F(2,11))],id='pipeline_toy')
        c=fixture(p,128);out=V.verify_norm(p,c,meter=METER)
        self.assertTrue(out['verified']);self.assertTrue(out['display_ball_is_diagnostic_only'])
        # A zero-radius diagnostic overlapping its wider exact interval is
        # permitted. It never replaces the exact interval used in admission.
        changed=deepcopy(c)
        with ctx.workprec(300):
            bounds=c['head']['enclosure'];mid=(dyadic(bounds['lower_dyadic'])+dyadic(bounds['upper_dyadic']))/2
            diagnostic=arb(mid.numerator)/mid.denominator
            changed['head']['enclosure']['ball']=diagnostic.str(80)
        self.assertTrue(V.verify_norm(p,changed,meter=METER)['verified'])

    def test_underpriced_head_tail_and_distant_display_rejected(self):
        p=program([(2,F(3,7)),(5,F(-1,13))],[(3,F(2,11))]);c=fixture(p,36)
        for mutate in ('head','tail','whole','display'):
            bad=deepcopy(c)
            if mutate=='head':bad['head']['enclosure']={'ball':'0','lower_dyadic':['0',0],'upper_dyadic':['0',0]}
            elif mutate=='tail':bad['tail']['upper']='0'
            elif mutate=='whole':bad['norm_squared']=deepcopy(c['head']['enclosure'])
            else:bad['norm_squared']['ball']='100'
            with self.assertRaises(ValueError):V.verify_norm(p,bad,meter=METER)

    def test_forged_lattice_scope_and_flags_rejected(self):
        p=program([(2,F(3,7))],[(3,F(2,11))]);c=fixture(p,12)
        for mutate in ('event','step','unit','domain','claim','bool'):
            bad=deepcopy(c)
            if mutate=='event':bad['lattice']['events'][0]['value']='1'
            elif mutate=='step':bad['lattice']['step_events']=[]
            elif mutate=='unit':bad['lattice']['R_zero']='0'
            elif mutate=='domain':bad['continuous_integral_domain']='x>=1/12'
            elif mutate=='claim':bad['convergence_as_support_increases_proved']=True
            else:bad['RH_proved']=0
            with self.assertRaises(ValueError):V.verify_norm(p,bad,meter=METER)

    def test_step_tail_cannot_start_before_activation(self):
        p=program([(2,F(1,3))],[(13,F(5,7))]);c=fixture(p,20);c['H']=12
        with self.assertRaises(ValueError):V.verify_norm(p,c,meter=METER)

    def test_relative_young_price_and_exact_boundary(self):
        result=V.verify_relative_forcing_gate(4,'1','1/16',meter=METER)
        self.assertTrue(result['admissible']);t=F(result['t']);y=F(result['young_parameter'])
        rho=(1+y)*t+(1+1/y)*F('1/16')
        self.assertEqual(rho,F(result['contraction_energy_coefficient']));self.assertLess(rho,1)
        boundary=V.verify_relative_forcing_gate(4,'1','1/4',meter=METER)
        self.assertFalse(boundary['admissible']);self.assertEqual(boundary['strict_margin'],'0')

    def test_geometric_gates_excluded_by_imported_support_lower_bound(self):
        a=V.verify_relative_forcing_gate(3,'1','1/64',meter=METER)
        b=V.verify_absolute_forcing_gate(4,'1','1','3','1/2',meter=METER)
        for result in (a,b):
            self.assertTrue(result['uniform_geometric_gate_excluded_for_linear_support'])
            self.assertIn('maxsupport<=N',result['imported_lower_bound']['domain'])
            self.assertEqual(result['imported_lower_bound']['source'],V.BURNOL_SOURCE)
            self.assertFalse(result['imported_lower_bound']['growing_support_convergence_refuted'])
            self.assertFalse(result['RH_proved']);self.assertFalse(result['convergence_proved'])
        self.assertTrue(b['equal_ratio_resonance_retained'])

    def test_log_forcing_arbitrary_fraction_and_exact_young_cost(self):
        for q,b,eta in ((2,'1','123/257'),(3,'-1/2','1'),(5,'0','1/5')):
            result=V.verify_log_forcing_gate(q,b,'1/4',eta,meter=METER)
            t=F(b)**2/q
            self.assertEqual(result['rho'],str(F(0) if not t else (1+t)/2))
            if t:
                y=F(result['young_parameter'])
                self.assertEqual((1+y)*t,F(result['rho']))
                self.assertEqual((1+1/y)*F('1/4'),F(result['forcing_multiplier']))
            else:self.assertEqual(result['forcing_multiplier'],'1/4')
            self.assertTrue(result['conditional_tends_to_zero']);self.assertFalse(result['convergence_proved'])
            self.assertEqual(result['leaf']['status'],'OPEN')
            self.assertIn('N.bit_length()',result['leaf']['L'])

    def test_log_chain_scale_and_convolution_including_b_zero(self):
        for q in (2,3,7):
            for N0 in (1,3,17):
                for i in range(17):self.assertGreaterEqual((N0*q**i).bit_length(),1+i)
        result=V.verify_log_forcing_gate(2,'1','1','1',meter=METER)
        rho=F(result['rho']);B=F(result['forcing_multiplier']);E=F(2)
        for j in range(1,18):
            E=rho*E+B/j
            expected=rho**j*2+B*sum((rho**(j-1-i)/F(1+i) for i in range(j)),F(0))
            self.assertEqual(E,expected);METER.charge(500)
        result=V.verify_log_forcing_gate(2,'0','1','1',meter=METER)
        self.assertTrue(result['endpoint_restatement']);self.assertEqual(result['rho'],'0')

    def test_global_leaf_cannot_be_finite_or_declared_proved(self):
        for call in (lambda:V.verify_relative_forcing_gate(2,'1/2','1/4',provider_status='PROVED',meter=METER),
                     lambda:V.verify_absolute_forcing_gate(2,'1/2','1','1','1/2',provider_status='FINITE',meter=METER),
                     lambda:V.verify_vanishing_forcing_gate(2,'1/2',provider_status=True,meter=METER),
                     lambda:V.verify_log_forcing_gate(2,'1/2','1','1/3',provider_status='PROVED',meter=METER)):
            with self.assertRaises(ValueError):call()

    def test_invalid_log_gate_and_rational_types_fail_closed(self):
        for args in ((2,'2','1','1'),(2,'1','-1','1'),(2,'1','1','0'),(2,'1','1','2'),
                     (True,'1','1','1'),(2,0.5,'1','1'),(2,'1','1','2/6')):
            with self.assertRaises(ValueError):V.verify_log_forcing_gate(*args,meter=METER)
        bad=program([(2,F(1,3))]);bad['coefficients'][0]['n']=True
        with self.assertRaises(ValueError):V.verify_program(bad,meter=METER)
        bad=program([(2,F(1,3))]);bad['coefficients'][0]['value']='2/6'
        with self.assertRaises(ValueError):V.verify_program(bad,meter=METER)

    def test_charge_only_external_meter_and_unknown_schema(self):
        class ChargeOnly:
            def __init__(self):self.operations=0
            def charge(self,n=1):self.operations+=n
        m=ChargeOnly();out=V.verify_log_forcing_gate(2,'1','1','1/257',meter=m)
        self.assertTrue(out['verified']);self.assertGreater(m.operations,0);METER.charge(m.operations)
        p=program([(2,F(1,3))]);p['RH_proved']=True
        with self.assertRaises(ValueError):V.verify_program(p,meter=METER)

def tearDownModule():
    operations=METER.operations+FIXTURE_METER.operations
    print('SYNTHETIC_WORK module=test_check_floor_residual_arguments_043 operations='+str(operations)+
      ' checker_operations='+str(METER.operations)+' fixture_operations='+str(FIXTURE_METER.operations)+
      ' elapsed_seconds='+str(time.monotonic()-START),flush=True)

if __name__=='__main__':unittest.main()
