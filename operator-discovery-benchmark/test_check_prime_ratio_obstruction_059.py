"""Source-free exact cells and adversarial policy-obstruction admission."""
import copy
import unittest
from fractions import Fraction as Q
import check_prime_ratio_obstruction_059 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]
def meter():
    m=C.Meter();METERS.append(m);return m

def fixture(profile='Q'):
    ps,q,lo,hi,sigma=([2,5],5,'25/4','13/2',-1)
    if profile=='P':lo,hi,sigma='29/2','15',1
    if profile=='S':lo,hi,sigma='17/2','35/4',1
    if profile=='D':ps,q,lo,hi,sigma=[2,7],7,'35/4','9',1
    return {'schema':'prime-ratio-cost-obstruction-v1',
        'parameters':{'alpha':'1/2','gamma':'1/3','tau':'1/2','primes':ps,'p':2,'q':q},
        'policy':{'steps':[{'kind':'prime_ratio','group':'profile','order':'asc'}]},
        'prime':3,'cell':{'lower':lo,'upper':hi},'profile':profile,
        'kernel_sign':sigma,'log_power':'7/2' if profile=='D' else '5/2'}

class RatioObstructionCheckerTests(unittest.TestCase):
    def test_all_four_exact_profile_gates(self):
        m=meter()
        for p in ('P','Q','D','S'):
            cert=fixture(p);out=C.verify(cert,m)
            self.assertIs(out['verified'],True)
            self.assertEqual(out['profile'],p)
            self.assertEqual(out['lower_bound']['log_power'],cert['log_power'])

    def test_open_integer_endpoints_are_allowed(self):
        m=meter();row=C._floor_cell(Q(1),Q(5,4),1,m)
        self.assertEqual(row['floors'],[1,2,4])
        out=C.verify(fixture('P'),m)
        self.assertEqual(out['floor_cells'][2]['floors'],[2,4,9])

    def test_midpoint_cannot_hide_component_floor_changes(self):
        m=meter()
        with self.assertRaises(ValueError):C._floor_cell(Q(1),Q(3,2),1,m)
        bad=fixture();bad['cell']['upper']='27/4'
        with self.assertRaises(ValueError):C.verify(bad,m)

    def test_bad_profile_or_sign_and_different_endpoints(self):
        m=meter()
        for key,value in (('profile','P'),('kernel_sign',1),('kernel_sign',True)):
            bad=fixture();bad[key]=value
            with self.assertRaises(ValueError):C.verify(bad,m)
        bad=fixture();bad['cell']={'lower':'1/2','upper':'1'}
        with self.assertRaises(ValueError):C.verify(bad,m)

    def test_smallest_outside_prime_is_mandatory(self):
        m=meter()
        for r in (2,5,7,9,True):
            bad=fixture();bad['prime']=r
            with self.assertRaises(ValueError):C.verify(bad,m)

    def test_complete_prime_mask_and_ordered_source_scales(self):
        m=meter()
        for key,value in (('primes',[2,2,5]),('primes',[5,2]),('primes',[2,9]),
                ('primes',[2]),('p',5),('q',3),('p',True)):
            bad=fixture();bad['parameters'][key]=value
            with self.assertRaises(ValueError):C.verify(bad,m)

    def test_general_rational_band_and_order_exponent(self):
        m=meter();cert=fixture();cert['parameters'].update(alpha='1/257',gamma='257/1026',tau='3/7')
        cert['log_power']=str(3-Q(1,257))
        out=C.verify(cert,m)
        self.assertEqual(out['kernel_lower']['log_power'],'770/257')
        bad=copy.deepcopy(cert);bad['log_power']='5/2'
        with self.assertRaises(ValueError):C.verify(bad,m)

    def test_boundary_band_parameters_rejected(self):
        m=meter()
        for key,values in (('alpha',('0','1','-1/3')),('gamma',('0','-1/5')),('tau',('0','1','2'))):
            for value in values:
                bad=fixture();bad['parameters'][key]=value
                with self.assertRaises(ValueError):C.verify(bad,m)

    def test_alias_float_bool_and_large_rationals_rejected(self):
        m=meter()
        for value in ('2/4',0.5,True,'0.5',str(1<<4097)):
            bad=fixture();bad['parameters']['alpha']=value
            with self.assertRaises(ValueError):C.verify(bad,m)

    def test_both_first_pass_groups_and_canonical_residual(self):
        m=meter()
        for first in ('all','profile'):
            for later in (None,'all','profile'):
                cert=fixture();cert['policy']['steps'][0]['group']=first
                if later:cert['policy']['steps'].append({'kind':'scan','group':later,'order':'asc','method':'stack'})
                self.assertTrue(C.verify(cert,m)['first_pass']['later_residual_scan_cannot_undo_cost'])

    def test_prior_scan_descending_and_unsupported_rescue_rejected(self):
        m=meter()
        invalid=[[],[{'kind':'scan','group':'all','order':'asc','method':'stack'}],
            [{'kind':'prime_ratio','group':'all','order':'desc'}],
            [{'kind':'prime_ratio','group':'sector','order':'asc'}],
            [{'kind':'prime_ratio','group':'all','order':'asc'},{'kind':'scan','group':'all','order':'asc','method':'fifo'}],
            [{'kind':'prime_ratio','group':'all','order':'asc'},{'kind':'prime_ratio','group':'all','order':'asc'}]]
        for steps in invalid:
            bad=fixture();bad['policy']['steps']=steps
            with self.assertRaises(ValueError):C.verify(bad,m)

    def test_schema_rejects_forged_proof_or_source_flags(self):
        m=meter()
        for where,key,value in (('', 'actual_arithmetic_refuted',True),('parameters','source_verified',True),
                ('cell','midpoint_only',True),('policy','undo_prior_costs',True)):
            bad=fixture();obj=bad if not where else bad[where];obj[key]=value
            with self.assertRaises(ValueError):C.verify(bad,m)
        bad=fixture();del bad['cell']['lower']
        with self.assertRaises(ValueError):C.verify(bad,m)

    def test_density_preserves_whole_fixed_interval_and_modulus(self):
        m=meter();out=C.verify(fixture(),m)
        self.assertEqual(out['density']['coprime_squarefree_modulus'],30)
        self.assertEqual(out['density']['density_lower'],'1/15')
        self.assertEqual(out['density']['reciprocal_cell_width'],'2/325')
        self.assertFalse(out['density']['finite_threshold_claimed'])

    def test_cost_exclusion_is_not_arithmetic_or_rh_refutation(self):
        m=meter();out=C.verify(fixture(),m)
        self.assertTrue(out['growth_exclusion']['proved'])
        for field in ('actual_arithmetic_refuted','RH_refuted','RH_proved',
                'uniform_signed_target_bound_proved','finite_counterexample_claimed','fresh_source_arrays_or_integrals_evaluated'):
            self.assertIs(out[field],False)
        self.assertFalse(out['lower_bound']['numerical_lower_constant_claimed'])
        self.assertEqual(out['lower_bound']['domain'],'every sufficiently large integer N')

    def test_charge_only_pipeline_meter(self):
        m=PipelineMeter();METERS.append(m)
        self.assertTrue(C.verify(fixture(),m)['verified'])
        self.assertGreater(m.operations,100)

    def test_capacity_rejection_and_meter_cap(self):
        m=meter();bad=fixture();bad['prime']=1_000_001
        with self.assertRaises(ValueError):C.verify(bad,m)
        tiny=C.Meter(cap=1);METERS.append(tiny)
        with self.assertRaises(OverflowError):C.verify(fixture(),tiny)
        bad=fixture();bad['cell']={'lower':'0','upper':'1'}
        with self.assertRaises(ValueError):C.verify(bad,m)

if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_prime_ratio_obstruction_059 operations='+str(sum(m.operations for m in METERS)))
