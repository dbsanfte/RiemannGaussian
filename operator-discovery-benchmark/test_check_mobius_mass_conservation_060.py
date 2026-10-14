"""Independent060 synthetic identities, source units and cost-scope mutations."""
import copy
import unittest
from fractions import Fraction as Q
from math import gcd
import check_mobius_mass_conservation_060 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]
def meter():
    m=C.Meter(cap=1_000_000_000);METERS.append(m);return m

def identity(A=2,B=-1):
    # Tiny different prime mask, ordinary W expressions only. No nullspace miner.
    rows={}
    for p,s in ((3,A),(7,B)):
        for d,c in ((p,s),(2*p,-3*s),(4*p,2*s)):
            rows[d]=rows.get(d,0)+c
    return {'schema':'mobius-profile-floor-identity-v1',
        'parameters':{'alpha':'1/2','gamma':'1/3','tau':'1/2','primes':[3,7],'p':3,'q':7},
        'period':84,'profile_coefficients':[str(x) for x in (A,-B,A+B,A-B)],
        'floor_coefficients':[{'d':d,'c':str(c)} for d,c in sorted(rows.items()) if c]}

def copy_certificate():
    cert=identity();mass=sum(abs(Q(r['c'])) for r in cert['floor_coefficients'])
    mag=Q(6*21)/(2-Q(cert['parameters']['alpha']))
    weights=[int(x) for x in cert['profile_coefficients']]
    return {'schema':'mobius-copy-leftover-bound-v1','identity':cert,'weights':weights,
        'magnitude_constant':str(mag),'coefficient':str(mag*mass/min(weights)),'log_degree':2}

def ordinary_mu(n,m):
    sign=1;d=2
    while d*d<=n:
        m.charge(4)
        if n%d==0:
            n//=d;sign=-sign
            if n%d==0:return 0
        d+=1
    return -sign if n>1 else sign

def smooth_count(x,ps,m):
    count=0
    for n in range(1,x.numerator//x.denominator+1):
        remainder=n
        for p in ps:
            while remainder%p==0:remainder//=p;m.charge(4)
        m.charge(4)
        count+=remainder==1
    return count

class MassCheckerTests(unittest.TestCase):
    def test_complete_period_identity(self):
        m=meter();out=C.verify_identity(identity(),m)
        self.assertTrue(out['floor_identity_proved'])
        self.assertEqual(out['all_period_jumps_checked'],84)
        self.assertTrue(out['zero_period_drift_checked']);self.assertTrue(out['zero_head_checked'])

    def test_continuous_cells_endpoints_and_multiple_periods(self):
        m=meter();cert=identity();xs=list(map(Q,cert['profile_coefficients']))
        floor=lambda x:x.numerator//x.denominator
        for n in range(-84,169):
            for v in (Q(n,4),Q(3*n+1,12)):
                # Direct real floor formula; not the checker's grid jump implementation.
                a=floor(4*v/3)-3*floor(2*v/3)+2*floor(v/3)
                b=floor(4*v/7)-3*floor(2*v/7)+2*floor(v/7)
                row=[0]*4
                if a or b:
                    i=0 if not b else 1 if not a else 2 if a==b else 3
                    row[i]=a if a else -b
                left=sum(x*f for x,f in zip(xs,row))
                right=sum(Q(r['c'])*floor(4*v/r['d']) for r in cert['floor_coefficients'])
                self.assertEqual(left,right);m.charge(200)

    def test_ordinary_mu_to_smooth_all_units_and_exits(self):
        m=meter();cert=identity();xs=list(map(Q,cert['profile_coefficients']));ps=[3,7]
        for N in range(2,20):
            total=Q(0)
            for d in range(1,4*N+1):
                if gcd(d,21)!=1:continue
                mu=ordinary_mu(d,m)
                v=Q(N,d);a=int(4*v/3)-3*int(2*v/3)+2*int(v/3)
                b=int(4*v/7)-3*int(2*v/7)+2*int(v/7)
                row=[0]*4
                if a or b:
                    i=0 if not b else 1 if not a else 2 if a==b else 3;row[i]=a if a else -b
                total+=mu*sum(x*f for x,f in zip(xs,row));m.charge(100)
            smooth=sum(Q(r['c'])*smooth_count(Q(4*N,r['d']),ps,m) for r in cert['floor_coefficients'])
            self.assertEqual(total,smooth)
        out=C.verify_identity(cert,m)['global_signed_mass_identity']
        self.assertTrue(out['d1_retained']);self.assertTrue(out['q_range_exits_retained'])
        self.assertEqual(out['zero_extension_horizon'],'4N')

    def test_missing_floor_row_or_altered_profile_coefficient(self):
        m=meter()
        for kind in ('drop','sign','profile'):
            bad=identity()
            if kind=='drop':bad['floor_coefficients'].pop()
            elif kind=='sign':bad['floor_coefficients'][0]['c']='-2'
            else:bad['profile_coefficients'][3]='2'
            with self.assertRaises(ValueError):C.verify_identity(bad,m)

    def test_divisor_rows_canonical_nonzero_unique(self):
        m=meter()
        for change in ('zero','alias','duplicate','nondivisor','order','bool'):
            bad=identity()
            if change=='zero':bad['floor_coefficients'][0]['c']='0'
            elif change=='alias':bad['floor_coefficients'][0]['c']='4/2'
            elif change=='duplicate':bad['floor_coefficients'].insert(0,copy.deepcopy(bad['floor_coefficients'][0]))
            elif change=='nondivisor':bad['floor_coefficients'][0]['d']=5
            elif change=='order':bad['floor_coefficients'].reverse()
            else:bad['floor_coefficients'][0]['d']=True
            with self.assertRaises(ValueError):C.verify_identity(bad,m)

    def test_period_cannot_be_truncated_or_swapped(self):
        m=meter()
        for value in (21,83,85,True):
            bad=identity();bad['period']=value
            with self.assertRaises(ValueError):C.verify_identity(bad,m)

    def test_general_rational_identity_and_zero_identity(self):
        m=meter();cert=identity(Q(1,257),Q(-3,11))
        cert['parameters'].update(alpha='1/257',gamma='257/1026',tau='3/7')
        self.assertTrue(C.verify_identity(cert,m)['verified'])
        zero=identity(0,0);out=C.verify_identity(zero,m)
        self.assertEqual(out['signed_mass_upper']['coefficient'],'0')
        self.assertFalse(out['whole_signed_target_bound_proved'])

    def test_prime_mask_and_band_gates(self):
        m=meter()
        for key,value in (('primes',[7,3]),('primes',[3,3,7]),('primes',[3,9]),
            ('q',5),('p',7),('p',True),('alpha','1'),('gamma','0'),('tau','0')):
            bad=identity();bad['parameters'][key]=value
            with self.assertRaises(ValueError):C.verify_identity(bad,m)

    def test_positive_copy_bound_exact_price(self):
        m=meter();cert=copy_certificate();out=C.verify_copy_bound(cert,m)
        self.assertEqual(out['magnitude_constant'],'84')
        self.assertEqual(out['coefficient'],'1512')
        self.assertTrue(out['leftover_cost_bound_proved']);self.assertEqual(out['paired_cost_status'],'OPEN')

    def test_equal_copies_conserve_signed_weighted_count(self):
        m=meter();cert=copy_certificate();weights=cert['weights']
        # Finite abstract source magnitudes: arbitrary legal initial pairings.
        tokens=[(0,1,Q(2)),(1,-1,Q(3)),(2,1,Q(1)),(3,-1,Q(4))]
        copies=[(sign,mag/weights[i]) for i,sign,mag in tokens for _ in range(weights[i])]
        signed=sum(sign for sign,mag in copies)
        plus=[mag for sign,mag in copies if sign>0];minus=[mag for sign,mag in copies if sign<0]
        count=min(len(plus),len(minus));plus=plus[count:];minus=minus[count:]
        self.assertEqual(len(plus)+len(minus),abs(signed))
        self.assertLessEqual(sum(plus+minus),max(mag for sign,mag in copies)*abs(signed));m.charge(500)

    def test_bad_weights_unit_copy_or_profile_swap(self):
        m=meter()
        for weights in ([0,1,1,3],[2,-1,1,3],[2,1,1,17],[2,1,3,1],[2,1,1],[True,1,1,3]):
            bad=copy_certificate();bad['weights']=weights
            with self.assertRaises(ValueError):C.verify_copy_bound(bad,m)

    def test_underpriced_constant_or_log_degree(self):
        m=meter()
        for key,value in (('magnitude_constant','83'),('coefficient','1511'),('log_degree',1),('log_degree',True)):
            bad=copy_certificate();bad[key]=value
            with self.assertRaises(ValueError):C.verify_copy_bound(bad,m)

    def test_copy_weight_must_bind_identity(self):
        m=meter();bad=copy_certificate();bad['identity']=identity(3,-1)
        with self.assertRaises(ValueError):C.verify_copy_bound(bad,m)
        bad=copy_certificate();bad['identity']['floor_coefficients'].pop()
        with self.assertRaises(ValueError):C.verify_copy_bound(bad,m)

    def test_completeness_requirement_and_rh_scope(self):
        m=meter();out=C.verify_copy_bound(copy_certificate(),m)
        self.assertIn('COMPLETE global',out['pairing_requirements'])
        self.assertFalse(out['whole_signed_target_bound_proved']);self.assertFalse(out['RH_proved'])
        self.assertFalse(out['source_arrays_evaluated'])

    def test_extra_proof_flags_and_float_inputs_rejected(self):
        m=meter()
        bad=identity();bad['RH_proved']=True
        with self.assertRaises(ValueError):C.verify_identity(bad,m)
        bad=copy_certificate();bad['paired_cost_bound_proved']=True
        with self.assertRaises(ValueError):C.verify_copy_bound(bad,m)
        bad=identity();bad['profile_coefficients'][0]=2.0
        with self.assertRaises(ValueError):C.verify_identity(bad,m)

    def test_charge_only_pipeline_meter(self):
        m=PipelineMeter();METERS.append(m)
        self.assertTrue(C.verify_copy_bound(copy_certificate(),m)['verified'])
        self.assertGreater(m.operations,100)

    def test_prospective_period_and_bit_caps(self):
        m=meter();bad=identity();bad['parameters'].update(primes=[37,41],p=37,q=41)
        with self.assertRaises(OverflowError):C.verify_identity(bad,m)
        bad=identity();bad['profile_coefficients'][0]=str(1<<4097)
        with self.assertRaises(ValueError):C.verify_identity(bad,m)
        tiny=C.Meter(cap=1);METERS.append(tiny)
        with self.assertRaises(OverflowError):C.verify_identity(identity(),tiny)

if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_mobius_mass_conservation_060 operations='+str(sum(m.operations for m in METERS)))
