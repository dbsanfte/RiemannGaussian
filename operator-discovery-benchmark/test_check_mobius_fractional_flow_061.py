"""Source-free061 column, finite transport, head and scope admission tests."""
import copy
import unittest
from fractions import Fraction as Q
from itertools import product
import check_mobius_fractional_flow_061 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]
def meter():
    m=C.Meter(cap=1_000_000_000);METERS.append(m);return m

def fixture(alpha='1/2',theta='1/2'):
    parameters={'alpha':alpha,'gamma':'1/3','tau':'1/2','primes':[2,7],'p':2,'q':7}
    columns=[]
    for base,sign,xs in ((2,1,['1','0','1','1']),(7,-1,['0','1','-1','1'])):
        identity={'schema':'mobius-profile-floor-identity-v1','parameters':copy.deepcopy(parameters),'period':56,
            'profile_coefficients':xs,'floor_coefficients':[{'d':base*j,'c':str(sign*c)} for j,c in ((1,1),(2,-3),(4,2))]}
        columns.append({'base':base,'identity':identity})
    return {'schema':'mobius-fractional-flow-v1','parameters':parameters,
        'kernels':{'P':[[2,'1']],'Q':[[7,'1']],'D':[[2,'1'],[7,'-1']],'S':[[2,'1'],[7,'1']]},
        'columns':columns,'positive_prefixes':{'P':['1'],'Q':['1'],'D':['1','0'],'S':['1','2']},
        'carrier':'d^(-t)','endpoint_coefficient':str(Q(3*14*12)/(2-Q(alpha))),
        'log_degree':2,'head_theta':theta,'head_coefficient':str(Q(6*14)/(3-Q(alpha))),
        'exit_rho':'3/4','exit_coefficient':str(Q(6*2*14)/(3-Q(alpha))),
        'horizon':'max(1,floor(4*N/p))'}

def independent_transport(xs,bs,m):
    # Quantile coupling of positive and negative measures, including dummy0.
    positive=[];negative=[]
    for x,b in list(zip(xs,bs))+[(Q(0),-sum(bs))]:
        if b>0:positive.append([x,b])
        if b<0:negative.append([x,-b])
    cost=Q(0);i=j=0
    while i<len(positive) and j<len(negative):
        amount=min(positive[i][1],negative[j][1]);cost+=amount*abs(positive[i][0]-negative[j][0])
        positive[i][1]-=amount;negative[j][1]-=amount
        i+=positive[i][1]==0;j+=negative[j][1]==0;m.charge(100)
    if i!=len(positive) or j!=len(negative):raise ArithmeticError('transport balance')
    return cost

class FractionalFlowTests(unittest.TestCase):
    def test_complete_shared_carrier_column_proof(self):
        m=meter();out=C.verify_fractional_flow(fixture(),m)
        self.assertTrue(out['verified']);self.assertTrue(out['kernel_positivity_proved'])
        self.assertEqual(out['floor_coefficient_l1'],'12');self.assertEqual(out['terminal_bound']['coefficient'],'336')
        self.assertEqual(out['column_proofs'],[{'base':2,'verified':True,'floor_l1':'6'},{'base':7,'verified':True,'floor_l1':'6'}])

    def test_every_small_signed_measure_matches_quantile_transport(self):
        m=meter();xs=[Q(1),Q(3,5),Q(1,7)]
        for bs in product(range(-2,3),repeat=3):
            bs=list(map(Q,bs));row=C._flow_variation(xs,bs,m)
            self.assertEqual(row['cost'],independent_transport(xs,bs,m))
            self.assertLessEqual(abs(row['signed']),row['cost'])

    def test_empty_measure_and_nonzero_total_dummy(self):
        m=meter();self.assertEqual(C._flow_variation([],[],m),{'cost':Q(0),'signed':Q(0),'terminal':Q(0)})
        xs=[Q(1),Q(1,2)];bs=[Q(2),Q(-1)];row=C._flow_variation(xs,bs,m)
        self.assertEqual(row['cost'],Q(3,2));self.assertEqual(row['terminal'],Q(1,2))
        # A greedy unmatched mass at position1 costs1, so terminal is different.
        self.assertNotEqual(row['terminal'],Q(1))

    def test_finite_measure_types_order_and_coverage(self):
        m=meter()
        for xs,bs in (([Q(1)],[Q(1),Q(2)]),([Q(1),Q(1)],[Q(1),Q(-1)]),
            ([Q(0)],[Q(1)]),([1],[Q(1)]),([Q(1)],[1])):
            with self.assertRaises(ValueError):C._flow_variation(xs,bs,m)

    def test_negative_and_zero_kernel_prefixes_cannot_be_forged(self):
        m=meter()
        for profile,values in (('D',['1','1']),('D',['-1','0']),('S',['1','0']),('Q',['0'])):
            bad=fixture();bad['positive_prefixes'][profile]=values
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_missing_altered_or_unsorted_kernel_atoms(self):
        m=meter()
        for change in ('missing','sign','base','order','bool'):
            bad=fixture()
            if change=='missing':bad['kernels']['D'].pop()
            elif change=='sign':bad['kernels']['D'][1][1]='1'
            elif change=='base':bad['kernels']['Q'][0][0]=5
            elif change=='order':bad['kernels']['S'].reverse()
            else:bad['kernels']['P'][0][0]=True
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_complete_column_coverage_and_source_binding(self):
        m=meter()
        for change in ('missing','duplicate','order','base','parameters'):
            bad=fixture()
            if change=='missing':bad['columns'].pop()
            elif change=='duplicate':bad['columns'][1]=copy.deepcopy(bad['columns'][0])
            elif change=='order':bad['columns'].reverse()
            elif change=='base':bad['columns'][0]['base']=3
            else:bad['columns'][0]['identity']['parameters']['gamma']='1/2'
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_column_kernel_masses_cannot_be_swapped(self):
        m=meter();bad=fixture();bad['columns'][1]['identity']['profile_coefficients']=['0','1','1','1']
        with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)
        bad=fixture();bad['columns'][0]['identity']['profile_coefficients']=['2','0','2','2']
        with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_missing_origin_or_floor_exit_cannot_pass_old_identity_rule(self):
        m=meter()
        for change in ('period','row','sign'):
            bad=fixture();col=bad['columns'][0]['identity']
            if change=='period':col['period']=28
            elif change=='row':col['floor_coefficients'].pop()
            else:col['floor_coefficients'][0]['c']='-1'
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_terminal_coefficient_and_degree_exact(self):
        m=meter()
        for key,value in (('endpoint_coefficient','335'),('endpoint_coefficient','337'),('log_degree',1),('log_degree',True)):
            bad=fixture();bad[key]=value
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_head_cutoff_zero_half_and_arbitrary_fraction(self):
        m=meter()
        for theta in ('0','1/2','1/257'):
            out=C.verify_fractional_flow(fixture(theta=theta),m)
            self.assertTrue(out['head_bound_proved']);self.assertEqual(out['head_bound']['N_power'],theta)
            self.assertEqual(out['head_bound']['coefficient'],'168/5')

    def test_underpriced_head_and_out_of_scope_theta(self):
        m=meter()
        for key,value in (('head_coefficient','33'),('head_coefficient','34'),('head_theta','-1/257'),('head_theta','129/257')):
            bad=fixture();bad[key]=value
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_exit_cutoff_price_and_discrete_plus_one(self):
        m=meter()
        for rho in ('0','3/4','1/257'):
            cert=fixture();cert['exit_rho']=rho;out=C.verify_fractional_flow(cert,m)
            self.assertEqual(out['exit_residual_bound']['coefficient'],'336/5')
            self.assertEqual(Q(out['exit_residual_bound']['N_power']),2*Q(rho)-1)
        # Full integer strip integration: D-floor(y) on each unit cell.
        for D in range(2,20):
            for K in range(1,D//2+1):
                exact=sum(D-j for j in range(D-K,D))
                self.assertEqual(exact,K*(K+1)//2)
                self.assertLessEqual(2*K*(K+1),4*K*K);m.charge(100)
        self.assertEqual(sum(4-j for j in range(3,4)),1)
        self.assertNotEqual(Q(1),Q(1,2)) # naive continuous K^2/2 is wrong at K1.

    def test_exit_underpricing_horizon_and_wrong_rho_rejected(self):
        m=meter()
        for key,value in (('exit_coefficient','67'),('exit_rho','-1/257'),('exit_rho','193/257'),('horizon','last token')):
            bad=fixture();bad[key]=value
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_general_rational_alpha_and_positive_band(self):
        m=meter();cert=fixture('1/257','1/257')
        for obj in [cert['parameters']]+[r['identity']['parameters'] for r in cert['columns']]:
            obj.update(gamma='257/1026',tau='3/7')
        out=C.verify_fractional_flow(cert,m)
        self.assertEqual(Q(out['terminal_bound']['coefficient']),Q(504)/(2-Q(1,257)))
        self.assertEqual(Q(out['head_bound']['coefficient']),Q(84)/(3-Q(1,257)))

    def test_wrong_carrier_and_forged_global_proof_fields(self):
        m=meter();bad=fixture();bad['carrier']='(p*d)^(-t)'
        with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)
        for where,key in (('', 'long_prefix_bound_proved'),('kernels','target_bound'),('positive_prefixes','all_proved')):
            bad=fixture();obj=bad if not where else bad[where];obj[key]=True
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_only_head_and_terminal_are_paid(self):
        m=meter();out=C.verify_fractional_flow(fixture(),m)
        self.assertTrue(out['head_bound_proved']);self.assertTrue(out['terminal_bound_proved']);self.assertTrue(out['exit_residual_bound_proved'])
        for key in ('core_prefix_bound_proved','long_prefix_bound_proved','whole_signed_target_bound_proved','uniform_full_flow_bound_proved','RH_proved','source_arrays_or_kernel_integrals_evaluated'):
            self.assertIs(out[key],False)
        self.assertFalse(out['terminal_bound']['literal_greedy_leftover_claimed'])
        self.assertTrue(out['flow']['plans_may_depend_on_t'])
        self.assertTrue(out['variation_split']['unit_and_all_range_exits_retained'])

    def test_charge_only_pipeline_meter(self):
        m=PipelineMeter();METERS.append(m)
        self.assertTrue(C.verify_fractional_flow(fixture(),m)['verified']);self.assertGreater(m.operations,100)

    def test_alias_float_bool_and_invalid_source_parameters(self):
        m=meter()
        for key,value in (('alpha','2/4'),('alpha',0.5),('alpha','1'),('gamma','0'),('tau','1'),('p',True),('primes',[2,9])):
            bad=fixture();bad['parameters'][key]=value
            with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)
        bad=fixture();bad['head_theta']=True
        with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)

    def test_resource_guard_work_and_bit_capacity(self):
        m=meter();bad=fixture();bad['head_theta']=str(1<<4097)
        with self.assertRaises(ValueError):C.verify_fractional_flow(bad,m)
        tiny=C.Meter(cap=1);METERS.append(tiny)
        with self.assertRaises(OverflowError):C.verify_fractional_flow(fixture(),tiny)

if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_mobius_fractional_flow_061 operations='+str(sum(m.operations for m in METERS)))
