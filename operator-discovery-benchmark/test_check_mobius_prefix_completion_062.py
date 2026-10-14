"""Tiny synthetic exact completions and adversarial horizon/residual tests."""
import copy
import unittest
from fractions import Fraction as Q
from math import gcd
import check_mobius_prefix_completion_062 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]
def meter():
    m=C.Meter(cap=1_000_000_000);METERS.append(m);return m

def parameters():
    return {'alpha':'1/2','gamma':'1/3','tau':'1/2','primes':[2,7],'p':2,'q':7}

def full_completion():
    # Exact full W floor expressions, not LP inference or a partial winner.
    horizons=[2,4,7,8,14,28];rows=[]
    for r in (Q(2,7),Q(1)):
        values={28:Q(1),14:Q(-3),7:Q(2),8:-r,4:3*r,2:-2*r}
        rows.append([str(values[x]) for x in horizons])
    return {'schema':'mobius-prefix-completion-v1','parameters':parameters(),'N':14,'y':28,'H':1,
        'horizons':horizons,'ratios':['2/7','1'],'coefficients':rows,'budget':'12'}

def pure_short():
    return {'schema':'mobius-prefix-completion-v1','parameters':parameters(),'N':5,'y':1,'H':1,
        'horizons':[],'ratios':['2/7','1'],'coefficients':[[],[]],'budget':'5/7'}

def own_weight(N,a):return int(Q(4*N,a))-3*int(Q(2*N,a))+2*int(Q(N,a))

def own_budget(cert,m):
    totals=[]
    for ratio,row in zip(map(Q,cert['ratios']),cert['coefficients']):
        row=list(map(Q,row));cost=sum(map(abs,row),Q(0))
        for d in range(1,cert['H']+1):
            if gcd(d,14)!=1:continue
            target=Q(own_weight(cert['N'],2*d))-ratio*own_weight(cert['N'],7*d) if d<=cert['y'] else Q(0)
            cost+=abs(target-sum((c*(X//d) for c,X in zip(row,cert['horizons'])),Q(0)));m.charge(100)
        totals.append(cost)
    return str(max(totals))

def ordinary_mu(n,m):
    sign=1;factor=2
    while factor*factor<=n:
        m.charge(4)
        if n%factor==0:
            n//=factor;sign=-sign
            if n%factor==0:return 0
        factor+=1
    return -sign if n>1 else sign

def smooth_count(X,m):
    count=0
    for n in range(1,X+1):
        residual=n
        for p in (2,7):
            while residual%p==0:residual//=p;m.charge(4)
        count+=residual==1;m.charge(4)
    return count

class PrefixCompletionTests(unittest.TestCase):
    def test_exact_full_floor_completion(self):
        m=meter();out=C.verify_completion(full_completion(),m)
        self.assertTrue(out['finite_prefix_bound_proved']);self.assertTrue(out['parameter_continuum_proved'])
        self.assertEqual(out['endpoint_costs'],[
            {'ratio':'2/7','coefficient_l1':'54/7','short_residual_l1':'0','total':'54/7'},
            {'ratio':'1','coefficient_l1':'12','short_residual_l1':'0','total':'12'}])

    def test_empty_horizons_and_complete_nonzero_unit_residual(self):
        m=meter();out=C.verify_completion(pure_short(),m)
        self.assertEqual(out['budget'],'5/7')
        self.assertEqual(out['endpoint_costs'][0]['short_residual_l1'],'5/7')
        self.assertEqual(out['endpoint_costs'][1]['short_residual_l1'],'0')
        self.assertTrue(out['completion']['unit_in_short_residual'])

    def test_nontrivial_completed_short_residual_includes_squareful_rows(self):
        m=meter();cert=pure_short();cert.update(H=10,horizons=[9],coefficients=[['1'],['1']])
        cert['budget']=own_budget(cert,m);out=C.verify_completion(cert,m)
        self.assertEqual(out['completion']['coprime_short_rows'],4) #1,3,5,9; mu(9)=0 still priced.
        self.assertTrue(out['completion']['nonsquarefree_coprime_rows_retained'])
        self.assertGreater(Q(out['endpoint_costs'][0]['short_residual_l1']),1)

    def test_direct_tiny_mu_convolution_and_interior_ratio(self):
        m=meter();cert=full_completion();N=14;r=Q(3,5)
        lam=(r-Q(2,7))/(1-Q(2,7))
        row=[(1-lam)*Q(a)+lam*Q(b) for a,b in zip(*cert['coefficients'])]
        source=Q(0)
        for d in range(1,4*N+1):
            if gcd(d,14)!=1:continue
            source+=ordinary_mu(d,m)*(own_weight(N,2*d)-r*own_weight(N,7*d));m.charge(100)
        complete=sum((c*smooth_count(X,m) for c,X in zip(row,cert['horizons'])),Q(0))
        self.assertEqual(source,complete)
        self.assertLessEqual(sum(map(abs,row)),Q(cert['budget']))
        self.assertTrue(C.verify_completion(cert,m)['parameter_continuum_proved'])

    def test_tail_horizon_exit_beyond_original_D_is_checked(self):
        m=meter();bad=pure_short();bad.update(H=10,horizons=[20],coefficients=[['1'],['1']])
        bad['budget']=own_budget(bad,m)
        #d11>original D10 remains coprime and floor20/d11=1.
        with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_zero_extended_added_horizon_is_valid(self):
        m=meter();cert=full_completion();cert['horizons'].append(56)
        for row in cert['coefficients']:row.append('0')
        out=C.verify_completion(cert,m)
        self.assertEqual(out['completion']['tail_checked_through'],56)
        self.assertTrue(out['completion']['all_added_horizon_exits_retained'])

    def test_tail_change_and_lost_prefix_cutoff_rejected(self):
        m=meter();bad=full_completion();bad['y']=1
        with self.assertRaises(ValueError):C.verify_completion(bad,m)
        bad=full_completion();bad['coefficients'][0][-1]='0'
        with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_every_endpoint_row_and_horizon_must_be_present(self):
        m=meter()
        for change in ('row','coefficient','horizon','swap'):
            bad=full_completion()
            if change=='row':bad['coefficients'].pop()
            elif change=='coefficient':bad['coefficients'][0].pop()
            elif change=='horizon':bad['horizons'].pop()
            else:bad['coefficients'].reverse()
            with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_budget_exact_no_omitted_unit_or_underpayment(self):
        m=meter()
        for value in ('0','4/7','6/7','-1'):
            bad=pure_short();bad['budget']=value
            with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_horizon_order_duplicates_domains_and_types(self):
        m=meter()
        for horizons in ([0],[57],[2,2],[4,2],[True]):
            bad=full_completion();bad['horizons']=horizons
            with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_N_y_H_integer_and_capacity_gates(self):
        m=meter()
        for key,values in (('N',(1,65537,True)),('y',(0,29,True)),('H',(0,29,True))):
            for value in values:
                bad=full_completion();bad[key]=value
                with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_general_rational_source_parameters(self):
        m=meter();cert=full_completion();cert['parameters'].update(alpha='1/257',gamma='257/1026',tau='3/7')
        self.assertTrue(C.verify_completion(cert,m)['verified'])
        cert['coefficients'][0][-1]='-1' #tail-visible sign error relative exact source.
        with self.assertRaises(ValueError):C.verify_completion(cert,m)

    def test_actual_prime_mask_and_parameter_gates(self):
        m=meter()
        for key,value in (('primes',[2,9]),('primes',[7,2]),('p',7),('q',5),('alpha','1'),('gamma','0'),('tau','1')):
            bad=full_completion();bad['parameters'][key]=value
            with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_ratios_canonical_ordered_and_source_bound(self):
        m=meter()
        for values in (['1','2/7'],['3/7','1'],['4/14','1'],['2/7']):
            bad=full_completion();bad['ratios']=values
            with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_forged_proof_scope_and_extra_fields(self):
        m=meter()
        for key in ('uniform_N_growth_proved','all_y_bound_proved','RH_proved'):
            bad=full_completion();bad[key]=True
            with self.assertRaises(ValueError):C.verify_completion(bad,m)
        bad=full_completion();bad['parameters']['source_verified']=True
        with self.assertRaises(ValueError):C.verify_completion(bad,m)

    def test_pointwise_continuum_is_not_all_scale_proof(self):
        m=meter();out=C.verify_completion(full_completion(),m)
        self.assertEqual(out['finite_prefix_bound']['N_and_y_scope'],'only the exact fixed integer N,y in this certificate')
        for key in ('uniform_N_growth_proved','all_y_bound_proved','core_bound_proved','whole_signed_target_bound_proved','RH_proved','scientific_source_values_or_kernel_integrals_evaluated'):
            self.assertIs(out[key],False)

    def test_fraction_type_and_resource_guards(self):
        m=meter()
        for value in (True,1.0,'1.0','2/2',str(1<<4097)):
            bad=full_completion();bad['coefficients'][0][0]=value
            with self.assertRaises(ValueError):C.verify_completion(bad,m)
        tiny=C.Meter(cap=1);METERS.append(tiny)
        with self.assertRaises(OverflowError):C.verify_completion(full_completion(),tiny)

    def test_charge_only_pipeline_meter(self):
        m=PipelineMeter();METERS.append(m)
        self.assertTrue(C.verify_completion(full_completion(),m)['verified']);self.assertGreater(m.operations,100)

if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_mobius_prefix_completion_062 operations='+str(sum(m.operations for m in METERS)))
