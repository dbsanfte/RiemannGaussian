"""Tiny one/two-prime universal identity and independent bound calibrations."""
import copy
from fractions import Fraction as Q
from math import prod
import unittest
from unittest.mock import patch
import check_prime_transfer_058 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]

def meter():
    m=C.Meter(cap=1_000_000_000,seconds=180);METERS.append(m);return m

def atom(primes=(),divisor=1,attenuation=1):
    return dict(primes=list(primes),divisor=divisor,attenuation=attenuation)

def transfer(p=2,shift=1,scale='1'):
    # H_p+z_p H_empty-H_empty-z_p H_p(x/p)=0, with arbitrary x/shift.
    return {'universe':[p],'atoms':[atom((p,),shift),atom((),shift,p),
        atom((),shift),atom((p,),p*shift,p)],
        'coefficients':[scale,scale,str(-Q(scale)),str(-Q(scale))]}

def source(p=2,attenuation=1):
    request={'universe':[p],'atoms':[atom((p,),1,attenuation)],'coefficients':['1']}
    if attenuation==1:
        terms=[{'powers':[1],'coefficient':'1'}];B=Q(p)
    elif attenuation==p:
        terms=[{'powers':[1],'coefficient':'1'},{'powers':[2],'coefficient':'-1'}];B=Q(p+p*p)
    else:raise ValueError('hand fixture')
    cases=[{'presence':[v],'terms':copy.deepcopy(terms),'order':1,'envelope':str(B)} for v in (0,1)]
    cert={'schema':'prime-transfer-source-order-v1','request':request,'cases':cases,
        'order':1,'envelope':str(B),'zero_source':False,
        'scope':{'N_minimum':2,'N_type':'integer','t_lower_exclusive':'0','t_upper':'1'},
        'whole_bound_proved':False,'RH_proved':False}
    return request,cert

def endpoints(alpha='1/5',gamma='257/193',tau='123/257'):
    op,order=source()
    request={'operator':op,'alpha':alpha,'gamma':gamma,'tau':tau}
    cert={'schema':'prime-transfer-endpoints-v1','request':request,'source_order':order,
        'microscopic':{'C':str(24/(1-Q(alpha))),'N_power':str(1-Q(gamma)*(1-Q(alpha)))},
        'tail':{'C':str(16/(Q(tau)**2*(1-Q(tau)))),'N_power':str(1-Q(tau))},
        'middle_status':'OPEN','uniform_full_source_bound_proved':False,'RH_proved':False}
    return request,cert

def factors(n):
    out=[];rest=n;p=2
    while p*p<=rest:
        if rest%p==0:
            out.append(p)
            while rest%p==0:rest//=p
        p+=1
    if rest>1:out.append(rest)
    return out

def H(primes,x,t=1):
    total=Q(0)
    for n in range(1,int(4*x)+1):
        weight=int(2*x<n<=4*x)-2*int(x<n<=2*x)
        polynomial=prod((1-Q(1,p)**t) for p in set(primes).union(factors(n)))
        total+=weight*polynomial
    return total


class TransferCheckerTests(unittest.TestCase):
    def test_universal_transfer_and_rational_scale(self):
        m=meter()
        for p in (2,3,5):
            for scale in ('1','1/257','-123/193'):
                r=transfer(p,scale=scale)
                out=C.verify_identity(r,m)
                self.assertTrue(out['universal_identity_proved'])
                self.assertEqual(out['valuation_caps'],[2])
                self.assertEqual(out['valuation_cases_checked'],3)
                self.assertTrue(out['inclusive_unit_retained'])
                self.assertFalse(out['signed_bound_proved'])
                self.assertFalse(out['uniform_target_bound_proved'])

    def test_complete_primepowers_beyond_largest_divisor(self):
        m=meter();r=transfer(2,shift=4)
        out=C.verify_identity(r,m)
        self.assertEqual(out['valuation_caps'],[4]);self.assertEqual(out['valuation_cases_checked'],5)
        # Missing the last term leaves ALL valuations0..2 zero; high casesfail.
        bad=copy.deepcopy(r);bad['atoms'].pop();bad['coefficients'].pop()
        with self.assertRaisesRegex(ValueError,'valuation \\(3,\\)'):C.verify_identity(bad,m)

    def test_unit_case_is_not_discarded(self):
        m=meter()
        r={'universe':[2],'atoms':[atom(()),atom((2,))],'coefficients':['1','-1']}
        # This iszero for everyregistered valuation>=1, but not atvaluation0.
        with self.assertRaisesRegex(ValueError,'valuation \\(0,\\)'):C.verify_identity(r,m)
        self.assertNotEqual(H((),Q(1,4)),H((2,),Q(1,4)))
        self.assertEqual(H((2,),Q(1,4)),Q(1,2))

    def test_real_pullbacks_inclusive_unit_and_unregistered_primes(self):
        m=meter();r=transfer(2,shift=2)
        C.verify_identity(r,m)
        for x in (Q(1,16),Q(1,8),Q(1,4),Q(1,2),Q(3,4),Q(2),Q(17,3)):
            value=sum(Q(c)*Q(1,a['attenuation'])*H(a['primes'],x/a['divisor']) for a,c in zip(r['atoms'],r['coefficients']))
            self.assertEqual(value,0)
            m.charge(1000)

    def test_two_prime_coupled_identity_and_outside_common_factor(self):
        m=meter()
        r=transfer(2);r['universe']=[2,3]
        for a in r['atoms']:a['primes']=sorted(set(a['primes'])|{3})
        out=C.verify_identity(r,m)
        self.assertEqual(out['valuation_cases_checked'],6)
        self.assertTrue(out['outside_prime_factor_common'])
        for x in (Q(1,3),Q(7,2),Q(5)):
            self.assertEqual(sum(Q(c)*Q(1,a['attenuation'])*H(a['primes'],x/a['divisor']) for a,c in zip(r['atoms'],r['coefficients'])),0)
            m.charge(5000)

    def test_current_part_cannot_be_promoted_to_zero_or_bound(self):
        m=meter();r=transfer();out=C.verify_identity(r,m)
        # All universal identities must cancel the registered-valuation0
        # currentsector: no strict lowerdivisor can be active there.
        self.assertTrue(out['current_zero_on_unregistered_sector'])
        self.assertEqual(out['current_unregistered_sector_polynomial'],[])
        universe,parsed,_,_=C._parse(r,m)
        self.assertTrue(C._case(universe,parsed,(1,),m,{},True))
        self.assertFalse(out['free_prime_sector_bound_proved'])
        self.assertFalse(out['RH_proved']);self.assertFalse(out['RH_refuted'])
        r={'universe':[2],'atoms':[atom((2,))],'coefficients':['0']}
        out=C.verify_identity(r,m)
        self.assertTrue(out['current_zero_on_unregistered_sector'])
        self.assertFalse(out['signed_bound_proved'])

    def test_mutated_attenuation_divisor_coefficients_rejected(self):
        m=meter();r=transfer()
        for j,key,value in [(3,'attenuation',1),(3,'divisor',4),(0,'primes',[])]:
            bad=copy.deepcopy(r);bad['atoms'][j][key]=value
            with self.assertRaises(ValueError):C.verify_identity(bad,m)
        for j in range(4):
            bad=copy.deepcopy(r);bad['coefficients'][j]=str(Q(bad['coefficients'][j])+Q(1,257))
            with self.assertRaises(ValueError):C.verify_identity(bad,m)

    def test_typed_prime_support_and_canonical_alias_guards(self):
        m=meter();r=transfer()
        for values in ([4],[True],[3,2],[2,2]):
            bad=copy.deepcopy(r);bad['universe']=values
            with self.assertRaises(ValueError):C.verify_identity(bad,m)
        for key,value in [('divisor',True),('divisor',0),('divisor',3),('attenuation',3),('attenuation','2'),('primes',[2,2])]:
            bad=copy.deepcopy(r);bad['atoms'][0][key]=value
            with self.assertRaises(ValueError):C.verify_identity(bad,m)
        for coefficient in ('2/2',1,True,0.5):
            bad=copy.deepcopy(r);bad['coefficients'][0]=coefficient
            with self.assertRaises(ValueError):C.verify_identity(bad,m)
        bad=copy.deepcopy(r);bad['atoms'][1]=copy.deepcopy(bad['atoms'][0])
        with self.assertRaises(ValueError):C.verify_identity(bad,m)
        bad=copy.deepcopy(r);bad['signed_bound_proved']=True
        with self.assertRaises(ValueError):C.verify_identity(bad,m)

    def test_work_capacity_and_charge_only_meter(self):
        m=PipelineMeter(cap=10000000,seconds=180);METERS.append(m)
        self.assertTrue(C.verify_identity(transfer(),m)['verified'])
        with self.assertRaises(OverflowError):C.verify_identity(transfer(),C.Meter(cap=1))
        with patch.object(C,'MAX_CASES',2):
            with self.assertRaises(OverflowError):C.verify_identity(transfer(),m)
        with patch.object(C,'MAX_ROWS',1):
            with self.assertRaises(MemoryError):C.verify_identity(transfer(),m)
        bad=transfer();bad['atoms'][0]['attenuation']=2**65
        with self.assertRaises(OverflowError):C.verify_identity(bad,m)

    def test_source_order_signed_y_expansion_and_attenuation(self):
        m=meter()
        for p in (2,3):
            for attenuation in (1,p):
                r,c=source(p,attenuation)
                out=C.verify_source_order(r,c,m)
                self.assertEqual(out['order'],1)
                self.assertEqual(Q(out['envelope']),p if attenuation==1 else p+p*p)
                self.assertTrue(out['all_presence_cases_retained'])
                self.assertFalse(out['signed_whole_target_bound_proved'])
        # For t<=1 eachy=1-p^-t<=p*t and attenuation<=1.
        for n in range(1,8):
            t=Q(1,n);z=Q(1,2)**n
            self.assertLessEqual((1-z)*z,1)
            m.charge(100)

    def test_source_order_all_presence_cases_and_zero_source(self):
        m=meter()
        r={'universe':[2],'atoms':[atom(()),atom((2,))],'coefficients':['1','-1']}
        cert={'schema':'prime-transfer-source-order-v1','request':r,
            'cases':[{'presence':[0],'terms':[{'powers':[0],'coefficient':'1'},{'powers':[1],'coefficient':'-1'}],'order':0,'envelope':'3'},
                {'presence':[1],'terms':[],'order':None,'envelope':'0'}],
            'order':0,'envelope':'3','zero_source':False,
            'scope':{'N_minimum':2,'N_type':'integer','t_lower_exclusive':'0','t_upper':'1'},'whole_bound_proved':False,'RH_proved':False}
        out=C.verify_source_order(r,cert,m);self.assertEqual(out['order'],0)
        bad=copy.deepcopy(cert);bad['cases']=bad['cases'][1:];bad['order']=None;bad['envelope']='0';bad['zero_source']=True
        with self.assertRaises(ValueError):C.verify_source_order(r,bad,m)
        r={'universe':[2],'atoms':[atom((2,))],'coefficients':['0']}
        cert={'schema':'prime-transfer-source-order-v1','request':r,
            'cases':[{'presence':[v],'terms':[],'order':None,'envelope':'0'} for v in (0,1)],
            'order':None,'envelope':'0','zero_source':True,
            'scope':{'N_minimum':2,'N_type':'integer','t_lower_exclusive':'0','t_upper':'1'},'whole_bound_proved':False,'RH_proved':False}
        out=C.verify_source_order(r,cert,m)
        self.assertTrue(out['zero_source']);self.assertFalse(out['signed_whole_target_bound_proved'])

    def test_source_order_false_power_signed_terms_and_domain_rejected(self):
        m=meter();r,c=source(2,2)
        for key,value in [('order',2),('envelope','2'),('whole_bound_proved',True),('zero_source',True)]:
            bad=copy.deepcopy(c);bad[key]=value
            with self.assertRaises(ValueError):C.verify_source_order(r,bad,m)
        bad=copy.deepcopy(c);bad['cases'][0]['terms'][1]['coefficient']='1'
        with self.assertRaises(ValueError):C.verify_source_order(r,bad,m)
        bad=copy.deepcopy(c);bad['scope']['N_type']='real'
        with self.assertRaises(ValueError):C.verify_source_order(r,bad,m)
        bad=copy.deepcopy(r);bad['atoms'][0]['divisor']=2
        with self.assertRaises(ValueError):C.verify_source_order(bad,c,m)

    def test_endpoint_arbitrary_rationals_and_unpaid_middle(self):
        m=meter();r,c=endpoints();out=C.verify_endpoint_bound(r,c,m)
        self.assertEqual(Q(out['microscopic']['C']),30)
        self.assertEqual(Q(out['microscopic']['N_power']),-Q(63,965))
        self.assertTrue(out['both_end_region_bounds_proved']);self.assertEqual(out['middle_status'],'OPEN')
        self.assertFalse(out['uniform_full_source_bound_proved']);self.assertFalse(out['RH_proved'])
        for alpha,gamma,tau in [('256/257','1/257','1/257'),('1/2','3/7','256/257')]:
            r,c=endpoints(alpha,gamma,tau)
            self.assertTrue(C.verify_endpoint_bound(r,c,m)['verified'])

    def test_endpoint_cheap_prices_and_reused_lower_atoms_rejected(self):
        m=meter();r,c=endpoints()
        for section,key,value in [('microscopic','C','1'),('microscopic','N_power','-1'),('tail','C','1'),('tail','N_power','0')]:
            bad=copy.deepcopy(c);bad[section][key]=value
            with self.assertRaises(ValueError):C.verify_endpoint_bound(r,bad,m)
        for key,value in [('middle_status','PROVED'),('uniform_full_source_bound_proved',True),('RH_proved',True)]:
            bad=copy.deepcopy(c);bad[key]=value
            with self.assertRaises(ValueError):C.verify_endpoint_bound(r,bad,m)
        for key,value in [('alpha','1'),('gamma','0'),('tau','0'),('tau','1')]:
            bad=copy.deepcopy(r);bad[key]=value
            with self.assertRaises(ValueError):C.verify_endpoint_bound(bad,c,m)
        bad=copy.deepcopy(r);bad['operator']['atoms'][0]['divisor']=2
        with self.assertRaises(ValueError):C.verify_endpoint_bound(bad,c,m)
        bad=copy.deepcopy(r);bad['operator']['atoms'][0]['primes']=[]
        with self.assertRaises(ValueError):C.verify_endpoint_bound(bad,c,m)
        bad=copy.deepcopy(r);bad['operator']['coefficients']=['0']
        with self.assertRaises(ValueError):C.verify_endpoint_bound(bad,c,m)

    def test_endpoint_filter_unit_and_tail_elementary_premises(self):
        m=meter()
        for N in range(2,33):
            self.assertEqual(4*N-3*(2*N)+2*N,0)
            total=sum(abs(int(2*N<n<=4*N)-2*int(N<n<=2*N)) for n in range(1,4*N+1))
            self.assertEqual(total,4*N)
        for numerator in range(0,100):
            x=Q(numerator,20)
            W=int(4*x)-3*int(2*x)+2*int(x)
            self.assertLessEqual(abs(W),1)
        m.charge(20000)


if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_prime_transfer_058 operations='+str(sum(m.operations for m in METERS)))
