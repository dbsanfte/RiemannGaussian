"""New055 synthetic source/algebra/conditional recovery tests only."""
import copy
from fractions import Fraction as Q
from itertools import combinations
from math import gcd
import unittest

import check_prime_insertion_055 as C
import prime_insertion_source_055 as P
import prime_scale_source_053 as SOURCE
import prime_scale_dense_054 as DENSE
from prime_bank_candidates import Meter as PipelineMeter

M=C.Meter(cap=300_000_000,seconds=180)
PM=P.Meter(cap=300_000_000,seconds=180)
SM=SOURCE.Meter(cap=300_000_000,seconds=180)
DM=DENSE.Meter(cap=300_000_000,seconds=180)
PIPE=PipelineMeter(cap=300_000_000,seconds=180)
BANKS={}


def fixture(alpha='1/2'):
    if alpha not in BANKS:
        source=SOURCE.make_source(alpha,144,bits=32,meter=SM)
        fields={k:getattr(source,k) for k in ('alpha','max_n','bits','mu','prefix_w','prefix_up','prefix_down')}
        fields['metadata']=source.metadata()
        dense=DENSE.dense_source(fields,DM)
        fields={k:getattr(dense,k) for k in ('alpha','max_n','bits','Acenter','Adown','Aup')}
        fields['metadata']=dense.metadata()
        BANKS[alpha]=P.build_insertion_sources(fields,[[],[2],[3],[2,3]],PM)
    return BANKS[alpha]


def finite(alpha='1/2',primes=None,cs=None,N=2):
    request={'alpha':alpha,'primes':[] if primes is None else primes,'q':2,
        'coefficients':[2,-3,1] if cs is None else cs,'N':N}
    result=P.evaluate_filter(fixture(alpha),request['primes'],2,request['coefficients'],N,PM)
    return request,{'lower':result['lower'],'upper':result['upper']}


def energy(delta='1/257',Cvalue='1/64'):
    r={'alpha':'1/5','features':[[],[2],[3]],'coefficients':[1,-2,1],
        'lambda':'1/2','delta':delta,'C':Cvalue}
    d,c=Q(delta),Q(Cvalue)
    cert={'schema':'prime-insertion-energy-recovery-v1','request':copy.deepcopy(r),
        'matrix_terms':[{'i':0,'j':0,'coefficient':'3/2'},
            {'i':0,'j':1,'coefficient':'-2'},{'i':0,'j':2,'coefficient':'1'},
            {'i':1,'j':1,'coefficient':'2'},{'i':1,'j':2,'coefficient':'-2'},
            {'i':2,'j':2,'coefficient':'1/2'}],
        'base_upper':'24300',
        'recurrence':{'minimum':2,'children':[0,1],
            'formula':'F(2N+r)<=F(N)+C/N^delta','status':'OPEN'},
        'recovery':{'kind':'bounded' if d else 'logarithmic',
            'constant':str(Q(24300)+2*c/d) if d else '24300',
            'log_coefficient':'0' if d else str(c),'logarithm_base':2},
        'uniform_drift_proved':False,'uniform_target_bound_proved':False,'RH_proved':False}
    return r,cert


def tail(primes=None,tau=8,alpha='1/5'):
    primes=[] if primes is None else primes
    R=1
    for p in primes:R*=p
    r={'alpha':alpha,'primes':primes,'tau':tau}
    cert={'schema':'prime-insertion-laplace-tail-v1','request':copy.deepcopy(r),
        'product':R,'integer_N_minimum':2,
        'filter':{'q':2,'coefficients':[2,-3,1],'normalization':'divide_by_alpha'},
        'integrand':'R^-t*sum_(d<=4N,gcd(d,R)=1)mu(d)*d^-t*sum_(e|R)mu(e)*W(N/(d*e))',
        'W':'floor(4y)-3floor(2y)+2floor(y)',
        'normalizer':'1/(alpha*I_alpha)',
        'uniform_absolute_upper':str(Q(18,2**tau) if not primes else Q(12*2**len(primes),R**tau)),
        'unpaid_core':'0<t<tau','tail_bound_proved':True,'complete_target_bound_proved':False,'RH_proved':False}
    return r,cert


def trial_mu(n):
    value=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;value=-value
            if n%p==0:return 0
            while n%p==0:n//=p
        p+=1
    return -value if n>1 else value


def tearDownModule():
    total=sum(m.operations for m in (M,PM,SM,DM,PIPE))
    print('SYNTHETIC_WORK module=test_check_prime_insertion_055 operations='+str(total))


class PrimeInsertionTests(unittest.TestCase):
    def symbolic(self,alpha='1/2',primes=None):
        primes=[] if primes is None else primes
        request={'alpha':alpha,'primes':primes}
        cert=P.boolean_certificate(alpha,primes,PM)
        return request,cert

    def test_empty_and_complete_three_prime_boolean_algebra(self):
        for primes in ([],[2],[2,3],[2,3,5]):
            r,c=self.symbolic(primes=primes)
            out=C.verify_insertion(r,c,M)
            self.assertIs(out['verified'],True)
            self.assertFalse(out['uniform_prefix_bound_proved'])
            self.assertFalse(out['RH_proved'])
            self.assertEqual(len(c['subset_terms']),1<<len(primes))
            self.assertEqual([row['atom_coefficient'] for row in c['atom_cancellation_rows']],
                             [0]*((1<<len(primes))-1)+[1])

    def test_source_unit_and_radical_state_restrictions(self):
        r,c=self.symbolic(primes=[2,3])
        for field,value in [('domain_minimum',1),('unit_n1_excluded',False),
                ('source_condition','arbitrary bounded coefficients'),
                ('boolean_relations','E_p^2=E_p for every sequence'),
                ('all_scale_bound_proved',True),('source_chain_replayed_here',True)]:
            bad=copy.deepcopy(c);bad[field]=value
            with self.assertRaises(ValueError):C.verify_insertion(r,bad,M)
        self.assertEqual(C.verify_insertion(r,c,M)['unit_value'],
                         '-(log(product))^alpha; exactly0 for empty set')

    def test_missing_atoms_and_incorrect_idempotence_rejected(self):
        r,c=self.symbolic(primes=[2,3,5])
        for key in ('subset_terms','atom_cancellation_rows','square_reduction'):
            bad=copy.deepcopy(c);bad[key].pop()
            with self.assertRaises(ValueError):C.verify_insertion(r,bad,M)
        bad=copy.deepcopy(c);bad['atom_cancellation_rows'][-1]['atom_coefficient']=-1
        with self.assertRaises(ValueError):C.verify_insertion(r,bad,M)
        bad=copy.deepcopy(c);bad['square_reduction'][1]['coefficient']=1
        with self.assertRaises(ValueError):C.verify_insertion(r,bad,M)

    def test_prime_and_exact_rational_parameter_guards(self):
        for primes in ([4],[2,2],[3,2],[1],[True]):
            with self.assertRaises(ValueError):C.verify_insertion({'alpha':'1/2','primes':primes},{},M)
        for alpha in ('0','1','2/4',0.5,True,'-1/2'):
            with self.assertRaises(ValueError):C.verify_insertion({'alpha':alpha,'primes':[]},{},M)
        r,c=self.symbolic('1/257',[2,3]);self.assertTrue(C.verify_insertion(r,c,M)['verified'])

    def test_independent_formal_shift_and_shared_prime_mask(self):
        # Arbitrary COMMON divisor atoms prove the exact identity without
        # relying on the producer's floating arithmetic or success formulas.
        def phi(d):return Q((d-1)**2,17)
        def kernel(n):return -sum(trial_mu(d)*phi(d) for d in range(1,n+1) if n%d==0)
        for S in ([],[2],[2,3]):
            subsets=[s for k in range(len(S)+1) for s in combinations(S,k)]
            R=1
            for p in S:R*=p
            for n in range(1,20):
                inserted=Q(0)
                for U in subsets:
                    divisor=1
                    for p in U:divisor*=p
                    inserted+=(-1)**len(U)*kernel(n*divisor);M.charge(n*divisor)
                expected=0 if gcd(n,R)>1 else -sum(trial_mu(d)*phi(R*d) for d in range(1,n+1) if n%d==0)
                self.assertEqual(inserted,expected)
            self.assertEqual(-phi(R),sum((-1)**len(U)*kernel(__import__('math').prod(U)) for U in subsets))

    def test_independent_mu_and_coprime_counts(self):
        mu=C.VALUES._mobius(120,M)
        self.assertEqual(list(map(int,mu[1:])),[trial_mu(n) for n in range(1,121)])
        _,_,R,subsets=C._parameters({'alpha':'1/2','primes':[2,3,5]},M)
        for t in range(1,101):
            self.assertEqual(C._cofactor_count(t,subsets,M),sum(gcd(n,R)==1 for n in range(1,t+1)))

    def test_fresh_empty_single_and_joint_interval_admission(self):
        for S in ([],[2],[3],[2,3]):
            r,c=finite(primes=S)
            out=C.verify_filter_interval(r,c,M)
            self.assertTrue(out['verified']);self.assertTrue(out['finite_only'])
            self.assertFalse(out['uniform_bound_proved']);self.assertFalse(out['RH_proved'])
            self.assertTrue(out['rebuild']['unit_correction_combined_before_rounding'])
            self.assertTrue(out['rebuild']['mu_recomputed'])

    def test_nonzero_P_one_and_excluded_unit(self):
        r,c=finite(primes=[2,3],cs=[-2,1],N=3)
        checked=C.verify_filter_interval(r,c,M)
        # Nonzero P(1) means the unit correction really participates.
        self.assertEqual(sum(r['coefficients']),-1)
        self.assertTrue(checked['verified'])
        # A filter concentrated at a scale containing only shared-prime2
        # has exact valuezero, not the negative insertion at n1.
        r,c=finite(primes=[2],cs=[1],N=2)
        checked=C.verify_filter_interval(r,c,M)
        self.assertEqual((checked['lower'],checked['upper']),('0','0'))

    def test_arbitrary_fractional_exponent_and_normalization(self):
        r,c=finite(alpha='1/257',primes=[2],cs=[-2,1],N=2)
        checked=C.verify_filter_interval(r,c,M)
        self.assertTrue(checked['verified'])
        lo,hi=Q(c['lower']),Q(c['upper'])
        # Omitting division byalpha is a different finite value.
        bad={'lower':str(lo/257),'upper':str(hi/257)}
        with self.assertRaises(ValueError):C.verify_filter_interval(r,bad,M)

    def test_private_cache_extension_and_alpha_key(self):
        context=C.prepare_context(M)
        r,c=finite(primes=[2],N=2)
        first=C.verify_filter_interval(r,c,M,context)
        repeated=C.verify_filter_interval(r,c,M,context)
        self.assertEqual(repeated['rebuild']['new_shifted_atoms'],0)
        self.assertGreater(repeated['rebuild']['reused_new_audit_atoms'],0)
        self.assertFalse(repeated['rebuild']['mu_recomputed'])
        r,c=finite(primes=[2],N=3)
        larger=C.verify_filter_interval(r,c,M,context)
        self.assertTrue(larger['rebuild']['mu_recomputed'])
        self.assertEqual(larger['rebuild']['previous_mu_horizon'],first['rebuild']['cofactor_horizon'])
        r,c=finite(alpha='1/257',primes=[2],N=2)
        changed=C.verify_filter_interval(r,c,M,context)
        self.assertGreater(changed['rebuild']['new_shifted_atoms'],0)

    def test_forged_interval_profile_or_source_authority_rejected(self):
        r,c=finite(primes=[2],N=3)
        for bad in ({'lower':'0','upper':'0'},
                {'lower':c['upper'],'upper':c['lower']},
                {'lower':c['lower'],'upper':c['upper'],'source_verified':True}):
            with self.assertRaises(ValueError):C.verify_filter_interval(r,bad,M)
        bad=copy.deepcopy(r);bad['alpha']='1/257'
        with self.assertRaises(ValueError):C.verify_filter_interval(bad,c,M)
        with self.assertRaises(ValueError):C.verify_filter_interval(r,c,M,{'source_verified':True})
        with self.assertRaises(ValueError):C.verify_filter_interval(r,c,M,C._Context())

    def test_complete_tail_signs_not_dropped(self):
        r,c=finite(primes=[3],cs=[2,-3,1],N=3)
        out=C.verify_filter_interval(r,c,M)
        self.assertEqual(out['rebuild']['cofactor_horizon'],12)
        self.assertEqual(out['rebuild']['maximum_shifted_index'],36)
        source=fixture().sources[(3,)]
        # Endpoint B(4N) is not a replacement for the complete signedfilter.
        denominator=(1<<32)*Q(r['alpha'])
        bad={'lower':str(Q(int(source.Bcenter[12])-int(source.Bdown[12]))/denominator),
             'upper':str(Q(int(source.Bcenter[12])+int(source.Bup[12]))/denominator)}
        with self.assertRaises(ValueError):C.verify_filter_interval(r,bad,M)

    def test_numeric_type_and_capacity_guards_before_rebuild(self):
        r,c=finite()
        for key,value in [('q',True),('q',2.0),('N',1),('N',True),('coefficients',[2,-3,True]),('coefficients',[1,0])]:
            bad=copy.deepcopy(r);bad[key]=value
            with self.assertRaises(ValueError):C.verify_filter_interval(bad,c,M)
        bad=copy.deepcopy(r);bad['N']=C.MAX_N
        with self.assertRaises(OverflowError):C.verify_filter_interval(bad,c,M)
        with self.assertRaises(OverflowError):C.verify_filter_interval(r,c,C.Meter(cap=0))
        with self.assertRaises(ValueError):C.verify_filter_interval(r,{'lower':0.0,'upper':1.0},M)

    def test_derived_output_capacity_is_separate_from_input(self):
        large=Q(1<<5000,7)
        self.assertEqual(C._output_rational(str(large),M),large)
        with self.assertRaises(ValueError):C._output_rational(str(Q(1<<17000)),M)

    def test_energy_complete_signed_crosses_and_fractional_decay(self):
        r,c=energy()
        out=C.verify_energy_recovery(r,c,M)
        self.assertEqual(out['base_upper'],'24300')
        self.assertEqual(Q(out['recovery']['constant']),Q(24300)+Q(257,32))
        self.assertTrue(out['target_domination_proved'])
        self.assertTrue(out['conditional_recovery_proved'])
        self.assertFalse(out['uniform_target_bound_proved'])
        self.assertEqual(out['recurrence_status'],'OPEN')

    def test_energy_negative_cross_cannot_be_omitted(self):
        r,c=energy()
        for mutation in ('drop','absolute','missingtarget'):
            bad=copy.deepcopy(c)
            if mutation=='drop':bad['matrix_terms'].pop(1)
            elif mutation=='absolute':bad['matrix_terms'][1]['coefficient']='2'
            else:bad['matrix_terms'][0]['coefficient']='1/2'
            with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)

    def test_energy_seed_and_recovery_cost_cannot_be_underpriced(self):
        r,c=energy()
        for section,key in ((None,'base_upper'),('recovery','constant')):
            bad=copy.deepcopy(c)
            if section is None:bad[key]='100'
            else:bad[section][key]='24300'
            with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)
        bad=copy.deepcopy(c);bad['recurrence']['minimum']=3
        with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)

    def test_both_children_open_quantifier_and_false_claims(self):
        r,c=energy()
        for children in ([0],[1],[0,1,2]):
            bad=copy.deepcopy(c);bad['recurrence']['children']=children
            with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)
        for field in ('uniform_drift_proved','uniform_target_bound_proved','RH_proved'):
            bad=copy.deepcopy(c);bad[field]=True
            with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)
        bad=copy.deepcopy(c);bad['recurrence']['status']='PAID'
        with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)

    def test_log_boundary_and_bounded_zero_C(self):
        r,c=energy('0','1/64')
        out=C.verify_energy_recovery(r,c,M)
        self.assertEqual(out['recovery'],{'kind':'logarithmic','constant':'24300',
            'log_coefficient':'1/64','logarithm_base':2})
        bad=copy.deepcopy(c);bad['recovery']['logarithm_base']='natural'
        with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)
        r,c=energy('1/257','0')
        self.assertEqual(C.verify_energy_recovery(r,c,M)['recovery']['constant'],'24300')

    def test_energy_bound_request_types_source_and_parameter_binding(self):
        r,c=energy()
        for key,value in [('alpha',0.2),('features',[[2],[],[3]]),
                ('features',[[],[2],[2]]),('lambda','-1'),('delta','-1/2'),
                ('C',True),('coefficients',[1,-2,True])]:
            bad=copy.deepcopy(r);bad[key]=value
            with self.assertRaises(ValueError):C.verify_energy_recovery(bad,c,M)
        bad=copy.deepcopy(c);bad['request']['C']='1/32'
        with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)
        bad=copy.deepcopy(c);bad['RH_proved']=0
        with self.assertRaises(ValueError):C.verify_energy_recovery(r,bad,M)

    def test_charge_only_pipeline_meter_and_no_hidden_source_reads(self):
        r,c=self.symbolic(primes=[2,3])
        self.assertTrue(C.verify_insertion(r,c,PIPE)['verified'])
        r,c=finite(primes=[2])
        self.assertTrue(C.verify_filter_interval(r,c,PIPE)['verified'])
        r,c=energy()
        self.assertTrue(C.verify_energy_recovery(r,c,PIPE)['verified'])
        self.assertFalse(hasattr(PIPE,'number'))

    def test_uniform_laplace_tail_source_bound(self):
        for primes in ([],[2],[3],[2,3],[2,3,5]):
            r,c=tail(primes,alpha='1/257')
            out=C.verify_tail_bound(r,c,M)
            self.assertTrue(out['tail_bound_proved'])
            self.assertFalse(out['complete_target_bound_proved'])
            self.assertFalse(out['source_values_evaluated'])
            self.assertTrue(out['full_energy_tail_crosses_must_be_retained'])
        r,c=tail([],2)
        self.assertEqual(C.verify_tail_bound(r,c,PIPE)['uniform_absolute_upper'],'9/2')
        r,c=tail([2,3],8)
        self.assertEqual(Q(C.verify_tail_bound(r,c,M)['uniform_absolute_upper']),Q(48,6**8))

    def test_tail_requires_integer_scope_full_source_and_open_core(self):
        r,c=tail([2,3])
        for key,value in [('integer_N_minimum',1),('product',2),
                ('uniform_absolute_upper','0'),('unpaid_core','none'),
                ('complete_target_bound_proved',True),('RH_proved',True),
                ('integrand','R^-t*sum_(d prime)mu(d)*d^-t*W(N/d)')]:
            bad=copy.deepcopy(c);bad[key]=value
            with self.assertRaises(ValueError):C.verify_tail_bound(r,bad,M)
        bad=copy.deepcopy(c);bad['filter']['coefficients']=[-2,1]
        with self.assertRaises(ValueError):C.verify_tail_bound(r,bad,M)
        for tau in (1,2.0,True,257):
            bad=copy.deepcopy(r);bad['tau']=tau
            with self.assertRaises(ValueError):C.verify_tail_bound(bad,c,M)

    def test_binary_floor_weight_and_empty_unit_gate(self):
        def W(y):return (4*y).__floor__()-3*(2*y).__floor__()+2*y.__floor__()
        for j in range(256):
            y=Q(j,32)
            self.assertLessEqual(abs(W(y)),1)
            if y.denominator==1:self.assertEqual(W(y),0)
        self.assertNotEqual(W(Q(3,8)),0)
        # Dropping the nonempty d1 cofactor term is not licensed by W(N)=0.
        self.assertNotEqual(W(Q(2,3)),0)
        _,_,_,subsets=C._parameters({'alpha':'1/5','primes':[3]},M)
        self.assertNotEqual(sum(sign*W(Q(2,e)) for _,e,sign in subsets),0)


if __name__=='__main__':unittest.main()
