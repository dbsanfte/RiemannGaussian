"""Independent exact fixtures and high-precision generic integral checks."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from math import comb
import resource
import sys
import time
import unittest
from flint import arb,ctx

import check_core_joint_power_search as CHECK
from potential_candidate_language import Meter

START=time.monotonic()
WORK=Meter(50000000,deadline=START+180,max_cells=1000000)
ctx.prec=192


def real(q):
    q=Q(q);WORK.charge(100)
    return arb(q.numerator)/q.denominator


def power(x,q):
    q=Q(q);WORK.charge(200)
    return (x**q.numerator).root(q.denominator)


def mass(f):
    WORK.charge(2*len(f));return sum(map(abs,f),Q(0))


def moment(f,theta):
    WORK.charge(10*len(f))
    return sum((real(v)/power(arb(d),theta) for d,v in enumerate(f) if d and v),arb(0))


def finite_convolution(f,g):
    # Full support, never truncated at the prefix horizon.
    H=(len(f)-1)*(len(g)-1);out=[Q(0)]*(H+1)
    for d,v in enumerate(f[1:],1):
        for e,w in enumerate(g[1:],1):out[d*e]+=v*w;WORK.charge(4)
    return out


def kernel_prefix(t,a):
    t=Q(t);return sum((1/power(arb(n),a) for n in range(1,t.numerator//t.denominator+1)),arb(0))


def centered_prefix(f,n,a):
    theta=1-a
    direct=sum((real(v)*kernel_prefix(Q(n,d),a) for d,v in enumerate(f) if d and v),arb(0))
    return direct-moment(f,theta)*power(arb(n),theta)/real(theta)


def fixture():
    # Two hand-derived opposite signed finite kernels. Joint cancellation is
    # exact; a coefficientwise drift bound would miss it completely.
    row=dict(id=1,alpha='1/6',gamma='1/6',cases=[])
    terms=[];refs=[];eligible=[]
    old=dict(constant='46656',power='2/3',log_degree=0,uniform_constant=None)
    for i,(name,scalar) in enumerate([('positive','beta'),('negative','-beta')]):
        mode=dict(name=name,coefficient=scalar,p=2,q=0,positive_shift='1/3')
        row['cases'].append(dict(mode=mode,program=dict(terms=[dict(a=0,b=0,coefficient='1')])))
        key=dict(mode=name,a=0,b=0);ref=dict(source_key=key,depth=0,piece=0);refs.append(ref)
        piece=dict(expression=['A','A','K'],coefficient='1',energy=deepcopy(old),prefix_proof=4)
        terms.append(dict(key=key,source_scalar=scalar,inverse_coefficient='1',selected_depth=0,
                          alternatives=[dict(depth=0,pieces=[piece])]))
        eligible.append(dict(id=i,reference=ref,source_scalar=scalar,coefficient='1',factors=['A','A'],
                             kernel_shift='1/3',old_energy=deepcopy(old)))
    nodes=[
        dict(id=0,expression=['A'],norm='critical',constant='2',power='1/12',log_degree=0,proof_size=1,rule='atom',atom_rule='A_critical',children=[]),
        dict(id=1,expression=['K'],norm='critical',constant='6',power='1/6',log_degree=0,proof_size=1,rule='atom',atom_rule='K_critical',children=[]),
        dict(id=2,expression=['A','A'],norm='critical',constant='4',power='1/6',log_degree=0,proof_size=3,rule='critical_convolution',children=[0,0]),
        dict(id=3,expression=['A','A','K'],norm='critical',constant='24',power='1/3',log_degree=0,proof_size=5,rule='critical_convolution',children=[2,1]),
        dict(id=4,expression=['A','A','K'],norm='prefix',constant='24',power='5/6',log_degree=0,proof_size=6,rule='critical_to_prefix',children=[3])]
    prefix=dict(geometry_id=1,alpha='1/6',gamma='1/6',terms=terms,nodes=nodes)
    profiles=[]
    for theta in ['1/6','1/3','1/2','2/3','5/6','1']:
        valid=theta=='2/3'
        profiles.append(dict(kernel_shift='1/3',theta=theta,status='supported' if valid else 'unmatched_power_profile',
            leading_power='2/3',leading_coefficient='3/2',solved_multiplier='3/2' if valid else None,
            universal_remainder_constant='3/2' if valid else None))
    alternatives=[]
    for mask in range(4):
        chosen=[i for i in range(2) if mask&(1<<i)];unchanged=[i for i in range(2) if i not in chosen]
        remainders=[dict(eligible_id=i,theta='2/3',definition='signed K*h minus its complete signed moment/theta times J_theta',
            prefix_bound=dict(constant='27/4',power='1/3',log_degree=0),
            energy=dict(constant='729/4',power='-1/3',log_degree=0,uniform_constant='729/4')) for i in chosen]
        drifts=[]
        if mask in (1,2):
            drifts=[dict(theta='2/3',polynomial=[dict(powers=[2,0,0,0],coefficient='27/4' if mask==1 else '-27/4')],
                prefix_bound=dict(constant='243/4',power='7/9',log_degree=0),
                energy=dict(constant='59049/4',power='5/9',log_degree=0,uniform_constant=None))]
        score=['2/3',0,2,0,0] if mask==0 else ['2/3',0,2,1,mask] if mask in (1,2) else ['0',0,0,2,3]
        alternatives.append(dict(mask=mask,status='exact_decomposition_with_bound_certificates',centered_ids=chosen,
            unchanged_ids=unchanged,remainders=remainders,joint_drifts=drifts,score=score,
            comparison_scope='eligible finite-factor subsum only; other full-core pieces are unchanged',whole_signed_bound_proved=False))
    result=dict(schema='core-joint-power-search-v1',geometry_id=1,alpha='1/6',gamma='1/6',remaining_refs=refs,
        eligible=eligible,profile_trials=profiles,alternatives=alternatives,selected_mask=3,
        moment_variable_order=['m_theta_A','m_theta_B','c_U','R_u'],
        operator_definition='J_theta(n)=n^theta-(n-1)^theta; complete finite moments multiply under Dirichlet convolution',
        statistics=dict(eligible_pieces=2,profile_trials=6,rejected_profiles=5,subsets=4,selected_centered=2,
                        selected_joint_drifts=0,selected_paid_remainders=2),whole_signed_bound_proved=False,RH_proved=False)
    return row,prefix,refs,result


class JointPowerCheckerTests(unittest.TestCase):
    def test_all_real_remainder_fractional_and_t_below_one(self):
        for a in map(Q,['0','1/6','1/3','1/2','2/3','5/6']):
            theta=1-a
            for t in map(Q,['0','1/100','1/3','9/10','1','7/4','2','17/3','11']):
                remainder=kernel_prefix(t,a)-power(real(t),theta)/real(theta)
                lower=-1/real(theta)
                self.assertTrue(remainder>=lower or (remainder-lower).contains(0))
                self.assertTrue(remainder<=0 or remainder.contains(0))

    def test_arbitrary_signed_remainders_full_moment(self):
        for seed in range(1,9):
            f=[Q(0)]+[Q((seed*d)%9-4,d%4+1) for d in range(1,10)]
            for a in map(Q,['0','1/3','2/3','5/6']):
                bound=real(mass(f)/(1-a))
                for n in (1,2,4,7,11):
                    value=centered_prefix(f,n,a)
                    self.assertTrue(value>=-bound or (value+bound).contains(0))
                    self.assertTrue(value<=bound or (value-bound).contains(0))

    def test_moment_beyond_n_required(self):
        f=[Q(0)]*11;f[10]=Q(-7,3);theta=Q(2,3)
        correct=centered_prefix(f,1,1-theta)
        self.assertFalse(correct.contains(0))
        self.assertTrue((correct+moment(f,theta)/real(theta)).contains(0))
        # A truncated moment would incorrectly declare the entire prefix zero.
        self.assertTrue(moment(f[:2],theta).contains(0))

    def test_complete_convolution_moment_beyond_N(self):
        f=[Q(0),Q(1),Q(-2),Q(3,4),Q(2)]
        g=[Q(0),Q(-1,2),Q(2),Q(0),Q(3,5)]
        fg=finite_convolution(f,g)
        self.assertEqual(len(fg),17)
        for theta in CHECK.PROFILES:
            self.assertTrue((moment(fg,theta)-moment(f,theta)*moment(g,theta)).contains(0))
            self.assertFalse((moment(fg[:5],theta)-moment(f,theta)*moment(g,theta)).contains(0))

    def test_joint_signed_source_and_drift_recombination(self):
        A=[Q(0),Q(1),Q(-2),Q(1,3)];B=[Q(0),Q(1),Q(2,5)]
        terms=[(Q(9,2),finite_convolution(A,A)),(Q(-9,2),finite_convolution(A,B)),
               (Q(-7,4),B)]
        a=Q(1,3);theta=1-a
        drift=sum((real(c)*moment(h,theta)/real(theta) for c,h in terms),arb(0))
        for n in (1,2,5,11):
            old=sum((real(c)*sum((real(v)*kernel_prefix(Q(n,d),a) for d,v in enumerate(h) if d and v),arb(0))
                     for c,h in terms),arb(0))
            new=sum((real(c)*centered_prefix(h,n,a) for c,h in terms),arb(0))+drift*power(arb(n),theta)
            self.assertTrue((new-old).contains(0))

    def test_finite_moment_bounds_all_three_regimes(self):
        self.assertEqual(CHECK._finite_moment_bound(Q(2,3),Q(1,6)),(Q(3),Q(1,18),0))
        self.assertEqual(CHECK._finite_moment_bound(Q(1),Q(5,6)),(Q(1),Q(0),1))
        self.assertEqual(CHECK._finite_moment_bound(Q(4,3),Q(1,6)),(Q(4),Q(0),0))
        for s in map(Q,['0','1/3','1','4/3','2']):
            for r,U,N in [(Q(1,2),4,16),(Q(1,3),3,27)]:
                c,e,k=CHECK._finite_moment_bound(s,r)
                actual=sum((1/power(arb(d),s) for d in range(1,U+1)),arb(0))
                bound=real(c)*power(arb(N),e)*(1+arb(N).log())**k
                self.assertTrue(actual<=bound or (actual-bound).contains(0))

    def test_Abel_full_variation_and_channel_squares(self):
        construction=dict(channels=[dict(eta='1/2',polynomial=['1','-2','3']),dict(eta='0',polynomial=['-2'])])
        self.assertEqual(CHECK._abel(construction,WORK),488)
        construction['channels'][0]['eta']='-1/2'
        with self.assertRaises(ValueError):CHECK._abel(construction,WORK)


    def test_paper_signed_cancellation_certificate_and_all_subsets(self):
        row,prefix,refs,result=fixture()
        verified=CHECK.verify_search(row,prefix,refs,result,WORK)
        self.assertEqual(verified['selected_mask'],3)
        self.assertEqual(result['alternatives'][3]['joint_drifts'],[])

    def test_missing_current_piece_subset_or_profile_rejected(self):
        row,prefix,refs,result=fixture()
        with self.assertRaises(ValueError):CHECK.verify_search(row,prefix,refs[:-1],result,WORK)
        for field in ('eligible','profile_trials','alternatives'):
            bad=deepcopy(result);bad[field].pop()
            with self.subTest(field=field),self.assertRaises(ValueError):CHECK.verify_search(row,prefix,refs,bad,WORK)
        bad=deepcopy(result);bad['selected_mask']=1
        with self.assertRaises(ValueError):CHECK.verify_search(row,prefix,refs,bad,WORK)

    def test_corrupt_prior_source_row_paid_flag_or_proof_rejected(self):
        row,prefix,refs,result=fixture()
        for kind in ('row','paid','proof','coefficient'):
            bad=deepcopy(prefix)
            if kind=='row':bad['terms'].pop()
            if kind=='paid':bad['terms'][0]['alternatives'][0]['pieces'][0]['energy']['uniform_constant']='1'
            if kind=='proof':bad['nodes'][-1]['power']='1/2'
            if kind=='coefficient':bad['terms'][0]['alternatives'][0]['pieces'][0]['coefficient']='-1'
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify_search(row,bad,refs,result,WORK)

    def test_formal_Ru_and_c_signs_are_retained(self):
        powers,coefficient=CHECK._signed_moment(dict(coefficient='-2',source_scalar='-R_u',factors=['A','B','C']),WORK)
        self.assertEqual(powers,(1,1,1,1))
        self.assertEqual(coefficient,2)

    def test_profile_coefficient_sign_moment_and_payment_tamper(self):
        row,prefix,refs,result=fixture()
        for kind in ('profile','sign','powers','remainder','zero_drift','scope','closed'):
            bad=deepcopy(result)
            if kind=='profile':bad['profile_trials'][3]['solved_multiplier']='1'
            if kind=='sign':bad['alternatives'][2]['joint_drifts'][0]['polynomial'][0]['coefficient']='27/4'
            if kind=='powers':bad['alternatives'][1]['joint_drifts'][0]['polynomial'][0]['powers']=[1,0,0,0]
            if kind=='remainder':bad['alternatives'][3]['remainders'][0]['energy']['uniform_constant']='1'
            if kind=='zero_drift':bad['alternatives'][3]['joint_drifts']=deepcopy(result['alternatives'][1]['joint_drifts'])
            if kind=='scope':bad['alternatives'][0]['comparison_scope']='full core bounded'
            if kind=='closed':bad['whole_signed_bound_proved']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify_search(row,prefix,refs,bad,WORK)

    def test_unsupported_profile_is_retained_and_not_disproof(self):
        _,_,_,result=fixture()
        eligible=deepcopy(result['eligible'])
        for piece in eligible:piece['kernel_shift']='1/4'
        profiles=CHECK._profile_certificates(eligible,WORK)
        self.assertEqual(len(profiles),6)
        self.assertTrue(all(p['status']=='unmatched_power_profile' for p in profiles))
        self.assertTrue(all(p['leading_power']=='3/4' and p['solved_multiplier'] is None for p in profiles))
        for mask in range(1,4):
            alternative=dict(mask=mask,status='unsupported_power_profile')
            self.assertIsNone(CHECK._audit_alternative(mask,eligible,profiles,Q(1,6),Q(1,6),alternative,WORK))

    def test_lower_power_logs_and_joint_Ru_polynomial(self):
        old=dict(constant='1',power='1',log_degree=0,uniform_constant=None)
        eligible=[dict(id=0,kernel_shift='2/3',source_scalar='beta',coefficient='1',factors=['A'],old_energy=old),
                  dict(id=1,kernel_shift='2/3',source_scalar='-R_u',coefficient='1',factors=['B'],old_energy=old)]
        profiles=CHECK._profile_certificates(eligible,WORK)
        remainder_A=dict(eligible_id=0,theta='1/3',definition='signed K*h minus its complete signed moment/theta times J_theta',
            prefix_bound=dict(constant='27/2',power='1/6',log_degree=0),
            energy=dict(constant='729',power='-2/3',log_degree=0,uniform_constant='729'))
        remainder_B=dict(eligible_id=1,theta='1/3',definition='signed K*h minus its complete signed moment/theta times J_theta',
            prefix_bound=dict(constant='45',power='1/18',log_degree=0),
            energy=dict(constant='8100',power='-8/9',log_degree=0,uniform_constant='8100'))
        drift=dict(theta='1/3',polynomial=[dict(powers=[0,1,0,1],coefficient='-3'),dict(powers=[1,0,0,0],coefficient='27/2')],
            prefix_bound=dict(constant='141/4',power='4/9',log_degree=1),
            energy=dict(constant='19881/4',power='-1/9',log_degree=2,uniform_constant='6461325'))
        alternative=dict(mask=3,status='exact_decomposition_with_bound_certificates',centered_ids=[0,1],unchanged_ids=[],
            remainders=[remainder_A,remainder_B],joint_drifts=[drift],score=['0',0,0,2,3],
            comparison_scope='eligible finite-factor subsum only; other full-core pieces are unchanged',whole_signed_bound_proved=False)
        self.assertEqual(CHECK._audit_alternative(3,eligible,profiles,Q(1,6),Q(1,6),alternative,WORK)[0],0)
        alternative['joint_drifts'][0]['prefix_bound']['log_degree']=0
        with self.assertRaises(ValueError):CHECK._audit_alternative(3,eligible,profiles,Q(1,6),Q(1,6),alternative,WORK)

    def test_reduction_complete_payment_and_transport(self):
        _,_,refs,result=fixture()
        construction=dict(channels=[dict(eta='1/2',polynomial=['1','-2','3']),dict(eta='0',polynomial=['-2'])])
        parent=dict(parent_obligation_id='synthetic',geometry_id=1,remaining_signed_pieces=refs,channel_abel_constant='488',
            transport_error_retained=True,all_remaining_crosses_retained=True,whole_signed_bound_proved=False,
            original_fixed_recurrence_discharged=False,goal=dict(p='3',status='open',same_finite_constant=True))
        reduction=dict(schema='core-joint-power-reduction-v1',parent_obligation_id='synthetic',geometry_id=1,selected_mask=3,
            newly_paid=[dict(kind='remainder',eligible_id=i,uniform_energy_constant='729/4') for i in range(2)],
            remaining_source_refs=[],remaining_centered_remainders=[],remaining_joint_drifts=[],channel_abel_constant='488',
            combined_paid_constant='355752',
            exact_split='Z_old=P_new+Z_new; Z_new retains all untouched pieces, unpaid centered remainders, complete joint drifts, and -e where e=f-g',
            recovery='S_old<=2*S_new+2*C_new; S_new<=2*S_old+2*C_new',
            goal=dict(expression='S_new(X)<=C*(1+log2X)^p for every dyadicX>=1',p='3',status='open',same_finite_constant=True),
            full_finite_moments_retained=True,all_remaining_crosses_retained=True,transport_error_retained=True,
            original_fixed_recurrence_discharged=False,whole_signed_bound_proved=False,RH_proved=False)
        self.assertEqual(CHECK.verify_reduction(parent,construction,result,reduction,WORK)['newly_paid'],2)
        for field,value in [('transport_error_retained',False),('full_finite_moments_retained',False),
                            ('combined_paid_constant','177876'),('remaining_centered_remainders',[0]),('newly_paid',[])]:
            bad=deepcopy(reduction);bad[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):CHECK.verify_reduction(parent,construction,result,bad,WORK)
        bad_parent=deepcopy(parent);bad_parent['goal']['p']='-1'
        with self.assertRaises(ValueError):CHECK.verify_reduction(bad_parent,construction,result,reduction,WORK)

    def test_strict_rationals_and_resource_caps(self):
        for text in ('2/4','01','+1','-0','1.0','1/0',True):
            with self.subTest(text=text),self.assertRaises(ValueError):CHECK._rational(text,WORK)
        with self.assertRaises(OverflowError):CHECK._rational('1',Meter(1))
        with self.assertRaises(OverflowError):CHECK._rational('256',Meter(100,max_bits=8))


def tearDownModule():
    print(f'SYNTHETIC_WORK module=test_check_core_joint_power_search operations={WORK.operations} elapsed_seconds={time.monotonic()-START:.6f}')


if __name__=='__main__':
    resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024))
    if len(sys.argv)>1:suite=unittest.defaultTestLoader.loadTestsFromNames(['__main__.JointPowerCheckerTests.'+n for n in sys.argv[1:]])
    else:suite=unittest.defaultTestLoader.loadTestsFromTestCase(JointPowerCheckerTests)
    outcome=unittest.TextTestRunner(verbosity=2).run(suite)
    run=dict(returncode=0 if outcome.wasSuccessful() else 1,operations=WORK.operations,tests=outcome.testsRun,
        elapsed_seconds=time.monotonic()-START,failures=len(outcome.failures),errors=len(outcome.errors),
        failure_details=[dict(test=str(t),traceback=trace) for t,trace in outcome.failures+outcome.errors])
    try:
        with open('core_joint_power_checker_development.json') as source:previous=json.load(source)
    except FileNotFoundError:previous=dict(runs=[])
    runs=previous['runs']+[run]
    receipt=dict(schema='core-joint-power-checker-development-v1',runs=runs,operations=sum(r['operations'] for r in runs),
        success=outcome.wasSuccessful(),peak_live_cells=WORK.peak_live_cells,maximum_rational_bits=WORK.maximum_rational_bits,
        memory_limit_bytes=512*1024*1024,operation_limit=50000000,elapsed_limit_seconds=180,
        no_source_observations=True,edits_stopped=outcome.wasSuccessful())
    with open('core_joint_power_checker_development.json','w') as output:json.dump(receipt,output,indent=2);output.write('\n')
    raise SystemExit(run['returncode'])
