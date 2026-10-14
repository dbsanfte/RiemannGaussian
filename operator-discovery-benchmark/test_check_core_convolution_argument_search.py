"""Synthetic signed identities, exact witness audits, and scope mutations."""
import copy
import math
import time
import unittest
from fractions import Fraction as Q
from unittest.mock import patch

import core_convolution_argument_search as PRODUCER
import check_core_convolution_argument_search as CHECK
from prime_bank_candidates import Meter

START=time.monotonic()
WORK=Meter(50000000,180)
DRIVER=None


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_convolution_argument_search operations='+str(WORK.operations)+
          ' elapsed_seconds='+str(time.monotonic()-START),flush=True)


def driver():
    global DRIVER
    if DRIVER is None:
        binding=dict(target_id='synthetic_complete_cubic',unit=1,transport='-e',original_channels=list(range(144)))
        parent=dict(schema='core-bound-argument-feedback-v1',bound_argument_search=dict(binding=binding,
            recovery=CHECK.TRUSTED.recovery(2,3)),
            cutoff_work_targets=[dict(p=2,m=3,sigma='9/20',theta='2/3',original_low_obligation=dict(
                parameters=dict(alpha='1/24'),required_upper=dict(U_power='12/5',log_degree=0),status='open'))],
            next_search_tasks=[dict(priority=0,target_id='actual_signed_core',status='open'),
                               dict(priority=1,target_id='inherited_failed_argument',status='open')],
            signed_source=dict(unit=1,drifts=['opposite signed drift'],transport='-e',
                               channels=list(range(144)),alternatives=['original retained route']),
            whole_signed_bound_proved=False,RH_proved=False)
        with patch.object(PRODUCER,'source_binding',return_value=binding):
            result=PRODUCER.search(parent,WORK)
        DRIVER=parent,binding,result
    return DRIVER


def convolution(a,b,n):
    out=[Q(0)]*n
    for d,v in enumerate(a,1):
        for k,w in enumerate(b,1):
            if d*k<=n:out[d*k-1]+=v*w;WORK.charge()
    return out


def polynomial_value(rows,states,n):
    out=[Q(0)]*n
    for row in rows:
        term=[Q(1)]+[Q(0)]*(n-1)
        for variable in row['key']:term=convolution(term,states[variable],n)
        out=[a+Q(row['value'])*b for a,b in zip(out,term)]
    return out


def integer_cutoff(n,exponent):
    q=Q(exponent);limit=0
    while (limit+1)**q.denominator<=n**q.numerator:limit+=1;WORK.charge()
    return limit


class IndependentConvolutionArgumentTests(unittest.TestCase):
    def test_floor_synthesis_is_a_complete_formal_primal_certificate(self):
        result=PRODUCER.synthesize_floor(WORK)
        self.assertTrue(CHECK.verify_floor(result,WORK)['verified'])
        self.assertEqual(len(result['basis']),18)
        coefficients={}
        for term in result['certificate']['solution']:
            basis=result['basis'][term['column']]
            key=(tuple(basis['denominator']),tuple(basis['reciprocal']))
            coefficients[key]=Q(term['coefficient'])
        self.assertEqual(coefficients,{((0,1),(1,0)):Q(-1),((1,1),(0,0)):Q(1)})
        for a in range(1,8):
            for d in range(1,7):
                for n in range(0,3*a*d+1):
                    centered=lambda m,x:Q(x%m,m)-Q(m-1,2*m)
                    target=centered(a,n//d)
                    reconstructed=sum((c*centered(a**den[0]*d**den[1],n)/a**rec[0]/d**rec[1]
                        for (den,rec),c in coefficients.items()),Q(0))
                    self.assertEqual(target,reconstructed);WORK.charge(10)

    def test_floor_basis_and_certificate_mutations_fail_closed(self):
        result=PRODUCER.synthesize_floor(WORK)
        for mutation in ('coefficient','unit','basis','degree','domain'):
            bad=copy.deepcopy(result)
            if mutation=='coefficient':bad['certificate']['solution'][0]['coefficient']='1'
            elif mutation=='unit':bad['source']=[row for row in bad['source'] if row['key'][0]!='one']
            elif mutation=='basis':bad['basis'].pop()
            elif mutation=='degree':bad['basis'][0]['reciprocal']=[3,0]
            else:bad['domain']='positive n except jumps'
            with self.assertRaises(ValueError):CHECK.verify_floor(bad,WORK)

    def test_signed_dilation_matches_period_and_complete_physical_short_head(self):
        floor=PRODUCER.synthesize_floor(WORK)
        for a,h in [([1,-1,-1],[1,Q(-1,2),2]),
                    ([Q(1,3),Q(-2,5),Q(4,7)],[Q(-3,2),0,1]),([1],[1,0,-1])]:
            compiled=PRODUCER.compile_dilation(a,h,floor,WORK)
            CHECK.verify_dilation(a,h,floor,compiled,WORK)
            v=list(map(Q,compiled['coefficients']));c=Q(compiled['c']);mean=Q(compiled['mean'])
            self.assertEqual(sum(Q(w,n) for n,w in enumerate(v,1)),0)
            def periodic(n):return sum(Q(w)*(Q(n%d,d)-Q(d-1,2*d)) for d,w in enumerate(a,1))
            for n in range(0,20):
                original=sum(Q(w)*periodic(n//d) for d,w in enumerate(h,1))
                collected=sum(w*(Q(n%d,d)-Q(d-1,2*d)) for d,w in enumerate(v,1))
                self.assertEqual(original,collected)
                physical=sum(Q(w)*(periodic(n//d) if n//d else 0) for d,w in enumerate(h,1))
                self.assertEqual(physical,collected-(1-mean)*sum(Q(w) for d,w in enumerate(h,1) if d>n))
                WORK.charge(20*len(v))

    def test_dilation_rejects_lost_harmonic_null_mean_unit_and_sign(self):
        floor=PRODUCER.synthesize_floor(WORK)
        a,h=[1,-1,-1],[1,-1,2]
        result=PRODUCER.compile_dilation(a,h,floor,WORK)
        for field,value in [('c','0'),('mean','0'),('harmonic_null','1'),('short_head','discarded')]:
            bad=copy.deepcopy(result);bad[field]=value
            with self.assertRaises(ValueError):CHECK.verify_dilation(a,h,floor,bad,WORK)
        bad=copy.deepcopy(result);bad['coefficients'][0]=str(Q(bad['coefficients'][0])+1)
        with self.assertRaises(ValueError):CHECK.verify_dilation(a,h,floor,bad,WORK)

    def test_exact_signed_bilinear_gram_agrees_with_discrete_period(self):
        for v,w in [([1,-1,2],[2,1,-1]),([Q(2,3),Q(-4,5)],[1,0,Q(3,7),-2]),
                    ([1],[-1]),([0,1],[0,-1])]:
            gram=PRODUCER.exact_gram(v,w,WORK)
            CHECK.verify_gram(v,w,gram,WORK)
            period=math.lcm(*range(1,max(len(v),len(w))+1))
            series=lambda a,n:sum(Q(c)*(Q(n%d,d)-Q(d-1,2*d)) for d,c in enumerate(a,1))
            exact=sum(series(v,n)*series(w,n) for n in range(period))/period
            self.assertEqual(Q(gram),exact);WORK.charge(20*period*(len(v)+len(w)))
        v=[Q(1),Q(-2)] # harmonic null
        positive=sum(a*b*Q(math.gcd(n,m)**2,12*n*m)
                     for n,a in enumerate(v,1) for m,b in enumerate(v,1))
        self.assertEqual(Q(PRODUCER.exact_gram(v,v,WORK)),positive)
        v=[1,1]
        positive=sum(Q(a*b*math.gcd(n,m)**2,12*n*m)
                     for n,a in enumerate(v,1) for m,b in enumerate(v,1))
        with self.assertRaises(ValueError):CHECK.verify_gram(v,v,str(positive),WORK)

    def test_divisor_constants_and_cutoff_log_conversion_are_exact(self):
        actual=PRODUCER.divisor_arguments(2,0,'mobius',WORK)
        generic=PRODUCER.divisor_arguments(2,0,'bounded',WORK)
        CHECK.verify_divisor_arguments(actual,WORK);CHECK.verify_divisor_arguments(generic,WORK)
        self.assertEqual(CHECK.exponential_constant(6),1957)
        self.assertEqual(actual['period_bound'],CHECK.env(Q(5871,4)*3**8,3,logs=8))
        self.assertEqual(generic['period_bound']['U_power'],'3')
        self.assertEqual(generic['period_bound']['log_degree'],10)
        bad=copy.deepcopy(actual);bad['candidates'][-1]['bound']['constant']='5871/4'
        with self.assertRaises(ValueError):CHECK.verify_divisor_arguments(bad,WORK)
        bad=copy.deepcopy(generic);bad['candidates'][-1]['amplitude_squared_log_degree']=0
        with self.assertRaises(ValueError):CHECK.verify_divisor_arguments(bad,WORK)

    def test_generic_depth_fractional_decay_and_critical_abel_logs(self):
        for p in (0,1,3):
            for decay in ('0','1/6','1/2','2/3','1','3/2'):
                for profile in ('bounded','mobius'):
                    result=PRODUCER.divisor_arguments(p,decay,profile,WORK)
                    CHECK.verify_divisor_arguments(result,WORK)
                    self.assertEqual(result['support_U_power'],p+1)
        critical=PRODUCER.divisor_arguments(2,'1/2','mobius',WORK)
        abel=next(row for row in critical['candidates'] if row['rule']=='weighted_Abel')
        self.assertEqual(abel['bound']['log_degree'],10)
        self.assertEqual(critical['period_bound']['log_degree'],9)
        bad=copy.deepcopy(critical);next(row for row in bad['candidates'] if row['rule']=='weighted_Abel')['bound']['log_degree']=0
        with self.assertRaises(ValueError):CHECK.verify_divisor_arguments(bad,WORK)

    def test_divisor_domain_all_routes_and_spacing_debt_are_required(self):
        result=PRODUCER.divisor_arguments(2,0,'mobius',WORK)
        for mutation in ('missing','selected','domain','spacing','decay','profile','depth'):
            bad=copy.deepcopy(result)
            if mutation=='missing':bad['candidates'].pop(0)
            elif mutation=='selected':bad['selected']=0
            elif mutation=='domain':bad['window_domain']='physical prefix on all n including zero'
            elif mutation=='spacing':bad['window_bound'][-1]['U_power']='3'
            elif mutation=='decay':bad['decay']='-1'
            elif mutation=='profile':bad['profile']='unlicensed'
            else:bad['p']=True
            with self.assertRaises(ValueError):CHECK.verify_divisor_arguments(bad,WORK)

    def test_divisor_algebra_prerequisites_include_repeated_prime_powers(self):
        def divisor(k,n):
            remaining=n;out=1;prime=2
            while prime<=remaining:
                exponent=0
                while remaining%prime==0:exponent+=1;remaining//=prime
                if exponent:out*=math.comb(exponent+k-1,k-1)
                prime+=1
            return out
        for k in range(1,5):
            for a in range(1,15):
                for b in range(1,15):
                    self.assertLessEqual(divisor(k,a*b),divisor(k,a)*divisor(k,b))
                    self.assertLessEqual(divisor(k,a*b)**2,divisor(k*k,a*b))
                    WORK.charge(100)

    def test_hyperbola_primal_dual_optimum_and_mean_are_verified(self):
        for alpha,beta,m in [('1/3','1/2',3),('1/6','1/2',3),('2/5','2/3',3),('1/2','1/2',2),('1/3','1/2',4)]:
            result=PRODUCER.hyperbola_synthesize(alpha,beta,WORK,m)
            report=CHECK.verify_geometry(result,WORK)
            self.assertTrue(report['verified'])
            self.assertTrue(any(row['key']==['C']*m for row in result['source']))
            self.assertEqual(result['selected'],min(i for i,t in enumerate(result['trials']) if t['certificate']['status']=='feasible'))
            self.assertTrue(all(Q(c['lower_support_power'])>=1 for c in result['support_certificates']))
        result=PRODUCER.hyperbola_synthesize('1/3','1/2',WORK)
        self.assertEqual(result['trials'][result['selected']]['support_threshold'],'5/6')

    def test_hyperbola_identity_for_arbitrary_signed_sequences_all_small_prefixes(self):
        for alpha,beta in [('1/3','1/2'),('1/6','1/2'),('1/2','2/3')]:
            g=PRODUCER.hyperbola_synthesize(alpha,beta,WORK)
            CHECK.verify_geometry(g,WORK)
            for n in (1,2,5,12,30):
                e=[Q((i%4)-2,3) for i in range(1,n+1)];C=Q(-5,7)
                t=integer_cutoff(n,alpha);r=integer_cutoff(n,beta)
                states=dict(C=[C]+[Q(0)]*(n-1),e=e,t=e[:t]+[Q(0)]*(n-t),r=e[:r]+[Q(0)]*(n-r))
                original=polynomial_value(g['source'],states,n)
                h=polynomial_value(g['one_e_coefficient'],states,n)
                z=polynomial_value(g['finite_head'],states,n)
                reconstructed=[a+b for a,b in zip(convolution(h,e,n),z)]
                self.assertEqual(original,reconstructed)
                self.assertEqual(polynomial_value(g['vanishing_remainder'],states,n),[Q(0)]*n)
                for v in range(n):self.assertEqual(sum(original[:v+1]),sum(reconstructed[:v+1]))

    def test_dual_must_annihilate_all_allowed_columns_and_ideal_rows(self):
        g=PRODUCER.hyperbola_synthesize('1/3','1/2',WORK)
        trial=next(i for i,t in enumerate(g['trials']) if t['certificate']['status']=='infeasible')
        for mutation in ('dual','contradiction','allowed','missing'):
            bad=copy.deepcopy(g);t=bad['trials'][trial]
            if mutation=='dual':t['certificate']['dual'][0]['value']=str(Q(t['certificate']['dual'][0]['value'])+1)
            elif mutation=='contradiction':t['certificate']['contradiction']='0'
            elif mutation=='allowed':t['allowed'].pop()
            else:t['certificate']['dual'].pop()
            with self.assertRaises(ValueError):CHECK.verify_geometry(bad,WORK)

    def test_primal_missing_mean_or_finite_head_and_false_domains_rejected(self):
        g=PRODUCER.hyperbola_synthesize('1/3','1/2',WORK)
        for mutation in ('source','primal','finite','support','threshold','moving','global','paid','mean'):
            bad=copy.deepcopy(g)
            if mutation=='source':bad['source'].pop(0)
            elif mutation=='primal':bad['trials'][bad['selected']]['certificate']['solution'].pop()
            elif mutation=='finite':bad['finite_head'].pop()
            elif mutation=='support':bad['support_certificates'][0]['lower_support_power']='0'
            elif mutation=='threshold':bad['trials'].pop(0)
            elif mutation=='moving':bad['moving_cutoffs_allowed_in_period_rule']=True
            elif mutation=='global':bad['global_Dirichlet_series_identity']=True
            elif mutation=='paid':bad['head_or_cross_paid']=True
            else:bad['one_e_coefficient']=[row for row in bad['one_e_coefficient'] if 'C' not in row['key']]
            with self.assertRaises(ValueError):CHECK.verify_geometry(bad,WORK)

    def test_systematic_geometry_grid_is_complete_not_a_nominated_winner(self):
        grid=CHECK.geometry_grid(6)
        self.assertEqual(len(grid),51)
        self.assertIn(('1/6','1/2'),grid)
        self.assertEqual(max(Q(b) for a,b in grid),Q(5,6))
        for a,b in grid:
            self.assertLessEqual(Q(a),Q(b));self.assertGreaterEqual(2*Q(b),1)
            self.assertLess(Q(b),1)
            self.assertLessEqual(Q(a).denominator,6);self.assertLessEqual(Q(b).denominator,6)
        self.assertEqual(grid,PRODUCER.geometry_grid(6))
        for limit in (True,1,13):
            with self.assertRaises(ValueError):CHECK.geometry_grid(limit)

    def test_geometry_cost_retains_unit_amplitude_spacing_and_no_lower_claim(self):
        g=PRODUCER.hyperbola_synthesize('1/3','1/2',WORK)
        cost=CHECK.geometry_cost(g,2,'1/24',WORK)
        self.assertEqual(cost,PRODUCER.geometry_cost(g,2,'1/24'))
        self.assertEqual(cost['coefficient_U_power'],2)
        self.assertEqual(cost['denominator'],dict(U_power=3,N_power='5/6'))
        self.assertEqual(cost['normalized_spacing_cost_power'],'25/24')
        self.assertEqual(cost['optimistic_zero_amplitude_cost_power'],'7/8')
        self.assertFalse(cost['actual_arithmetic_lower_bound'])
        self.assertFalse(cost['finite_head_and_cross_paid'])

    def test_prime_count_obstruction_is_only_a_full_period_lower_statement(self):
        for p in range(7):
            record=PRODUCER.fresh_prime_obstruction(p)
            CHECK.equal(record,CHECK.prime_obstruction(p),WORK,'scoped prime obstruction')
            self.assertEqual(Q(record['lower_coefficient']),Q(math.factorial(p+1)**2,24))
            self.assertFalse(record['finite_window_lower_bound'])
        # Synthetic short weights at selected large primes calibrate the exact conductor.
        u=11;primes=[7,11];a=[Q(1)]+[Q(0)]*(u-1)
        for p in primes:a[p-1]=-1
        a2=convolution(a,a,u*u);c=sum(Q(v,d) for d,v in enumerate(a,1))
        v=a2[:]
        for d,av in enumerate(a,1):v[d-1]-=c*av
        r=primes[0]*primes[1]
        self.assertEqual(v[r-1],2)
        self.assertEqual(sum(v[n-1]*Q(r,n) for n in range(r,len(v)+1,r)),2)

    def test_source_wrapper_and_feedback_keep_full_signed_state_open(self):
        parent,binding,result=driver();artifact='synthetic/proof_search.json'
        with patch.object(CHECK,'source_binding',return_value=binding):
            self.assertTrue(CHECK.verify_search(parent,result,WORK)['verified'])
            out=PRODUCER.feedback(parent,result,artifact)
            self.assertTrue(CHECK.verify_feedback(parent,result,out,artifact,WORK)['verified'])
            for mutation in ('source','mean','cross','ordinary','period','cost','grid','selection'):
                bad=copy.deepcopy(result)
                if mutation=='source':bad['complete_source']='only periodic branch'
                elif mutation=='mean':bad['source_recovery']['mean']='bounded zero mean'
                elif mutation=='cross':bad['source_recovery']['joined_covariance']='sum of separate squares'
                elif mutation=='ordinary':bad['source_recovery']['ordinary_theta_moment_convergence_assumed']=True
                elif mutation=='period':bad['period_obstruction']['full_core_refuted']=True
                elif mutation=='cost':bad['geometry_costs'][0]['coefficient_U_power']=0
                elif mutation=='grid':bad['geometries'].pop()
                else:bad['selected_geometry']=(bad['selected_geometry']+1)%len(bad['geometries'])
                with self.assertRaises(ValueError):CHECK.verify_search(parent,bad,WORK)
            for mutation in ('unit','drift','binding','task','closed'):
                bad=copy.deepcopy(out)
                if mutation=='unit':bad['signed_source']['unit']=0
                elif mutation=='drift':bad['signed_source']['drifts']=[]
                elif mutation=='binding':bad['signed_source']['channels'].pop()
                elif mutation=='task':bad['next_search_tasks'].pop()
                else:bad['whole_signed_bound_proved']=True
                with self.assertRaises(ValueError):CHECK.verify_feedback(parent,result,bad,artifact,WORK)

    def test_source_binding_and_charge_only_rational_size_guard(self):
        parent,binding,result=driver()
        with patch.object(CHECK.TRUSTED,'source_binding',return_value=binding) as old:
            self.assertEqual(CHECK.source_binding(parent,WORK),binding)
            self.assertEqual(old.call_args.args[0]['schema'],'core-signed-primitive-feedback-v1')
            bad=copy.deepcopy(parent);bad['bound_argument_search']['binding']=dict(binding,unit=0)
            with self.assertRaises(ValueError):CHECK.source_binding(bad,WORK)
        self.assertFalse(hasattr(WORK,'number'))
        for q in (True,1<<4096,Q(1,1<<4096)):
            with self.assertRaises(ValueError):CHECK.number(q,WORK)


if __name__=='__main__':unittest.main()
