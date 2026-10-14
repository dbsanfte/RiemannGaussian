"""New semantic, bound and adaptive-search tests on unrelated polynomials."""
from fractions import Fraction as Q
from math import prod
from types import SimpleNamespace
from unittest.mock import patch
import unittest
import mobius_divisor_correction_070 as S

METER = S.Meter(cap=300_000_000_000)


def prefixes(U):
    mu = [0]*(U+1); mu[1] = 1
    for n in range(2, U+1):
        mu[n] = -sum(mu[d] for d in range(1, n) if n % d == 0)
    out = [0]*(U+1)
    for n in range(1, U+1): out[n] = out[n-1]+mu[n]
    return out


def evaluate(terms, values):
    return sum(t['numerator']*prod(values[i] for i in t['indices']) for t in terms)


def source(poly, U=7, degree=3, den=1):
    return dict(degree=degree, U=U, denominator=den, polynomial=S.pack(poly))


def bound(cert):
    return Q(cert['baseline_unconditional_bound']) if cert['selected_round'] == -1 else Q(cert['rounds'][cert['selected_round']]['primal_upper'])


class DivisorCorrectionTests(unittest.TestCase):
    def test_local_rule_on_actual_and_unrelated_assignments(self):
        algebra = S.Algebra(METER); M = prefixes(37)
        for n in range(2, 38):
            rule = S.pack(algebra.defect(n))
            self.assertEqual(evaluate(rule, M), 0)
            for vals in ([0, 1]+[i*i-3*i for i in range(2, 38)], [0, 1]+[0]*36):
                direct = sum(vals[d]-vals[d-1] for d in range(1, n+1) if n%d == 0)
                self.assertEqual(evaluate(rule, vals), direct)

    def test_adaptive_nonlinear_multiplier_recovery_without_target_input(self):
        inp = source({():5, (3,):2, (2,2):13, (2,7):37})
        cert = S.construct(inp, meter=METER)
        baseline = S.construct(inp, options={**S.DEFAULT_OPTIONS, 'rounds':0}, meter=METER)
        self.assertLess(bound(cert), bound(baseline))
        self.assertEqual(bound(cert), 3)
        selected = cert['rounds'][cert['selected_round']]
        self.assertTrue(any(c['multiplier_indices'] and v for c,v in zip(selected['columns'], selected['lambda_numerators'])))
        self.assertEqual(evaluate(cert['selected_polynomial'], prefixes(7)), 3*S.GRID)
        self.assertTrue(cert['scalar_fake']['violated_used_constraints'])

    def test_exact_polynomial_correction_identity_on_nonarithmetic_inputs(self):
        inp = source({():-11, (2,3):-7, (4,4):2, (5,):3, (6,7):5}, degree=2, den=5)
        cert = S.construct(inp, meter=METER)
        for row in cert['rounds']:
            for offset in (-3, 0, 2):
                vals = [0,1]+[offset+n%3 for n in range(2,8)]
                delta = 0
                for col,lam in zip(row['columns'], row['lambda_numerators']):
                    n = col['n']
                    defect = sum(vals[d]-vals[d-1] for d in range(1,n+1) if n%d == 0)
                    delta += lam*prod(vals[i] for i in col['multiplier_indices'])*defect
                self.assertEqual(evaluate(row['residual'],vals), S.GRID*evaluate(inp['polynomial'],vals)+delta)

    def test_robust_box_lower_against_arbitrary_feasible_controls(self):
        p = {():4,(2,):3,(3,):-2}; a=S.Algebra(METER)
        columns=[(2,()),(3,())]; box=7
        row=S.solve(p,columns,box,1,a,2.0)
        lower=Q(row['boxed_lower'])
        for x in (-box,-2,0,3,box):
            for y in (-box,-1,0,2,box):
                _,upper,_=S.replay(p,columns,[x*S.GRID,y*S.GRID],{},box,1,a)
                self.assertLessEqual(lower,upper)

    def test_signed_zero_and_constant_base_cases(self):
        for p in ({},{():-19}):
            cert=S.construct(source(p,U=1,den=7),meter=METER)
            self.assertEqual(cert['rounds'],[])
            self.assertEqual(cert['selected_round'],-1)
            self.assertTrue(cert['constant_only_selected'])
            self.assertTrue(cert['full_divisor_system_used'])
            self.assertEqual(bound(cert),abs(Q(p.get((),0),7)))

    def test_fractional_weights_and_all_constant_powers(self):
        a=S.Algebra(METER)
        for key in ((),(2,),(2,3),(7,7,11)):
            for text in ('0','1/257','3/11','2/7','1/2','1'):
                q=Q(text); w=a.upper_weight(key,text)
                target=prod(key)**q.numerator*S.GRID**q.denominator
                self.assertGreaterEqual(w**q.denominator,target)
                self.assertLess((w-1)**q.denominator,target)
        poly={():-3*S.GRID,(2,):4*S.GRID,(2,3):-5*S.GRID}
        prices=S.conditional_prices(poly,3,7,['0','1/2','1'],a)
        self.assertEqual(prices[0]['coefficients'],['3/7','4/7','5/7','0'])
        vals=[0,1,4,-6]
        self.assertLessEqual(abs(Q(evaluate(S.pack(poly),vals),S.GRID*7)),
            sum(Q(c)*2**d for d,c in enumerate(prices[-1]['coefficients'])))

    def test_explicit_extended_domain_is_preserved_and_paid(self):
        cert=S.construct(source({(2,2):5},U=2,degree=2),constraint_radius=11,meter=METER)
        self.assertEqual(cert['constraint_radius'],11)
        self.assertEqual(cert['input']['U'],2)
        self.assertEqual(evaluate(cert['selected_polynomial'],prefixes(11)),0)
        self.assertFalse(cert['uniform_head_bound_proved'])
        self.assertFalse(cert['conditional_prefix_bounds_paid'])

    def test_failed_numerical_proposal_retains_valid_zero_fallback(self):
        failure=SimpleNamespace(success=False,nit=4,message='synthetic optimizer failure')
        with patch.object(S,'linprog',return_value=failure):
            cert=S.construct(source({(3,):7}),meter=METER)
        self.assertEqual(cert['selected_round'],-1)
        self.assertTrue(cert['rounds'])
        self.assertTrue(all(r['solver']['status']=='failed_zero_fallback' for r in cert['rounds']))
        self.assertEqual(bound(cert),21)

    def test_rank_spread_and_scout_cover_large_constraint_scales(self):
        self.assertEqual(S.rank_spread(4),[2,3,4])
        self.assertEqual(S.rank_spread(1000)[-1],1000)
        a=S.Algebra(METER)
        p={(3,):7,(2,7):-11}
        dual={key:(1 if v>0 else -1)*prod(key)*S.GRID for key,v in p.items()}
        candidates,meta=S.scout(p,dual,11,3,[],2,a)
        self.assertEqual(len(candidates),2)
        self.assertTrue(meta['pool_limited'])
        self.assertTrue(all(2<=n<=11 and len(q)<=2 for n,q in candidates))

    def test_reject_missing_support_bad_indices_and_unbounded_requests(self):
        bad=source({(3,):1},U=2)
        with self.assertRaises(ValueError):S.construct(bad,meter=METER)
        with self.assertRaises(ValueError):S.construct(source({(2,):1}),constraint_radius=2,meter=METER)
        with self.assertRaises(ValueError):S.construct(source({}),price_exponents=['2/4'],meter=METER)
        with self.assertRaises(ValueError):S.construct(source({}),options={**S.DEFAULT_OPTIONS,'rounds':9},meter=METER)
        with self.assertRaises(OverflowError):S.Algebra(METER).upper_weight((3,),'1/1000000')

    def test_independent_checker_and_new_source_pipeline_binding(self):
        import copy
        import check_mobius_divisor_correction_070 as C
        import run_mobius_divisor_correction_070 as R
        import mobius_convolution_scale_069 as P
        import check_mobius_convolution_scale_069 as PC
        inp=source({():5,(3,):2,(2,2):13,(2,7):37})
        cert=S.construct(inp,meter=METER)
        cm=C.Meter();v=C.verify_correction(cert,cm);METER.charge(cm.operations)
        self.assertTrue(v['verified']);self.assertEqual(v['source_actual_value'],'3')
        mutant=copy.deepcopy(cert);mutant['selected_polynomial'][0]['numerator']+=1
        with self.assertRaises(ValueError):C.verify_correction(mutant)
        params={'primes':[2,3,5],'p':3,'q':5,'alpha':'1/5','gamma':'5/28','tau':'1/2'}
        parent=P.construct(17,14,4,params,[['1/2']*2,['1/3']*3],meter=METER)
        pm=PC.Meter();pv=PC.verify_control(parent,pm);METER.charge(pm.operations)
        endpoints=[];oldendpoints=[]
        for ep,pve in zip(parent['endpoints'],pv['endpoints']):
            rows=[]
            for row in ep['rows']:
                models=[]
                for i,model in enumerate(row['models']):
                    cc=S.construct(S.input_from_model(model,ep['denominator']),meter=METER)
                    cm=C.Meter();cv=C.verify_correction(cc,cm);METER.charge(cm.operations)
                    self.assertEqual(cv['source_actual_value'],pve['rows'][row['j']-1]['actual_coefficient'])
                    models.append({'parent_model_index':i,'certificate':cc,'verification':cv})
                best=min(range(len(models)),key=lambda i:(R.upper(models[i]['certificate']),R.multiplier_count(models[i]['certificate']),i))
                rows.append({'j':row['j'],'R':row['R'],'models':models,'selected_model':best})
            endpoints.append({'ratio':ep['ratio'],'rows':rows})
            actual=str(abs(Q(pve['rows'][0]['actual_coefficient'])))
            oldendpoints.append({'ratio':ep['ratio'],'actual_head_variation':actual,'prior068_certified_head_upper':actual,'selected_conditional_C1_head_prices':[actual]})
        saved={'N':17,'y':14,'max_j':4,'certificate':parent,'verification':pv,'original_source_binding_proved':True,
               'RH_proved':False,'uniform_head_bound_proved':False,
               'source_cases':[{'N':17,'y':14,'H':4,'theta':'1/2','endpoints':oldendpoints}]}
        self.assertEqual(R.bind_parent(saved),(parent,pv))
        result=R.summarize(saved,endpoints,METER)
        self.assertEqual(len(result[0]['endpoints']),2)
        saved['source_cases'][0]['H']=3
        with self.assertRaises(ValueError):R.summarize(saved,endpoints,METER)


if __name__=='__main__':unittest.main()
