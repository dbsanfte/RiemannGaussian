"""New synthetic algebra tests, independent of all scientific lifts."""
from fractions import Fraction as Q
from itertools import product
import unittest

import mobius_quadratic_contraction_064 as S

METER=S.Meter()


def fixture(H=2,K=2):
    return {'N':31,'y':23,'H':H,'K':K,'parameters':{'p':2,'q':7,'primes':[2,7]},
        'linear_terms':[['0']*H for _ in range(2)],
        'long_kernels_after_fill':[[['0']*K for _ in range(H)] for _ in range(2)]}


def terms(cert,e,j):
    return {t['index']:Q(t['coefficient']) for t in cert['endpoints'][e]['rows'][j-1]['terms']}


class QuadraticContractionSearchTests(unittest.TestCase):
    def test_squarefree_masks_and_overlap(self):
        ps,ms=S.prime_masks(12,METER)
        self.assertEqual(ps,[2,3,5,7,11]);self.assertEqual(ms[1],0)
        self.assertIsNone(ms[4]);self.assertIsNone(ms[12])
        self.assertEqual(ms[6]^ms[10],ms[3]^ms[5])

    def test_shared_prime_diagonal_is_constant(self):
        lift=fixture();lift['long_kernels_after_fill'][0][1][1]='1'
        compiled=S.compile_lift(lift,METER);cert=S.condition(lift,compiled,[],METER)
        self.assertEqual(terms(cert,0,1),{1:Q(-1),2:Q(1)})
        self.assertEqual(terms(cert,0,2),{2:Q(-1)})

    def test_linear_and_quadratic_terms_cancel_together(self):
        lift=fixture();lift['linear_terms'][0][1]='13/257'
        lift['long_kernels_after_fill'][0][1][0]='13/257'
        compiled=S.compile_lift(lift,METER);cert=S.condition(lift,compiled,[],METER)
        self.assertEqual(cert['budget'],'0');self.assertGreater(Q(compiled['raw_term_l1'][0]),0)

    def test_overlapping_composite_indices_and_conditioning_parity(self):
        lift=fixture(6,10);lift['long_kernels_after_fill'][0][5][9]='1'
        compiled=S.compile_lift(lift,METER);empty=S.condition(lift,compiled,[],METER)
        self.assertEqual(terms(empty,0,1),{15:Q(-1),30:Q(1)})
        partial=S.condition(lift,compiled,[2,3,5],METER)
        self.assertEqual(terms(partial,0,1),{1:Q(-2)})

    def test_envelope_dominates_all_remaining_sign_assignments(self):
        lift=fixture(5,5)
        lift['linear_terms'][0]=['1/2','-1','2','0','3/5']
        lift['long_kernels_after_fill'][0][1]=['1','2/3','-1','9','2']
        lift['long_kernels_after_fill'][0][4]=['-1','0','1','0','2/7']
        compiled=S.compile_lift(lift,METER);cert=S.condition(lift,compiled,[2],METER)
        ps=compiled['primes'];ms=compiled['masks']
        for assignment in product((-1,1),repeat=len(ps)-1):
            signs=[-1]+list(assignment);u=[0]*6
            for n in range(1,6):
                if ms[n] is not None:
                    u[n]=1
                    for i,z in enumerate(signs):
                        if ms[n]&(1<<i):u[n]*=z
            norm=Q(0)
            for j in range(1,6):
                value=Q(0)
                for at,sign in ((j,1),(j+1,-1)):
                    for m in range(1,5//at+1):
                        d=at*m-1
                        value+=sign*u[m]*(Q(lift['linear_terms'][0][d])-sum((Q(a)*u[l] for l,a in enumerate(lift['long_kernels_after_fill'][0][d],1)),Q(0)))
                        METER.charge(160)
                norm+=abs(value)
            self.assertLessEqual(norm,Q(cert['budget']))

    def test_conditioning_monotone_and_full_evaluation_exact(self):
        lift=fixture(5,5)
        lift['linear_terms'][0]=['1','-2','3','-4','5']
        lift['long_kernels_after_fill'][0][3]=['1','1','1','1','1']
        compiled=S.compile_lift(lift,METER)
        prices=[Q(S.condition(lift,compiled,ps,METER)['budget']) for ps in ([],[2],[2,3],[2,3,5])]
        self.assertEqual(prices,sorted(prices,reverse=True))
        full=S.condition(lift,compiled,[2,3,5],METER)
        self.assertTrue(all(t['index']==1 for e in full['endpoints'] for row in e['rows'] for t in row['terms']))

    def test_rational_conditioning_powers_and_duplicate_plans(self):
        lift=fixture(49,0);compiled=S.compile_lift(lift,METER)
        plans=S.conditioning_plans(lift,compiled,METER)
        half=next(p for p in plans if 'prefix_1/2' in p['labels'])
        self.assertEqual(half['primes'],[2,3,5,7])
        self.assertEqual(len({tuple(p['primes']) for p in plans}),len(plans))
        self.assertEqual(sum(p['fully_conditioned'] for p in plans),1)

    def test_zero_K_unit_and_invalid_conditioning(self):
        lift=fixture(1,0);lift['linear_terms'][0][0]='-1/257'
        compiled=S.compile_lift(lift,METER);cert=S.condition(lift,compiled,[],METER)
        self.assertEqual(terms(cert,0,1),{1:Q(-1,257)})
        with self.assertRaises(ValueError):S.condition(lift,compiled,[2],METER)
        with self.assertRaises(ValueError):S.prime_masks(True,METER)

    def test_independent_source_and_contraction_composition(self):
        import mobius_prefix_completion_062 as B
        import mobius_prefix_repair_063 as R
        import check_mobius_quadratic_source_064 as CS
        import check_mobius_quadratic_contraction_064 as CC
        params={'alpha':'1/257','gamma':'1/3','tau':'3/4','primes':[2,7],'p':2,'q':7}
        raw=B.inverse_completion(31,23,6,params,METER)
        base=B.exact_certificate(31,23,6,params,raw['endpoints'],METER)
        repaired=R.construct(base,'core_inverse',meter=METER)
        lift=R.quadratic_lift(base,'core_inverse',repaired['repair'],METER)
        cm=CS.Meter();source=CS.verify_quadratic(lift,repaired['repair'],cm);METER.charge(cm.operations)
        self.assertTrue(source['verified'])
        result=S.discover(lift,METER)
        for candidate in result['candidates']:
            cm=CC.Meter();checked=CC.verify_contraction(lift,candidate['certificate'],cm);METER.charge(cm.operations)
            self.assertTrue(checked['finite_variation_bound_proved'])
            self.assertFalse(checked['uniform_N_growth_proved'])
            if candidate['fully_conditioned']:
                self.assertEqual(Q(checked['budget']),max(map(Q,repaired['repair']['coefficient_l1'])))

    def test_custom_rational_powers_without_denominator_whitelist(self):
        lift=fixture(100,0);compiled=S.compile_lift(lift,METER)
        plans=S.conditioning_plans(lift,compiled,METER,powers=['0','1/257','5/11','7/8','1'])
        empty=next(p for p in plans if 'none' in p['labels'])
        self.assertIn('prefix_1/257',empty['labels']);self.assertIn('prefix_0',empty['labels'])
        middle=next(p for p in plans if 'prefix_5/11' in p['labels'])
        self.assertEqual(middle['primes'],[2,3,5,7])
        high=next(p for p in plans if 'prefix_7/8' in p['labels'])
        self.assertEqual(high['primes'],[p for p in compiled['primes'] if p<=56])
        discovered=S.discover(lift,METER,powers=['5/11','1'])
        self.assertTrue(any('prefix_5/11' in c['labels'] for c in discovered['candidates']))
        unit=fixture(1,0);unit_compiled=S.compile_lift(unit,METER)
        for powers in (['2/4'],['-1/3'],['3/2'],[0.5],'1/2', ['0']*257):
            with self.assertRaises(ValueError):S.conditioning_plans(unit,unit_compiled,METER,powers=powers)
        with self.assertRaises(OverflowError):
            S.conditioning_plans(lift,compiled,METER,powers=['1/500001'])

    def test_exact_sign_witnesses_degree_and_fourier_lower_guard(self):
        # Distinct characters on the two free prime signs, with a shared
        # assignment across rows. Both endpoint arrays are deliberately equal.
        rows=[{'j':1,'terms':[{'index':n,'coefficient':str(c)} for n,c in
            ((1,Q(2)),(2,Q(-3)),(3,Q(1,2)),(6,Q(5,7)))]},
            {'j':2,'terms':[{'index':2,'coefficient':'1'},{'index':3,'coefficient':'-1'}]}]
        cert={'endpoints':[{'ratio':r,'rows':rows} for r in ('2/7','1')]}
        diagnostic=S.sign_diagnostics(cert,METER)
        for endpoint in diagnostic['endpoints']:
            self.assertEqual(endpoint['maximum_remaining_prime_degree'],2)
            values=[]
            for x,y in product((-1,1),repeat=2):
                values.append(abs(2-3*x+Q(1,2)*y+Q(5,7)*x*y)+abs(x-y))
            self.assertEqual(Q(endpoint['all_free_plus_one_l1']),values[-1])
            self.assertEqual(Q(endpoint['actual_all_free_minus_one_l1']),values[0])
            self.assertEqual(Q(endpoint['fourier_l2_squared']),4+9+Q(1,4)+Q(25,49)+2)
            self.assertGreaterEqual(max(values)**2,Q(endpoint['fourier_l2_squared']))
        self.assertFalse(diagnostic['uniform_growth_conclusion'])

    def test_saved_whole_merge_binding_and_source_mutations(self):
        from copy import deepcopy
        import mobius_prefix_completion_062 as B
        import mobius_prefix_repair_063 as R
        import check_mobius_prefix_completion_062 as W
        import check_mobius_prefix_repair_063 as C
        import run_mobius_quadratic_contraction_064 as RUN
        params={'alpha':'1/257','gamma':'1/3','tau':'3/4','primes':[2,7],'p':2,'q':7}
        raw=B.inverse_completion(37,29,5,params,METER)
        base=B.exact_certificate(37,29,5,params,raw['endpoints'],METER)
        repaired=R.construct(base,'core',meter=METER)
        cm=C.Meter();repaired['repair_verification']=C.verify_repair(repaired['repair'],cm);METER.charge(cm.operations)
        wm=W.Meter();repaired['whole_verification']=W.verify_completion(repaired['completion'],wm)
        base_proof=W.verify_completion(base,wm);METER.charge(wm.operations)
        lift=R.quadratic_lift(base,'core',repaired['repair'],METER)
        saved={'selected_rule':'core','selected_budget':repaired['new_budget'],
            'selected_quadratic_lift':lift,'candidates':[repaired]}
        baseline={'candidates':[{'kind':'generic_indicator_inverse','admitted':True,
            'certificate':base,'verification':base_proof}]}
        selected,long=RUN.bind_saved_completion(saved,baseline,METER)
        self.assertIs(selected,repaired)
        self.assertEqual(str(max(long[e]+Q(repaired['repair']['coefficient_l1'][e]) for e in range(2))),repaired['new_budget'])
        changed=deepcopy(saved);changed['selected_quadratic_lift']['N']+=1
        with self.assertRaises(ValueError):RUN.bind_saved_completion(changed,baseline,METER)
        changed=deepcopy(saved);changed['candidates'][0]['completion']['coefficients'][0][0]='1234567'
        with self.assertRaises(ValueError):RUN.bind_saved_completion(changed,baseline,METER)
        changed=deepcopy(saved);changed['candidates'][0]['whole_verification']['endpoint_costs'][0]['short_residual_l1']='1'
        with self.assertRaises(ValueError):RUN.bind_saved_completion(changed,baseline,METER)
        changed=deepcopy(saved);changed['candidates'][0]['completion']['horizons']=changed['candidates'][0]['completion']['horizons'][1:]
        with self.assertRaises(ValueError):RUN.bind_saved_completion(changed,baseline,METER)
        changed=deepcopy(baseline);changed['candidates'][0]['admitted']=False
        with self.assertRaises(ValueError):RUN.bind_saved_completion(saved,changed,METER)


if __name__=='__main__':unittest.main()
