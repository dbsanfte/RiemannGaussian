"""New synthetic tests for exact energy/cycle discovery; no saved studies."""
from fractions import Fraction as Q
from itertools import product
import unittest

import mobius_walsh_energy_065 as S
import check_mobius_walsh_energy_065 as C

METER=S.Meter()


def parent(rows,conditioned=(),H=None,K=6):
    H=len(rows) if H is None else H
    rows=rows+[{} for _ in range(H-len(rows))]
    price=sum((abs(Q(c)) for row in rows for c in row.values()),Q(0))
    endpoints=[{'ratio':ratio,'rows':[{'j':j,'terms':[{'index':n,'coefficient':str(Q(c))}
        for n,c in sorted(row.items()) if c]} for j,row in enumerate(rows,1)],'l1':str(price)} for ratio in ('2/7','1')]
    return {'schema':'mobius-quadratic-contraction-v1','N':101,'y':K*(H+1),'H':H,'K':K,
        'conditioned_primes':list(conditioned),'endpoints':endpoints,'budget':str(price)}


def checked(p,cert):
    cm=C.Meter(cap=100_000_000)
    result=C.verify_energy(p,cert,cm);METER.charge(cm.operations)
    return result


class WalshEnergySearchTests(unittest.TestCase):
    def test_arbitrary_fractional_and_negative_weight_orders(self):
        for value in (Q(1,257),Q(3,2),Q(16),Q(53,11)):
            for order in ('-2','-1/2','0','1/257','5/11','7/8','1','3/2','2'):
                w=S.dyadic_power_weight(value,order,4,METER);t=Q(order)
                a=abs(t.numerator);v=value if t>=0 else 1/value
                self.assertGreater(w,0)
                self.assertGreaterEqual(w**t.denominator,v**a)
                self.assertLess((w*Q(16,17))**t.denominator,v**a)

    def test_weight_power_validation_and_work_guards(self):
        for order in ('2/4','0.5',True):
            with self.assertRaises(ValueError):S.dyadic_power_weight(Q(2),order,4,METER)
        for value in (Q(0),Q(-1),2.0):
            with self.assertRaises(ValueError):S.dyadic_power_weight(value,'1/2',4,METER)
        with self.assertRaises(ValueError):S.dyadic_power_weight(Q(2),'1/2',True,METER)
        with self.assertRaises(OverflowError):S.dyadic_power_weight(Q(2),'1/500001',4,METER)
        with self.assertRaises(OverflowError):S.dyadic_power_weight(Q(2),'1000001',4,METER)

    def test_exact_power_boundaries_and_small_scales(self):
        for value,order,expected in ((Q(16),'1/2',Q(4)),(Q(1,16),'1/2',Q(1,4)),
                (Q(81,16),'1/4',Q(3,2)),(Q(16),'-1/2',Q(1,4)),(Q(1,257),'0',Q(1))):
            self.assertEqual(S.dyadic_power_weight(value,order,4,METER),expected)
        self.assertEqual(S.dyadic_power_weight(Q(17,16),'1',0,METER),2)

    def test_rational_square_root_ceiling(self):
        for value in (Q(0),Q(4),Q(2),Q(1,257),Q(12345,7)):
            root=S.ceil_sqrt(value,4096,METER)
            self.assertGreaterEqual(root*root,value)
            if root:self.assertLess((root-Q(1,4096))**2,value)
        with self.assertRaises(ValueError):S.ceil_sqrt(Q(-1),meter=METER)

    def test_energy_cross_row_cancellation(self):
        p=parent([{2:1,3:1},{2:1,3:-1}]);compiled=S.compile_parent(p,METER)
        self.assertEqual(S.weighted_energy(compiled['squares'][0],[Q(1),Q(1)],METER),{0:Q(4)})
        candidate=S.construct(p,compiled,[[Q(1),Q(1)]]*2,meter=METER)
        verdict=checked(p,candidate['certificate'])
        self.assertLess(Q(verdict['budget']),Q(p['budget']))
        self.assertEqual(verdict['endpoints'][0]['energy_upper'],'4')

    def test_linear_quadratic_constants_and_shared_prime_square(self):
        p=parent([{1:1,2:1,3:1,6:-1}],H=3,K=3)
        result=S.discover(p,METER,powers=['0']);cert=result['candidates'][0]['certificate']
        self.assertEqual(cert['endpoints'][0]['energy_terms'],[{'index':1,'coefficient':'4'}])
        self.assertEqual(cert['budget'],'2');checked(p,cert)

    def test_frustrated_cycle_is_discovered_and_pays_energy(self):
        p=parent([{1:1,2:1,3:1,6:-3}],H=3,K=3)
        result=S.discover(p,METER,powers=['0']);candidate=result['candidates'][0];cert=candidate['certificate']
        endpoint=cert['endpoints'][0]
        self.assertEqual(endpoint['energy_l1'],'24');self.assertEqual(endpoint['energy_upper'],'16')
        self.assertEqual(endpoint['cycles'],[{'indices':[2,3,6],'mass':'4'}])
        self.assertEqual(cert['budget'],'4');self.assertGreater(Q(candidate['uncycled_endpoint_variation_bounds'][0]),4)
        checked(p,cert)

    def test_overlapping_cycles_respect_capacities(self):
        energy={0:Q(100),1:Q(-4),2:Q(-3),3:Q(-2),4:Q(-5),5:Q(-1),6:Q(-7)}
        cycles=S.pack_cycles(energy,64,METER);spent={key:Q(0) for key in energy}
        self.assertGreater(len(cycles),1)
        for c in cycles:
            key=0;negative=0
            for m in c['masks']:key^=m;negative+=energy[m]<0;spent[m]+=c['mass']
            self.assertEqual(key,0);self.assertEqual(negative%2,1)
        self.assertTrue(all(spent[k]<=abs(q) for k,q in energy.items()))
        self.assertEqual(S.pack_cycles({1:Q(1),2:Q(1),3:Q(1)},64,METER),[])

    def test_tiny_exhaustive_common_sign_soundness(self):
        for a,b,c in product((-1,1),repeat=3):
            p=parent([{1:Q(a,3),2:b,3:c,6:Q(-2,5)},{2:1,3:-1}],K=3)
            result=S.discover(p,METER,powers=['-1/2','0','1/257','7/8','1','3/2'])
            for candidate in result['candidates']:
                cert=candidate['certificate'];verdict=checked(p,cert)
                for x,y in product((-1,1),repeat=2):
                    v=abs(Q(a,3)+b*x+c*y-Q(2,5)*x*y)+abs(x-y)
                    self.assertLessEqual(v,Q(verdict['budget']))
                    weights=list(map(Q,cert['endpoints'][0]['weights']))
                    energy=(Q(a,3)+b*x+c*y-Q(2,5)*x*y)**2/weights[0]+Q((x-y)**2)/weights[1]
                    self.assertLessEqual(energy,Q(cert['endpoints'][0]['energy_upper']))

    def test_weight_deduplication_and_zero_polynomials(self):
        p=parent([{2:1},{}]);result=S.discover(p,METER,powers=['0','1/257','1','-1'])
        self.assertEqual(len(result['candidates']),1)
        self.assertEqual(result['candidates'][0]['weight_powers'],['0','1/257','1','-1'])
        checked(p,result['candidates'][0]['certificate'])
        empty=parent([{},{}]);zero=S.discover(empty,METER)
        self.assertEqual(zero['selected_budget'],'0');self.assertEqual(len(zero['candidates']),1)
        checked(empty,zero['candidates'][0]['certificate'])

    def test_degree_four_energy_keeps_overlap(self):
        p=parent([{6:Q(2,7),35:Q(-3,11),10:Q(1,3)}],H=7,K=7)
        result=S.discover(p,METER,powers=['0','2/5'])
        for candidate in result['candidates']:
            keys={t['index'] for t in candidate['certificate']['endpoints'][0]['energy_terms']}
            self.assertIn(210,keys);self.assertIn(15,keys);self.assertIn(14,keys)
            checked(p,candidate['certificate'])

    def test_full_source_to_energy_composition(self):
        import mobius_prefix_completion_062 as B
        import mobius_prefix_repair_063 as R
        import mobius_quadratic_contraction_064 as P
        import check_mobius_quadratic_source_064 as CS
        import check_mobius_quadratic_contraction_064 as CC
        params={'alpha':'1/257','gamma':'1/3','tau':'3/4','primes':[2,7],'p':2,'q':7}
        raw=B.inverse_completion(43,31,7,params,METER)
        base=B.exact_certificate(43,31,7,params,raw['endpoints'],METER)
        repaired=R.construct(base,'core_inverse',meter=METER)
        lift=R.quadratic_lift(base,'core_inverse',repaired['repair'],METER)
        sm=CS.Meter();self.assertTrue(CS.verify_quadratic(lift,repaired['repair'],sm)['verified']);METER.charge(sm.operations)
        compiled=P.compile_lift(lift,METER);pc=P.condition(lift,compiled,[2],METER)
        cm=CC.Meter();self.assertTrue(CC.verify_contraction(lift,pc,cm)['verified']);METER.charge(cm.operations)
        result=S.discover(pc,METER,powers=['-1/2','0','5/11','1','3/2'])
        for candidate in result['candidates']:
            v=checked(pc,candidate['certificate'])
            self.assertFalse(v['uniform_N_growth_proved'])
            self.assertGreaterEqual(Q(v['budget']),max(map(Q,repaired['repair']['coefficient_l1'])))


    def test_runner_reuses_same_source_parent_and_rejects_swaps(self):
        from copy import deepcopy
        import mobius_prefix_completion_062 as B
        import mobius_prefix_repair_063 as R
        import mobius_quadratic_contraction_064 as P
        import check_mobius_quadratic_source_064 as CS
        import check_mobius_quadratic_contraction_064 as CC
        import run_mobius_walsh_energy_065 as RUN
        params={'alpha':'1/257','gamma':'1/3','tau':'3/4','primes':[2,7],'p':2,'q':7}
        raw=B.inverse_completion(43,31,7,params,METER)
        base=B.exact_certificate(43,31,7,params,raw['endpoints'],METER)
        repaired=R.construct(base,'core_inverse',meter=METER)
        lift=R.quadratic_lift(base,'core_inverse',repaired['repair'],METER)
        sm=CS.Meter();source=CS.verify_quadratic(lift,repaired['repair'],sm);METER.charge(sm.operations)
        compiled=P.compile_lift(lift,METER);pc=P.condition(lift,compiled,[2],METER)
        cm=CC.Meter();proof=CC.verify_contraction(lift,pc,cm);METER.charge(cm.operations)
        long=[sum((abs(Q(c)) for c in row),Q(0)) for row in base['coefficients']]
        old={'labels':['prefix_1/2'],'certificate':pc,'verification':proof,
            'fully_conditioned':False,'all_small_primes_through_sqrtB_conditioned':True,
            'whole_prefix_budget':str(max(long[e]+Q(pc['endpoints'][e]['l1']) for e in range(2)))}
        saved={**{k:pc[k] for k in ('N','y','H','K')},'candidates':[old],
            'independent_quadratic_source_verification':source,
            'saved_whole_proof_reused_with_exact_merge_binding':True,
            'actual_repair_endpoint_l1':repaired['repair']['coefficient_l1'],
            'long_endpoint_l1':list(map(str,long)),'actual_selected_whole_budget':repaired['new_budget']}
        chosen,pp,ll,actual=RUN.bind_parent(saved,METER)
        self.assertIs(chosen,old);self.assertIs(pp,pc);self.assertEqual(ll,long)
        self.assertEqual(actual,list(map(Q,repaired['repair']['coefficient_l1'])))
        for change in ('source','conditioning','price','admission'):
            bad=deepcopy(saved)
            if change=='source':bad['independent_quadratic_source_verification']['N']+=1
            elif change=='conditioning':bad['candidates'][0]['certificate']['conditioned_primes']=[]
            elif change=='price':bad['candidates'][0]['whole_prefix_budget']='0'
            else:bad['candidates'][0]['verification']['verified']=False
            with self.assertRaises(ValueError):RUN.bind_parent(bad,METER)


if __name__=='__main__':unittest.main()
