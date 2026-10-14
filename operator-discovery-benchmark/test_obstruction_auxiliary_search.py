import unittest
from fractions import Fraction as Q
from flint import arb, ctx
import obstruction_auxiliary_search as P
import check_obstruction_auxiliary as C

METERS=[]


class AuxiliaryChecks(unittest.TestCase):
    def setUp(self):
        ctx.prec=128; self.m=P.P.Meter(); METERS.append(self.m)

    def test_complete_arithmetic_branch_split_independent_reconstruction(self):
        a=P.source_state(63,self.m); ctx.prec=192; b=C.source_state(63,self.m)
        for name in ('T','V','R'):
            for x,y in zip(a['atoms'][name],b['atoms'][name]):
                self.assertTrue(x.overlaps(y))
                self.m.charge()
        for n in range(1,64):
            self.assertTrue(a['atoms']['R'][n].overlaps(a['atoms']['T'][n]+a['atoms']['V'][n]))
        # A literal two-distinct-prime branch begins at6; all same-prime terms are peeled.
        self.assertTrue(a['atoms']['T'][5].is_zero())
        self.assertTrue(a['atoms']['T'][6]>0)
        self.assertTrue(a['atoms']['T'][8].overlaps(a['atoms']['T'][7]))

    def test_fractional_roots_are_exact_and_cover_thresholds(self):
        for text in P.EXPONENTS:
            exponent=Q(text)
            for n in (1,2,8,63,64,65,729):
                r=P.root_floor(n,text)
                self.assertEqual(r,C.integer_root(n,text))
                self.assertLessEqual(r**exponent.denominator,n**exponent.numerator)
                self.assertGreater((r+1)**exponent.denominator,n**exponent.numerator)

    def test_generic_finite_transform_kernels_retain_every_endpoint(self):
        state=dict(H=80,atoms={'T':[arb(n*n-3*n) for n in range(81)],
                               'V':[arb((-1)**n*n) for n in range(81)]})
        state['atoms']['R']=[t+v for t,v in zip(state['atoms']['T'],state['atoms']['V'])]
        for mode in ('shift','average'):
            for exponent in ('0','1/3','1/2','2/3'):
                tree=[mode,exponent,P.add(P.atom('T'),['average','1/2',P.atom('V')])]
                a=P.evaluate_tree(tree,16,16,32,state,self.m)
                b=C.evaluate_tree(tree,16,16,32,state,self.m)
                self.assertTrue(all(x.overlaps(y) for x,y in zip(a,b)))
                # Independently hand-sum the first average value at one known case.
                if mode=='average' and exponent=='1/2':
                    expected=sum((state['atoms']['T'][16+i]+sum(state['atoms']['V'][16+i:20+i],arb(0))/4
                                  for i in range(4)),arb(0))/4
                    self.assertTrue(a[0].overlaps(expected))
        with self.assertRaises(ValueError):
            P.evaluate_tree(['shift','2/3',P.atom('R')],64,64,80,state,self.m)

    def test_full_quadratic_and_transport_values_match_distinct_evaluators(self):
        source=P.source_state(127,self.m)
        programs=P.catalogue()
        parent=next(p for p in programs if p.get('channel')=='V' and p.get('exponent')=='1/2' and p.get('mode')=='average')
        programs=[programs[0],parent,P.feedback(parent,26,'average','1/3')]+[p for p in programs if p['family']=='transport']
        for p in programs:
            a=P.measure(p,16,source,self.m); b=C.measure(p,16,source,self.m)
            for name in a:
                if name!='X': self.assertTrue(a[name].overlaps(b[name]),name)
        bad=dict(parent); bad['terms']=[P.atom('T'),P.atom('V'),P.atom('R')]
        with self.assertRaises(ValueError): P.measure(bad,16,source,self.m)

    def test_feedback_uses_open_joint_expression_and_preserves_scope(self):
        parent=next(p for p in P.catalogue() if p.get('channel')=='V' and p.get('exponent')=='1/3')
        child=P.feedback(parent,26,'shift','1/2')
        self.assertEqual(child['terms'][0][2],parent['terms'][0])
        self.assertEqual(child['feedback_obligation'],'joint_energy_'+str(parent['id']))
        self.assertTrue(P.linear_identity([('1',P.atom('R'))]+[('-1',t) for t in child['terms']]))
        self.assertEqual(P.next_obligations(child)[0]['equivalence_class'],P.TARGET['id'])
        self.assertFalse(child['uniform_bound_proved'])
        self.assertTrue(all(row['status']=='open' for row in P.next_obligations(child)))
        obligation=P.next_obligations(parent)[0]
        generated=P.generate_from_obligation(obligation,parent,26,'shift','1/2')
        self.assertEqual(generated['obligation_input'],obligation)
        self.assertEqual(generated['terms'],child['terms'])
        closed=dict(obligation,status='proven')
        with self.assertRaises(ValueError):P.generate_from_obligation(closed,parent,26,'shift','1/2')
        altered=dict(obligation,expression=['energy',P.atom('T')])
        with self.assertRaises(ValueError):P.generate_from_obligation(altered,parent,26,'shift','1/2')

    def test_finite_drift_counterexample_never_refits_or_becomes_a_proof(self):
        rows=[dict(drift=arb(-2)),dict(drift=arb(1)/3)]
        cap=P.fitted_drift(rows,self.m)
        before=cap; out=P.score([dict(drift=arb(2))],cap,self.m)
        self.assertEqual(out['failed'],1); self.assertEqual(cap,before)
        self.assertFalse(out['uniform_bound_proved'])


def tearDownModule():
    print('SYNTHETIC_WORK module=test_obstruction_auxiliary_search operations='+str(sum(m.operations for m in METERS)))


if __name__=='__main__':unittest.main()
