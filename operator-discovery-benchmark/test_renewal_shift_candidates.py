import unittest
from fractions import Fraction as Q
from flint import arb, ctx
import renewal_shift_candidates as P

METERS=[]


class ProducerChecks(unittest.TestCase):
    def setUp(self):
        ctx.prec=128
        self.m=P.Meter(); METERS.append(self.m)

    def test_compilation_collision_and_higher_pole_gate(self):
        p={'shifts':['1/12','1/6','1/4','1/4']}
        expected={0:-1,1:1,2:1,3:1,4:-2,5:-2,6:1,7:1,8:1,9:-1}
        self.assertEqual(P.stencil(p),[(Q(i,12),c) for i,c in expected.items()])
        P.admissible(p)
        repeated={'shifts':['1/6','1/6']}
        self.assertEqual(P.stencil(repeated),[(Q(0),-1),(Q(1,6),2),(Q(1,3),-1)])
        with self.assertRaises(ValueError): P.admissible(repeated)
        rows=P.catalogue()
        self.assertEqual(len(rows),125)
        self.assertEqual([sum(r['eligible'] for r in rows if r['depth']==d) for d in range(1,5)],[5,10,9,3])

    def test_single_shift_divisor_identity_actual_and_changed_controls(self):
        for source in P.SOURCES:
            w=P.Workspace(source,48,self.m)
            state=w.evaluate({'shifts':['1/3']})
            for p in (2,3,5,7,17,23):
                q=arb(p)**(-arb(1)/3)
                for e in range(1,6):
                    n=p**e
                    if n>48:break
                    if source=='one': expected=3*(1-q)
                    else:
                        expected=-3*(1-q)*q**(e-1)
                        if source=='partial_prime_13' and p>13: expected*=(-1)**e
                    self.m.charge(80)
                    self.assertTrue(state['coefficients'][n].overlaps(expected))
            self.assertEqual(state['coefficients'][1],0)

    def test_two_mixed_shifts_local_and_global_normalization(self):
        w=P.Workspace('mu',48,self.m)
        program={'shifts':['1/6','1/3']}
        state=w.evaluate(program)
        scale=arb(1)/18
        for p in (2,3,5):
            a=arb(p)**(-arb(1)/6); b=a*a
            for e in range(1,6):
                n=p**e
                if n>48:break
                expected=-(1-a)*(1-b)*sum((a**j*b**(e-1-j) for j in range(e)),arb(0))/scale
                self.m.charge(100+4*e)
                self.assertTrue(state['coefficients'][n].overlaps(expected))
        # Q is multiplicative; normalized zero-unit increment is not.
        self.assertTrue(state['coefficients'][6].overlaps(scale*state['coefficients'][2]*state['coefficients'][3]))
        self.assertFalse(state['coefficients'][6].overlaps(state['coefficients'][2]*state['coefficients'][3]))

    def test_complete_center_and_absolute_channels(self):
        w=P.Workspace('mu',31,self.m)
        state=w.evaluate({'shifts':['1/12','1/6','1/4','1/4']})
        prefix=arb(0);absolute=arb(0)
        for n in range(1,32):
            prefix+=state['coefficients'][n];absolute+=abs(state['coefficients'][n])
            main=arb(0);envelope=arb(0)
            for row in state['normalizer']:
                power=arb(n)**(1-P.real(row['shift']))
                main+=row['coefficient']*power;envelope+=abs(row['coefficient'])*power
                self.m.charge(70)
            self.assertTrue(state['centered'][n].overlaps(prefix-main))
            self.assertTrue(state['absolute'][n].overlaps(absolute+envelope))
        rows=P.moments(state,[8,16],self.m)
        for row in rows:
            x=row['X']; expected=sum((t*t for t in state['centered'][x:2*x]),arb(0))/(x*x)
            self.m.charge(2*x+1)
            self.assertTrue(row['energy'].overlaps(expected))
        with self.assertRaises(ValueError):P.moments(state,[17],self.m)

    def test_baseline_and_domain(self):
        state=P.Workspace('one',15,self.m).baseline()
        mu=[0,0,-1,-1,0,-1,1,-1,0,0,1,-1,0,-1,1,1]
        self.assertEqual(state['coefficients'],list(map(arb,mu)))
        for bad in ({'shifts':[]},{'shifts':['0']},{'shifts':['1/2','1/2']},
                    {'shifts':['1/3','1/6']},{'shifts':['2/12']},{'shifts':['1/5','1/7']},
                    {'shifts':['1/6'],'extra':True},{'shifts':['1/0']}):
            with self.assertRaises(ValueError):P.validate(bad)
        self.assertFalse(any(P.FLAGS.values()))


def tearDownModule():
    print('SYNTHETIC_WORK module=test_renewal_shift_candidates operations='+str(sum(m.operations for m in METERS)))


if __name__=='__main__':unittest.main()
