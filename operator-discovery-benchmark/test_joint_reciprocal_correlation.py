import unittest
from flint import arb,ctx
import joint_reciprocal_correlation as P


class Meter:
    operations=0
    def charge(self,n=1):
        type(self).operations+=n
    def live(self,n):
        self.charge()


def fixture(a,c,R=None):
    a=list(map(arb,a));c=list(map(arb,c))
    if R is None:
        R=[arb(0)]
        for x,y in zip(a[1:],c[1:]):R.append(R[-1]+x-y)
    else:R=list(map(arb,R))
    return dict(H=len(a)-1,a=a,pure=c,R=R)


def literal(X,state):
    N=2*X-1
    values={k:{s:arb(0) for s in ('energy','low_head','high_diagonal','O')} for k in P.SECTORS}
    for h in range(1,N+1):
        for k in range(1,N+1):
            ah,ch,ak,ck=state['a'][h],state['pure'][h],state['a'][k],state['pure'][k]
            # Literal ordered geometry; no divisor convolution or prefix subtraction.
            products=(ah*ak,-ah*ck-ch*ak,ch*ck,(ah-ch)*(ak-ck))
            weight=arb(2*X-max(X,h,k))/(X*X)
            region='low_head' if h*k<=X else 'high_diagonal' if h==k else 'O'
            for name,value in zip(P.SECTORS,products):
                values[name]['energy']+=weight*value
                values[name][region]+=weight*value
                Meter.operations+=10
    return values


class JointReciprocalTests(unittest.TestCase):
    def setUp(self):ctx.prec=160

    def test_full_signed_geometry_at_unit_odd_and_dyadic_scales(self):
        s=fixture([0,0,3,-2,4,-1,0,2,-3,1,2,-4],
                  [0,2,1,0,1,-1,2,0,1,0,1,0])
        tables=P.prepare(s,6,Meter())
        for X in (1,2,3,4,6):
            result=P.query(X,tables,Meter());reference=literal(X,s)
            for sector in P.SECTORS:
                for key,value in reference[sector].items():
                    self.assertTrue((result['sectors'][sector][key]-value).contains(0),(X,sector,key))
            self.assertTrue(result['identity_residual'].contains(0))
            self.assertFalse(result['uniform_signed_bound_proved'])

    def test_source_center_changes_preserve_both_energy_crosses(self):
        s=fixture([0,2,-1,3,0,-2,1,4],[0,1,2,0,1,1,0,2],R=[0,0,2,-1,3,1,-2,4])
        tables=P.prepare(s,4,Meter());r=P.query(4,tables,Meter())
        direct=sum((s['R'][n]**2 for n in range(4,8)),arb(0))/16
        correction=sum((s['R'][n]**2-tables['tilde_R'][n]**2 for n in range(4,8)),arb(0))/16
        Meter.operations+=100
        self.assertTrue((r['energy_R']-direct).contains(0))
        self.assertTrue((r['center_correction']-correction).contains(0))
        self.assertTrue((r['O']+r['low_head']+r['high_diagonal']+correction-direct).contains(0))

    def test_actual_source_center_unit_and_remainder(self):
        meter=Meter();s=P.source(31,meter);tables=P.prepare(s,16,meter)
        self.assertTrue((s['tilde_b'][1]+s['R_u']).contains(0))
        for X in (1,4,16):
            r=P.query(X,tables,meter);bounds=P.analytic_remainder(X,s,meter)
            for name in ('low_head','high_diagonal','center_correction'):
                self.assertLess(r[name].abs_upper(),bounds[name].upper())
        self.assertTrue((tables['tilde_R'][31]-s['R'][31])>0)

    def test_zero_source_and_declared_horizon(self):
        s=fixture([0,0,0,0],[0,0,0,0]);tables=P.prepare(s,2,Meter())
        self.assertEqual(P.query(2,tables,Meter())['O'],0)
        with self.assertRaises(ValueError):P.query(3,tables,Meter())
        with self.assertRaises(ValueError):P.prepare(s,3,Meter())
        with self.assertRaises(ValueError):P.source(P.MAX_HORIZON+1,Meter())


def tearDownModule():
    print('SYNTHETIC_WORK module=test_joint_reciprocal_correlation operations='+str(Meter.operations))


if __name__=='__main__':unittest.main()
