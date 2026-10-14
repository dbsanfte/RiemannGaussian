import unittest
from fractions import Fraction as Q
from flint import arb,ctx
import joint_reciprocal_correlation as J
import joint_preconditioner_discovery as G
import joint_preconditioned_source as P


class Meter:
    operations=0
    def charge(self,n=1):type(self).operations+=n
    def live(self,n):self.charge()


class PreconditionedSourceTests(unittest.TestCase):
    def setUp(self):ctx.prec=160

    def test_fractional_inverse_is_complete_on_every_small_coefficient(self):
        s=J.source(15,Meter())
        rows=G.generate(Meter())
        cases=[r for r in rows if (r['shift'],r['power']) in
               {('1','0'),('1/2','1/2'),('2/3','1'),('5/6','-1/2')}]
        for program in cases:
            transformed=P.prepare(s,program,Meter())
            reconstructed=P.convolution(transformed['inverse'],transformed['w'],s['H'],Meter())
            for n in range(1,s['H']+1):
                self.assertTrue((reconstructed[n]-s['tilde_b'][n]).contains(0),(program['id'],n))

    def test_core_correction_including_unit_and_mode_gram(self):
        s=J.source(31,Meter());tables=J.prepare(s,16,Meter())
        chosen=G.choose(G.generate(Meter()));transformed=P.prepare(s,chosen,Meter())
        self.assertTrue((transformed['w'][1]+s['R_u']).contains(0))
        self.assertTrue((transformed['correction'][1]-arb(9)/2).contains(0))
        for X in (1,4,16):
            row=P.query(X,s,transformed,tables,chosen,Meter())
            scalars=[arb(9)/2,-arb(9)/2,-arb(9)/2,-s['R_u']]
            direct=sum((scalars[i]*scalars[j]*row['mode_gram'][i][j] for i in range(4) for j in range(4)),arb(0))
            self.assertTrue((direct-row['energy_core']).contains(0))
            self.assertFalse(row['signed_core_bound_proved'])

    def test_all_source_valuations_match_compiled_local_tail(self):
        s=J.source(31,Meter());chosen=G.choose(G.generate(Meter()))
        transformed=P.prepare(s,chosen,Meter());tails=G.compile_tails(chosen,Meter())
        for row in tails['terms']:
            for prime in (2,3,5):
                power=prime*prime;e=2;x=1/arb(prime).root(6)
                while power<=s['H']:
                    expected=arb(0) if row['zero_above_first_valuation'] else sum(
                        (arb(Q(c).numerator)/Q(c).denominator*x**d for d,c in row['tail']),arb(0))*x**(row['common_ratio_power']*(e-2))
                    self.assertTrue((transformed['modes'][row['name']][power]-expected).contains(0))
                    power*=prime;e+=1;Meter.operations+=80


def tearDownModule():
    print('SYNTHETIC_WORK module=test_joint_preconditioned_source operations='+str(Meter.operations))


if __name__=='__main__':unittest.main()
