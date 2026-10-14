import unittest
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_divisor_localizer_language as D

class Tests(unittest.TestCase):
    def square(self,group):
        out={}
        for term in group:
            p=L.load_poly(term['poly']);out=L.add(out,L.scale(L.mul(p,p),F(term['weight'])))
        return out
    def relation(self,group,H):
        out={}
        for term in group:out=L.add(out,L.mul(L.load_poly(term['multiplier']),L.relation(term['spec'],'mu',H)))
        return out
    def test_generic_norm_and_signed_closure(self):
        for X in (1,2):
            extra=D.build_additions(X);H=4*X-1
            for k in range(6):
                sq=list(map(self.square,extra['square_groups'][5*k:5*k+5]));norm=self.relation(extra['relation_groups'][2*k],H)
                self.assertEqual(norm,L.add(sq[2],L.scale(sq[1],-1)))
                # Both cubic signs and every quartic cross survive expansion.
                self.assertEqual(L.add(sq[3],sq[4]),L.scale(L.add(sq[0],sq[2]),2))
                region=extra['archive'][k]['region'];power=extra['archive'][k]['power'];co={};signed={}
                for t in extra['archive'][k]['scales']:
                    for a in range(1,t+1):
                        for b in range(1,t+1):
                            from math import gcd
                            w=F(a*b,t*t)**power
                            if gcd(a,b)==1:co=L.add(co,{tuple(sorted((a,b))):w})
                            for d in range(1,t+1):
                                if a%d==0 and b%d==0:signed=L.add(signed,{tuple(sorted((d,a,b))):w})
                self.assertEqual(self.relation(extra['relation_groups'][2*k+1],H),L.add(signed,L.scale(co,-1)))
                self.assertEqual(L.add(sq[3],L.scale(sq[4],-1)),L.scale(signed,4))
    def test_shape_coverage_zero_scalars_and_guards(self):
        d=D.descriptors();self.assertEqual((len(d['square']),len(d['relation'])),(312,331))
        e=D.build_additions(2)
        self.assertEqual([r['ordered_pair_count']for r in e['archive']],[13]*3+[126]*3)
        for g in e['square_groups']:
            for term in g:self.assertNotIn((),L.load_poly(term['poly']))
        for g in e['relation_groups']:
            for term in g:self.assertNotIn((),L.load_poly(term['multiplier']))
        for args in [dict(X=True),dict(X=2,max_operations=1),dict(X=2,max_horizon=6)]:
            with self.assertRaises((ValueError,OverflowError)):D.build_additions(**args)

if __name__=='__main__':unittest.main()
