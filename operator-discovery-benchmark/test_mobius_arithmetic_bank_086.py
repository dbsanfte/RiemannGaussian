"""Tiny independent complete-column comparisons; no source science."""
import unittest
from fractions import Fraction as Q
import mobius_arithmetic_bank_086 as P
import check_mobius_arithmetic_bank_086 as C
from test_check_mobius_arithmetic_bank_086 import pair,divisor,mu
from test_check_mobius_coupled_remainder_083 import example

class Tests(unittest.TestCase):
    def test_all_delays_cut_domains_and_signed_weighted_pairs(self):
        for memory in (1,2,3):
            p,_=example(True);p['memory']=memory;p['rays']=[];p['gram_weights']=['0']*(memory+1);u=131
            pm=P.B.build_model(p,u);cm=C.C.build_model(p,u)
            bank=[divisor()]
            for on in ('prime','cofactor'):
                for i in range(memory+1):
                    d=pair(u,7,on,dict(kind='source',i=i));bank.append(d)
            bank.extend([dict(kind='prime_pair',cut_on='cofactor',cut=dict(scale='1/3',u_exponent='17/31',complement=True),weight=dict(kind='one')),dict(kind='prime_pair',cut_on='prime',cut=dict(scale='1/100',u_exponent='-1001/1000',complement=False),weight=dict(kind='one'))])
            actual=C.build_identities(cm,bank);V,meta=P.vectors(pm,bank)
            self.assertEqual(meta['cuts'],actual['cuts']);self.assertEqual(meta['prime_pair_counts'],actual['prime_pair_counts'])
            self.assertEqual([[Q(str(V[i,j]))for j in range(len(bank))]for i in range(cm['effective_dimension'])],actual['vectors'])
            for j in range(len(bank)):self.assertEqual(sum(mu(n)*actual['raw_vectors'][i][j]for i,n in enumerate(cm['coordinates'])),0)
    def test_unit_empty_and_cut_zero(self):
        p,_=example(True)
        for u in (1,4,23):
            pm=P.B.build_model(p,u);cm=C.C.build_model(p,u);b=[pair(u,1),pair(u,1,'cofactor')];V,meta=P.vectors(pm,b);v=C.build_identities(cm,b)
            self.assertEqual((V.nrows(),V.ncols()),(cm['effective_dimension'],2));self.assertEqual(meta['prime_pair_counts'],v['prime_pair_counts']);self.assertEqual([[Q(str(V[i,j]))for j in range(2)]for i in range(V.nrows())],v['vectors'])
    def test_prospective_guards_and_selected_exact_extension(self):
        from unittest.mock import patch
        from test_check_mobius_arithmetic_bank_086 import lower_proposal
        with patch.object(P.OLD_BANK,'descriptors',side_effect=AssertionError('no expansion before gate')):
            with self.assertRaises((ValueError,P.B.ResourceLimit)):P.grammar(3,24,24,24)
        p,o=example(True);u=83;pm=P.B.build_model(p,u);cm=C.C.build_model(p,u);old=[pair(u,2)];s=[1]+[mu(n)for n in cm['effective_labels'][1:]];s[cm['effective_labels'].index(15)]=-1
        generated=[dict(id='a',descriptor=pair(u,3),cost=1),dict(id='b',descriptor=pair(u,2),cost=2)]
        with patch.object(P,'CATALOG_BYTES',1),patch.object(P,'integer_column',side_effect=AssertionError('gate precedes columns')):
            with self.assertRaises(P.B.ResourceLimit):P.catalog(pm,generated)
        cat=P.catalog(pm,generated);selected=P.choose_extension(cat,s);self.assertEqual(selected['status'],'EXACT_VIOLATING_IDENTITY');cert=lower_proposal(p,o,u,old,s);r=C.verify_extension(p,u,o,old,cert,selected['selected']['descriptor']);self.assertEqual(r['status'],'VERIFIED_FINITE_ARITHMETIC_BANK_INFORMATION_GAIN')
        meter=P.B.Meter();meter.ops=meter.limit
        with self.assertRaises(P.B.ResourceLimit):P.choose_extension(cat,s,meter=meter)
        with self.assertRaises(ValueError):P.choose_extension(cat,[-1]+s[1:])
        fake=dict(cat);fake['prospective_catalog_bytes']=P.CATALOG_BYTES
        with self.assertRaises(P.B.ResourceLimit):P.choose_extension(fake,s)
