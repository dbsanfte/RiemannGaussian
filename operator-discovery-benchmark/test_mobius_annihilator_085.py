import unittest
from fractions import Fraction as Q
import mobius_annihilator_085 as A
import mobius_annihilator_bank_085 as BANK
import check_mobius_annihilator_085 as C
from test_mobius_coupled_square_084 import program


def bank():
    return [dict(scale=a,u_exponent=e,complement=c,unit_balance=b)for a,e,c,b in
            [('1/9','1',False,True),('1/3','2/3',True,False),('1','5/7',False,True)]]


class AnnihilatorTests(unittest.TestCase):
    def test_complete_identity_columns_independent(self):
        p=program();model=A.B.build_model(p,137);V,K=A.identity_vectors(model,bank())
        independent=C.C.build_model(p,137);other=C.build_identities(independent,bank())
        self.assertEqual(K,other['cuts'])
        self.assertEqual([[Q(str(V[i,j]))for j in range(V.ncols())]for i in range(V.nrows())],other['vectors'])
        empty,_=A.identity_vectors(A.B.build_model(p,1),bank())
        self.assertEqual((empty.nrows(),empty.ncols()),(0,len(bank())))

    def test_signed_cross_correction_and_factor_exact_admission(self):
        p=program();model=A.B.build_model(p,137);n=model['price_dimension'];outer=A.SQUARE.O.synthesize(p)['certificate']
        H=[[Q(-2),Q(1,3),Q(0)],[Q(1,3),Q(3),Q(-1,5)],[Q(0),Q(-1,5),Q(-1)]]
        cert,_=A.certificate(model,bank(),H,8,[[i-2]for i in range(n)])
        self.assertEqual(C.verify_certificate(p,137,outer,bank(),cert)['status'],'VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND')

    def test_solver_and_exact_redundant_column_removal(self):
        p=program();b=bank()+bank()[:1];proposal=A.solve(p,b,131,time_limit=5)
        self.assertEqual(proposal['status'],'EXACT_ANNIHILATOR_SQUARE_PROPOSAL')
        self.assertLess(proposal['identity_rank'],len(b))
        outer=A.SQUARE.O.synthesize(p)['certificate']
        self.assertEqual(C.verify_certificate(p,131,outer,b,proposal['certificate'])['status'],'VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND')

    def test_generic_bank_inference_uses_artificial_witnesses(self):
        cat=BANK.catalog(program(),[131,137],scale_height=5,exponent_height=5)
        signs={u:[1 if i%2==0 else -1 for i in range(m['price_dimension'])]for u,m in cat['models'].items()}
        one=BANK.select(cat,signs,bank_size=3);two=BANK.select(cat,signs,bank_size=3)
        self.assertEqual(one,two);self.assertLessEqual(len(one['bank']),3)
        self.assertTrue(any(Q(d['descriptor']['u_exponent']).denominator>2 for d in cat['generated']))
        self.assertEqual(len(cat['representatives'])+len(cat['training_only_duplicates']),len(cat['generated']))
        self.assertGreater(one['scalar_operations'],0)
        with self.assertRaises(A.B.ResourceLimit):BANK.select(cat,signs,bank_size=3,meter=BANK.ScoreMeter(limit=1))
        signs[131][0]=-1
        with self.assertRaises(ValueError):BANK.select(cat,signs,bank_size=3)

    def test_prospective_and_exact_schema_guards(self):
        with self.assertRaises(ValueError):A.parse_bank(bank()*6)
        b=bank()[0].copy();b['unit_balance']=1
        with self.assertRaises(ValueError):A.parse_bank([b])
        with self.assertRaises(ValueError):BANK.descriptors(100,100)
        model=A.B.build_model(program(),137);b=bank()[0].copy();b['u_exponent']='1/100001'
        with self.assertRaises(A.B.ResourceLimit):A.identity_integer_column(model,b)
        with self.assertRaises(A.B.ResourceLimit):BANK.ScoreMeter().combine(Q(1,2**4095),Q(1,3))
        model['price_dimension']=513
        with self.assertRaises(A.B.ResourceLimit):A.identity_integer_column(model,bank()[0])


if __name__=='__main__':unittest.main()
