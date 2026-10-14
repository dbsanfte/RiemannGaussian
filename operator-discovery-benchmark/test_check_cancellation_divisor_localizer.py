import copy
import unittest
import check_cancellation_divisor_localizer as C
import cancellation_divisor_localizer_language as D
PROGRAM=dict(target='mu',q=6,C=32,claim='critical',allow_constant_slack=True,dictionary_mode='extended',constraint='zero_cubic')

class LocalizerAuditTests(unittest.TestCase):
    def test_complete_source_calibration(self):
        self.assertEqual(C.additions(),D.additions());self.assertEqual(C.descriptors(),D.descriptors())
        for X in [1,2]:
            a=C.build_additions(X);b=D.build_additions(X);self.assertEqual(a,b)
            out=D.build_instance('mu',X,6,32);self.assertTrue(C.check_builder(PROGRAM,X,out)['verified'])
        aux=C.auxiliary();self.assertEqual(len(aux['instance']['square_groups']),312);self.assertEqual(len(aux['instance']['relation_groups']),331)
        self.assertTrue(all(v=='0'for v in aux['gamma_coefficients'][319:]))
    def test_mutations(self):
        original=D.build_instance('mu',2,6,32)
        for mutation in ['coverage','weight','coefficient','archive','source_lhs']:
            out=copy.deepcopy(original)
            if mutation=='coverage':out['divisor_archive'][0]['ordered_pair_count']-=1
            if mutation=='weight':out['instance']['square_groups'][282][0]['weight']='2'
            if mutation=='coefficient':out['instance']['relation_groups'][319][0]['multiplier'][0]['c']='2'
            if mutation=='archive':out['divisor_archive'][0]['divisor_members_sha256']='0'*64
            if mutation=='source_lhs':out['instance']['lhs']=[]
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):C.check_builder(PROGRAM,2,out)
    def test_resource_domain(self):
        for args in [dict(X=True),dict(X=2,max_horizon=6),dict(X=2,max_operations=1),dict(X=2,max_terms=1),dict(X=2,max_coefficient_bits=1)]:
            with self.subTest(args=args),self.assertRaises((ValueError,OverflowError)):C.build_additions(**args)
        with self.assertRaises(ValueError):C.build(dict(PROGRAM,target='c'),1)

if __name__=='__main__':unittest.main()
