import copy
import unittest
import factor_region_asymptotic_backend as b


class ProofDomain(unittest.TestCase):
    def program(self):
        s={'prime_power':'1/3','core_power':'1/2'}
        f={'scheme':s,'scheme_id':b.digest(s),'vector':[0,0,1,0,0,0,0,0,0],'eta':'1/3'}
        f['feature_id']=b.digest(f)
        return {'target':{'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'},{'divisor':6,'weight':'-11/4'}]},
                'terms':[{'feature':f,'weight':'4/17'}],'constants':{'2':'0','12':None}}

    def rehash(self,p):
        f=p['terms'][0]['feature'];f['scheme_id']=b.digest(f['scheme'])
        f['feature_id']=b.digest({k:v for k,v in f.items() if k!='feature_id'})

    def test_filtered_nonzero_is_exact_not_precision_based(self):
        p=self.program();c=b.certificate(p)
        self.assertEqual(c['status'],'global_refutation')
        self.assertEqual(c['multiplier']['exact_difference'],'-25/16')
        self.assertEqual(c['witnesses'][0]['growth_power'],'1/6')
        self.assertFalse(c['finite_data_used']);self.assertFalse(c['direct_target_energy_claim_refuted'])
        p['constants']={};self.assertTrue(b.certificate(p)['global_potential_innovation_claim_refuted'])

    def test_annihilated_leading_term_is_unsupported(self):
        p=self.program();p['target']['filter'][1]={'divisor':4,'weight':'-2'}
        self.assertEqual(b.certificate(p)['status'],'unsupported')
        p['target']['filter'][1]['weight']='2'
        self.assertEqual(b.certificate(p)['status'],'global_refutation')

    def test_zero_alias_filter_and_wrong_actual_target(self):
        p=self.program();p['target']['filter']=[{'divisor':1,'weight':'1'},{'divisor':1,'weight':'-1'}]
        self.assertEqual(b.certificate(p)['status'],'unsupported')
        p=self.program();p['target']['l']=0
        self.assertEqual(b.certificate(p)['status'],'unsupported')

    def test_uncovered_cutoffs_normalizers_and_contrasts(self):
        for field,value in [('eta','1/2'),('vector',[0,0,1,0,0,0,-1,0,0])]:
            p=self.program();p['terms'][0]['feature'][field]=value;self.rehash(p)
            self.assertEqual(b.certificate(p)['status'],'unsupported')
        for field,value in [('prime_power','1/6'),('core_power','1/3')]:
            p=self.program();p['terms'][0]['feature']['scheme'][field]=value;self.rehash(p)
            self.assertEqual(b.certificate(p)['status'],'unsupported')

    def test_all_terms_must_remain_nonnegative_and_complete(self):
        p=self.program();other=copy.deepcopy(p['terms'][0]);other['weight']='-1';p['terms'].append(other)
        self.assertEqual(b.certificate(p)['status'],'invalid')
        p=self.program();p['terms'][0]['feature']['vector'][2]=-2
        self.assertEqual(b.certificate(p)['status'],'invalid')
        self.rehash(p);self.assertEqual(b.certificate(p)['status'],'global_refutation')
        p['terms'][0]['weight']=0.25
        self.assertEqual(b.certificate(p)['status'],'invalid')


if __name__=='__main__':unittest.main()
