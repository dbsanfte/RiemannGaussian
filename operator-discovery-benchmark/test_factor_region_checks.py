import copy
from fractions import Fraction
import unittest
import factor_region_checks as c
import factor_region_arithmetic as arithmetic
import factor_region_search as search

TARGETS=[{'r':1,'l':0,'filter':[{'divisor':1,'weight':'1'}]},
         {'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'}]},
         {'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'},{'divisor':6,'weight':'-11/4'}]}]
SCHEMES=[{'prime_power':'1/2','core_power':'1/2'}]


class IndependentRegionContracts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.profile=arithmetic.profile([1,2,4,8,16,32],TARGETS,SCHEMES,use_numpy=False)
        cls.table=search.feature_table(cls.profile,TARGETS,SCHEMES)

    def test_exact_rational_powers_and_local_factors(self):
        for X in range(1,100):
            for q in (Fraction(1,6),Fraction(1,3),Fraction(1,2),Fraction(3,2)):
                n=c.floor_power(X,q);self.assertLessEqual(n**q.denominator,X**q.numerator)
                self.assertGreater((n+1)**q.denominator,X**q.numerator)
        self.assertEqual(c.floor_power(2,Fraction(1,10**100)),1)
        self.assertEqual(c.ceiling_power(2,Fraction(1,10**100)),2)
        self.assertEqual([c.local(1,1,j) for j in range(6)],[1,-2,2,-2,2,-2])
        self.assertEqual([c.local(1,2,j) for j in range(6)],[1,-3,5,-7,9,-11])

    def test_complete_arithmetic_and_features_match(self):
        self.assertTrue(c.check_profile(self.profile,[1,2,4,8,16,32],TARGETS,SCHEMES)['all_passed'])
        table=c.feature_table(self.profile,TARGETS,SCHEMES)
        self.assertEqual(table,self.table)
        self.assertTrue(c.check_feature_table(self.profile,self.table,[1,2,4,8,16,32],TARGETS,SCHEMES)['all_passed'])

    def test_cross_term_cutoff_and_coverage_tampering_rejected(self):
        for field in ('gram_numerators','cutoffs','source_coverage_sha256'):
            profile=copy.deepcopy(self.profile);row=profile['value']['rows'][-1]
            if field=='gram_numerators':row[field][1][5]+=1
            elif field=='cutoffs':row[field]['z']+=1
            else:row[field]='0'*64
            with self.assertRaises(ValueError):c.check_profile(profile,[1,2,4,8,16,32],TARGETS,SCHEMES)

    def test_exact_refit_and_unknown_level(self):
        features=self.table['value']['features'];base={'target':TARGETS[1],'terms':[{'feature':features[10],'weight':'1/4'},{'feature':features[24],'weight':'3/2'}]}
        constants,evidence=c.exact_refit(base,self.table,[1,2,4,8,16],[2,3,6,12])
        self.assertEqual((constants,evidence),search.refit(base,self.table,[1,2,4,8,16]))
        program=dict(base,constants=constants)
        score=c.exact_score(program,self.table,[1,2,4,8,16],[3,12,17])
        self.assertEqual(score,search.score(program,self.table,[1,2,4,8,16],[3,12,17]))
        self.assertEqual(score['missing_cases'],5)
        bad=copy.deepcopy(program);bad['terms'][0]['weight']='-1'
        with self.assertRaises(ValueError):c.exact_score(bad,self.table,[1],[3])

    def test_all_productions_quantization_aliases_and_fits(self):
        features=self.table['value']['features']
        factory=search.candidate_factory(self.table,TARGETS[1],features,[1,2,4,8],[2,3],use_lp=True)
        audit=c.check_candidate_archive(factory,self.table,features,[1,2,4,8],[2,3])
        self.assertEqual(audit['proposal_count'],149)
        bad=copy.deepcopy(factory);bad['proposal_archive'][1]['exact_program']['constants']['2']='0'
        with self.assertRaises(ValueError):c.check_candidate_archive(bad,self.table,features,[1,2,4,8],[2,3])

    def test_prime_component_and_uniform_obstruction(self):
        X=32;factors=c.factor_data(2*X-1);target=TARGETS[1];a=c.coefficients(2*X-1,target,factors)
        z=c.floor_power(X,'1/2');pcount=sum(factors[0][n]==n for n in range(z+1,X+1))
        component=sum(a[n] for n in range(1,X+1) if c.region_index(n,factors,z,z)==5)
        self.assertEqual(component,-2*pcount)
        feature=next(f for f in c.feature_dictionary(SCHEMES) if f['vector']==[0,0,0,0,0,1,0,0,0] and f['eta']=='1/3')
        program={'target':target,'terms':[{'feature':feature,'weight':'1/4'}]}
        self.assertTrue(c.positive_prime_singleton_obstruction(program)['admitted'])
        program['target']=TARGETS[2]
        self.assertFalse(c.positive_prime_singleton_obstruction(program)['admitted'])


if __name__=='__main__':unittest.main()
