import copy
from fractions import Fraction as F
import tempfile
import unittest
import check_factor_region_run as c


class RunChecks(unittest.TestCase):
    def program(self, weight='1', eta='0'):
        scheme={'prime_power':'1/2','core_power':'1/2'}
        feature={'scheme':scheme,'scheme_id':c.digest(scheme), 'vector':[0,0,0,0,0,1,0,0,0], 'eta':eta}
        feature['feature_id']=c.digest(feature)
        return {'target':{'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'}]},
                'terms':[{'feature':feature,'weight':weight}],'constants':{'2':'1'}}

    def test_prime_obstruction_has_precise_scope(self):
        p=self.program();w=c.prime_obstruction(p)[0]
        self.assertEqual(w['coefficient'],'1/32')
        self.assertTrue(w['global_potential_innovation_claim_refuted'])
        self.assertFalse(w['direct_target_energy_claim_refuted'])
        self.assertFalse(w['RH_refuted'])
        for term in [('0','0'),('1','1')]:
            self.assertEqual(c.prime_obstruction(self.program(*term)),[])
        p['target']['filter'].append({'divisor':6,'weight':'-11/4'})
        self.assertEqual(c.prime_obstruction(p),[])
        p=self.program();p['terms'][0]['feature']['scheme']['prime_power']='1/3'
        self.assertEqual(c.prime_obstruction(p),[])

    def test_pole_and_global_promotion_guards(self):
        p=self.program();self.assertEqual(c.pole_bridge(p['target'])['retained_pole_order_at_least'],2)
        p['target']['r']=0;p['target']['filter'].append({'divisor':2,'weight':'1'})
        with self.assertRaises(ValueError):c.pole_bridge(p['target'])
        with self.assertRaises(ValueError):c.no_promotions({'nested':[{'RH_proved':True}]})
        c.no_promotions({'global_bound_proved':False})
        with self.assertRaises(ValueError):c.prime_obstruction(self.program('-1'))

    def test_exact_selection_retains_baseline_and_lp_groups(self):
        p=self.program();q=copy.deepcopy(p);q['terms']=[]
        items=[dict(program_id=c.digest(v),program=v,origins=[{'kind':origin}])
               for v,origin in [(p,'singleton'),(q,'baseline')]]
        items[0]['origins'].append({'kind':'lp'})
        factory=dict(target_id='t',candidates=items)
        scores=[dict(program_id=i['program_id'],score=dict(missing_cases=0,finite_failures=0)) for i in items]
        selected,decisions=c.selected([factory],scores)
        self.assertEqual(len(selected),2)
        self.assertEqual(decisions[1]['selected_id'],c.digest(q))
        self.assertEqual(selected[c.digest(p)]['origins'],['singleton','lp'])
        scores[0]['score']['missing_cases']=1
        self.assertGreater(c.rank(items[0],scores[0]['score']),c.rank(items[1],scores[1]['score']))

    def test_missing_run_does_not_certify(self):
        with tempfile.TemporaryDirectory() as path:
            with self.assertRaises(FileNotFoundError):c.audit_run(path)


if __name__=='__main__':unittest.main()
