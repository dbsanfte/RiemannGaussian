import unittest
from fractions import Fraction as Q
import check_fixed_pole_filter_run as c


class FixedRunContracts(unittest.TestCase):
    def fixture(self):
        records=[];N=15;structure=c.independent.factor_structure(N)
        for target in c.TARGETS:
            coefficients=c.independent.actual_coefficients(N,**target,structure=structure);sums=c.independent.prefix(coefficients);maximum=max(map(abs,sums))
            records.append({'target':target,'coefficients':coefficients,'prefix':sums,'divisors':c.D,
                'moments':[{'X':X,'matrix':c.independent.covariance(sums,X),'backend':'python_integer','int64_absolute_sum_bound':str(maximum*maximum*X),'complete_block':True} for X in [1,2,4,8]]})
        return {'status':'available','reason':None,'lookahead':15,'cost':1,'value':{'base_scales':[1,2,4],'scales':[1,2,4,8],'targets':records,'dictionary_sha256':c.digest(c.dictionary()),'global_bound_proved':False}}

    def test_all_moments_checked_and_offdiagonal_tamper_rejected(self):
        data=self.fixture();self.assertTrue(c.verify_dataset(data,[1,2,4])['full_covariance_verified'])
        data['value']['targets'][0]['moments'][1]['matrix'][0][1]='123'
        with self.assertRaises(ValueError):c.verify_dataset(data,[1,2,4])

    def test_exact_direct_innovation_constants_and_unknown_levels(self):
        data=self.fixture();base={'target':{'r':1,'l':1},'filter':[{'divisor':1,'weight':'1'},{'divisor':2,'weight':'-2'}]}
        constants,obs=c.exact_refit(base,data,[1,2,4],[2,3,6,12]);program={**base,'constants':constants}
        score=c.exact_score(program,data,[1,2,4],[2,3,6,12,17])
        for mode in ('direct','innovation'):
            self.assertEqual(score['modes'][mode]['finite_failures'],0)
            self.assertEqual(score['modes'][mode]['missing_cases'],3)
            self.assertTrue(all(o['reason']=='unknown_level_constant' for o in score['modes'][mode]['observations'] if o['missing']))
        self.assertEqual(c.ceil_root(8192,12),3)
        self.assertEqual(c.ceil_root(2,10**100),2)

    def test_schedule_contains_every_production_and_exact_composition(self):
        schedule=list(c.proposal_schedule())
        self.assertEqual(len(schedule),3959)
        count={kind:sum(o['kind']==kind for o,t in schedule) for kind in ('baseline','grid_two','grid_three','composition_square','inferred')}
        self.assertEqual(count,{'baseline':9,'grid_two':700,'grid_three':2880,'composition_square':120,'inferred':250})
        origin,terms=next((o,t) for o,t in schedule if o['kind']=='composition_square' and o['divisor']==3 and o['source_weight']=='-1/2')
        self.assertEqual(c.independent.canonical_filter(terms),[{'divisor':1,'weight':'1'},{'divisor':3,'weight':'-1'},{'divisor':9,'weight':'1/4'}])

    def test_absent_protocol_fails_closed(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):c.audit_run(directory)

    def test_nested_promotion_and_wrong_child_block_rejected(self):
        with self.assertRaises(ValueError):
            c.reject_promotions({'queue':[{'certificate':{'RH_proved':True}}]})
        c.reject_promotions({'conditional_bridge_admitted':True,'RH_proved':False})
        data=self.fixture()
        data['value']['targets'][0]['moments'][-1]['X']=4
        with self.assertRaises(ValueError):c.verify_dataset(data,[1,2,4])

    def test_optimization_and_hash_tampering_rejected(self):
        import os,tempfile
        from pathlib import Path
        from unittest.mock import patch
        with patch.dict(os.environ,{'PYTHONOPTIMIZE':'1'}):
            with self.assertRaises(RuntimeError):c.require_runtime()
        with patch.dict(os.environ,{'PYTHONOPTIMIZE':'0'}):c.require_runtime()
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'input.json';path.write_text('{}')
            hashes={'input.json':c.sha(path)};c.verify_hashes(directory,hashes)
            path.write_text('{"changed":true}')
            with self.assertRaises(ValueError):c.verify_hashes(directory,hashes)


if __name__=='__main__':unittest.main()
