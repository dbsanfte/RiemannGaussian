"""Small operational contract tests; no mathematical claim is tested here."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import detector_review_planner as p


class PlannerContracts(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.base=Path(self.temp.name)
        self.source=self.base/'source';self.source.mkdir()
        self.spec={'description':'seven arbitrary sealed leads'}
        self.queue={'protocol_sha256':p.digest(self.spec),'queue':[
            {'program_id':f'candidate-{i}','exact_program':{'free':i,'terms':[]},
             'global_claim':f'exact quantified claim {i}'} for i in range(7)]}
        p.write_new(self.source/'protocol.json',self.spec)
        p.write_new(self.source/'proof_queue.json',self.queue)
        p.write_new(self.source/'seal.json',{'protocol_sha256':p.digest(self.spec),
            'files':{'proof_queue.json':p.sha(self.source/'proof_queue.json')}})
        self.plan=self.base/'plan'

    def tearDown(self):self.temp.cleanup()

    def complete(self):
        m=p.plan(self.source,self.plan,workers=3)
        for i in range(1,m['batch_count']+1):
            name=f'batch-{i:02d}.json';b=p.read(self.plan/name);agent=f'/actual/tool-agent-{i}'
            p.record_receipt(self.plan,i,agent,p.sha(self.plan/name),'gpt-6.1-sol')
            p.write_new(self.plan/f'batch-{i:02d}-review.json',{'batch':i,
                'input_sha256':p.sha(self.plan/name),'tool_agent_task_name':agent,
                'runtime_model_independently_verified':False,
                'reviews':[{'program_id':r['program_id'],
                    'exact_program_sha256':r['exact_program_sha256'],
                    'precise_claim_sha256':r['precise_claim_sha256'],
                    'status':'unresolved','original_formula_changed':False}
                    for r in b['candidates']]})
        return m

    def test_seven_generic_candidates_complete_and_no_model_promotion(self):
        self.complete();r=p.preflight(self.plan)
        self.assertEqual(r['reviewed_candidates'],7)
        self.assertFalse(r['runtime_model_independently_verified'])
        self.assertTrue(r['domain_adjudication_required'])
        collection=self.base/'collection';p.collect(self.plan,collection)
        self.assertTrue((collection/'collection.json').exists())
        with self.assertRaises(FileExistsError):p.collect(self.plan,collection)

    def test_missing_review_never_creates_collection(self):
        m=p.plan(self.source,self.plan);destination=self.base/'not-created'
        with self.assertRaises(FileNotFoundError):p.collect(self.plan,destination)
        self.assertFalse(destination.exists());self.assertEqual(m['batch_count'],3)

    def test_refuses_sealed_worker_and_existing_plan(self):
        with self.assertRaises(FileExistsError):p.refuse_sealed_worker_destination(self.source)
        p.plan(self.source,self.plan)
        with self.assertRaises(FileExistsError):p.plan(self.source,self.plan)

    def test_potential_queue_and_seal_mutation(self):
        self.queue['potential_queue']=self.queue.pop('queue')
        (self.source/'proof_queue.json').write_text(json.dumps(self.queue))
        (self.source/'seal.json').write_text(json.dumps({'protocol_sha256':p.digest(self.spec),
            'files':{'proof_queue.json':p.sha(self.source/'proof_queue.json')}}))
        p.plan(self.source,self.plan,workers=7)
        (self.source/'proof_queue.json').write_text('{}')
        with self.assertRaises(ValueError):p.validate_plan(self.plan)

    def test_bad_receipt_duplicate_review_and_global_overclaim(self):
        self.complete()
        with self.assertRaises(ValueError):p.record_receipt(self.plan,1,'/wrong','wrong')
        file=self.plan/'batch-01-review.json';out=p.read(file)
        out['reviews'][1]=out['reviews'][0].copy();file.write_text(json.dumps(out))
        with self.assertRaises(ValueError):p.preflight(self.plan)
        original=p.read(self.plan/'batch-01.json')['candidates'][1]
        out['reviews'][1]={'program_id':original['program_id'],
            'exact_program_sha256':original['exact_program_sha256'],
            'precise_claim_sha256':original['precise_claim_sha256'],
            'status':'unresolved','original_formula_changed':False}
        file.write_text(json.dumps(out))
        out=p.read(self.plan/'batch-02-review.json')
        out['reviews'][0]['RH_proved']=True
        (self.plan/'batch-02-review.json').write_text(json.dumps(out))
        with self.assertRaises(ValueError):p.preflight(self.plan)

    def test_zero_optimization_environment_allowed(self):
        with patch.dict(os.environ,{'PYTHONOPTIMIZE':'0'}):
            self.assertEqual(p.plan(self.source,self.plan)['batch_count'],3)

    def test_optimization_and_path_escape_rejected(self):
        with patch.dict(os.environ,{'PYTHONOPTIMIZE':'1'}):
            with self.assertRaises(RuntimeError):p.plan(self.source,self.plan)
        with self.assertRaises(ValueError):p.source_record(self.source,'../elsewhere')
        self.assertFalse(self.plan.exists())


if __name__=='__main__':unittest.main()
