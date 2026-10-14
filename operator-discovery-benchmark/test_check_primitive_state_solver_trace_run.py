import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_primitive_state_solver_trace_run as I


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,sort_keys=True,allow_nan=False))


class ArchiveAuditTests(unittest.TestCase):
    def protocol(self):
        return dict(schema='primitive-state-solver-trace-run-v1',program=I.PROGRAM,scales=[1,2,3,5],phases=I.PHASES,
            language=I.B.SPEC,gram_specs=I.B.gram_specs(),compiler_limits=I.COMPILER_LIMITS,trace_limits=I.TRACE_LIMITS,
            parallel=I.PARALLEL,tests=I.TESTS,
            strategy='two independent numerical traces on unchanged complete source equations; no exact admission',
            no_refit_or_source_selection=True,historical_development_scales=True,canonical_primal_matrix_independently_rebuilt=False,
            solver_contract=dict(versions=dict(scipy='1',cvxpy='2',clarabel='3',numpy='4'),
                support_options=dict(threads=1,parallel=False,disp=True),primal_options=dict(max_threads=1,verbose=True)),**I.FLAGS)

    def execution(self):
        return dict(results=[dict(index=i,status='missing_resource',reason='synthetic external deadline') for i in range(2)],
            cost=dict(requested_workers=2,workers=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,
                worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',
                max_in_flight=2,elapsed_seconds=1.,result_bytes=0,payload_bytes=100,available=0,missing=2,errors=0))

    def archive(self,root):
        d=root/'run';(d/'frozen_source').mkdir(parents=True);(d/'jobs').mkdir()
        names=['run_primitive_state_solver_trace.py','check_primitive_state_solver_trace_run.py']
        for n in names:
            (root/n).write_text('# synthetic frozen source\n');(d/'frozen_source'/n).write_text('# synthetic frozen source\n')
        for n in I.INPUTS:write(root/n,dict(files={}) if n.endswith('manifest.json') else {})
        write(d/'protocol.json',self.protocol());write(d/'source_seal.json',{n:I.sha(root/n) for n in names})
        write(d/'input.json',dict(input_sha256={n:I.sha(root/n) for n in I.INPUTS}))
        write(d/'seal.json',{n+'_sha256':I.sha(d/(n+'.json')) for n in ['protocol','source_seal','input']})
        write(d/'run_started.json',dict(protocol_sha256=I.sha(d/'protocol.json')))
        write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 1 test\nOK'))
        write(d/'execution.json',self.execution())
        self.reseal(d,len(names))
        return d,names

    def reseal(self,d,count):
        entries={str(p.relative_to(d)):I.sha(p) for p in d.rglob('*') if p.is_file() and 'frozen_source' not in p.parts and p.name not in ('receipt.json','independent_verification.json')}
        write(d/'receipt.json',dict(files_sha256=entries,source_count=count,**I.FLAGS))

    def test_complete_external_failures_are_unknown(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);d,names=self.archive(root)
            geometry=dict(columns=[],domain=[],redundancy=[])
            with patch.object(I,'ROOT',root),patch.object(I,'source_names',return_value=names),patch.object(I,'rebuild',return_value=({},geometry)) as rebuild:
                review=I.audit(d,write=True)
                self.assertTrue(review['all_passed']);self.assertEqual(review['mathematical_feasibility'],'UNKNOWN')
                self.assertTrue(all(not c['trace_retained'] for c in review['checks']))
                self.assertFalse(review['infeasibility_proved']);self.assertEqual(rebuild.call_count,1)
                with self.assertRaises(FileExistsError):I.audit(d,write=True)

    def test_inventory_byte_hash_and_unbound_file_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);write(d/'execution.json',{})
            receipt=dict(files_sha256={'execution.json':I.sha(d/'execution.json')})
            self.assertTrue(I.verify_inventory(d,receipt))
            (d/'execution.json').write_text('{} ')
            with self.assertRaises(ValueError):I.verify_inventory(d,receipt)
            receipt['files_sha256']['execution.json']=I.sha(d/'execution.json')
            (d/'hidden.log').write_text('lost diagnostic')
            with self.assertRaises(ValueError):I.verify_inventory(d,receipt)

    def test_order_runtime_and_no_serial_fallback(self):
        e=self.execution();self.assertTrue(I.verify_runtime(e))
        for key,value in [('serial_fallback',True),('numerical_threads_per_worker',2),('memory_budget_bytes',7*1024**3),('workers',3),('missing',1)]:
            bad=copy.deepcopy(e);bad['cost'][key]=value
            with self.assertRaises(ValueError):I.verify_runtime(bad)
        for change in ('order','missing','invented'):
            bad=copy.deepcopy(e)
            if change=='order':bad['results'][0]['index']=1
            elif change=='missing':bad['results'].pop()
            else:bad['results'][0]['value']={}
            with self.assertRaises(ValueError):I.verify_runtime(bad)

    def test_protocol_change_and_claims_rejected(self):
        self.assertTrue(I.verify_protocol(self.protocol()))
        for key,value in [('phases',['dual']),('scales',[1,2,3]),('canonical_primal_matrix_independently_rebuilt',True),('certified',True)]:
            bad=self.protocol();bad[key]=value
            with self.assertRaises(ValueError):I.verify_protocol(bad)
        for flag in I.FLAGS:
            with self.assertRaises(ValueError):I.scope({flag:True})

    def test_solver_settings_versions_and_time_limits(self):
        trace=dict(vector_role='raw_failed_last_iterate',solver=dict(name='scipy-highs',versions={'scipy':'1'},
            options=dict(time_limit=30.,threads=1,parallel=False,disp=True)))
        self.assertTrue(I.verify_solver(trace,'dual',self.protocol()))
        for edit in ('time','version','option','accepted'):
            bad=copy.deepcopy(trace)
            if edit=='time':bad['solver']['options']['time_limit']=901.
            elif edit=='version':bad['solver']['versions']['scipy']='changed'
            elif edit=='option':bad['solver']['options']['threads']=2
            else:bad['vector_role']='accepted_proposal'
            with self.assertRaises(ValueError):I.verify_solver(bad,'dual',self.protocol())

    def test_partial_progress_binds_startup_without_invented_vector(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);path=d/'jobs/primal-progress.json';source=Path(str(path)+'.source.json')
            startup=dict(schema='primitive-state-solver-trace-v1',kind='primal-progress',numerical_evidence_only=True,
                original_vector=None,vector_role='unavailable',solver={},source_hashes={},original_system_hash='a',
                scaled_original_system_hash='b',solver_system_hash='c',transformation_receipt={})
            write(source,startup);write(path,dict(schema=startup['schema'],kind='primal-progress',numerical_evidence_only=True,
                original_vector=None,vector_role='unavailable',source_checkpoint_hash=I.TRACE.digest(startup),raw_info={'iterations':7}))
            with patch.object(I,'system_metadata',return_value={}),patch.object(I,'verify_trace',return_value={'verified':True}) as check:
                startup['solver']={'versions':{}};write(source,startup)
                progress=I.read(path);progress['source_checkpoint_hash']=I.TRACE.digest(startup);write(path,progress)
                result=I.verify_progress(d,'primal',None,{},self.protocol(),{})
                self.assertTrue(result['partial_only']);self.assertEqual(check.call_count,1)
                progress['original_vector']=[0.];write(path,progress)
                with self.assertRaises(ValueError):I.verify_progress(d,'primal',None,{},self.protocol(),{})

    def test_atomic_partial_windows_remain_nonadmitted(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);path=d/'jobs/primal-progress.json';startup_path=Path(str(path)+'.source.json')
            startup=dict(schema='primitive-state-solver-trace-v1',kind='primal-progress',numerical_evidence_only=True,
                original_vector=None,vector_role='unavailable',solver={},source_hashes={},original_system_hash='a',
                scaled_original_system_hash='b',solver_system_hash='c',transformation_receipt={})
            write(startup_path,startup)
            with patch.object(I,'system_metadata',return_value={}),patch.object(I,'verify_trace',return_value={'verified':True}):
                out=I.verify_progress(d,'primal',None,{},self.protocol(),{})
                self.assertEqual(out['origin'],'startup-before-first-progress');self.assertTrue(out['partial_only'])
            startup_path.unlink()
            final=dict(schema='primitive-state-solver-trace-v1',kind='primal',original_vector=[1.])
            write(path,final)
            with patch.object(I,'complete_trace_check',return_value={'verified':True}) as check:
                out=I.verify_progress(d,'primal',None,{},self.protocol(),{})
                self.assertEqual(out['origin'],'terminal-checkpoint-before-trace-transport')
                self.assertFalse(out['exact_admission']);self.assertEqual(check.call_count,1)

    def test_partial_atomic_trace_cap_and_foreign_artifacts(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);p=d/'jobs/primal-progress.json.tmp';p.parent.mkdir()
            p.write_bytes(b'x'*70000)
            receipt=dict(files_sha256={'jobs/primal-progress.json.tmp':I.sha(p)})
            self.assertTrue(I.verify_inventory(d,receipt))
            p=d/'candidate.json';write(p,{'certified':True})
            receipt['files_sha256']['candidate.json']=I.sha(p)
            with self.assertRaises(ValueError):I.verify_inventory(d,receipt)

    def test_final_progress_must_equal_trace(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);path=d/'jobs/dual-progress.json'
            trace=dict(schema='primitive-state-solver-trace-v1',kind='support',original_vector=None)
            write(path,trace)
            self.assertTrue(I.verify_progress(d,'dual',trace,{},self.protocol(),{})['terminal_trace_equal'])
            trace['termination_status']=4
            with self.assertRaises(ValueError):I.verify_progress(d,'dual',trace,{},self.protocol(),{})

    def test_duplicate_json_nonfinite_and_path_escape(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);p=d/'bad.json'
            for text in ('{"status":4,"status":0}','{"x":NaN}'):
                p.write_text(text)
                with self.assertRaises(ValueError):I.read(p)
            with self.assertRaises(ValueError):I.path_under(d,'../escape')

    def test_missing_trace_cannot_be_promoted(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);path=d/'jobs/dual.json'
            cost=dict(elapsed_seconds=1.,cpu_seconds=1.,peak_rss_kib=10,observed_threads_at_completion=1,pid=1)
            record=dict(phase='dual',index=0,program=I.PROGRAM,scales=[1,2,3,5],status='trace_available',cost=cost,**I.FLAGS)
            write(path,record)
            row=dict(index=0,status='available',value=dict(file='jobs/dual.json',sha256=I.sha(path),status=record['status'],cost=cost))
            with self.assertRaises(ValueError):I.verify_job(d,'dual',0,row,{}, {},self.protocol(),{})

if __name__=='__main__':unittest.main()
