import copy
from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_exact_row_basis_probe as I
import run_primitive_state_exact_row_basis_probe as runner


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value,sort_keys=True,allow_nan=False))


class WholeBasisAuditTests(unittest.TestCase):
    def geometry(self):
        columns=[{} for _ in range(363)]
        for j,q in [(0,1),(1,4),(2,-4),(3,3),(123,5),(243,-17)]:columns[j]={'a':F(q),'b':F(2*q)}
        return dict(columns=columns,lhs={'a':F(7),'b':F(14)},domain=['a','b'],shape=[1,1],offset=3,compilation=1)

    def process(self,d):
        geometry=self.geometry();retained,recipes=I.PROJECT.full15_recipes(geometry['shape'],geometry['offset'],I.ORIGINAL.B.gram_specs(),len(geometry['columns']))
        out=runner.process_equations(geometry['columns'],geometry['lhs'],geometry['domain'],retained,recipes,
            directory=d/'jobs',deadline=time.monotonic()+10,compilation_work_reserve=1)
        self.assertEqual(out['status'],'basis_verified')
        artifacts=I.verify_stage_artifacts(d,geometry)
        return geometry,out,artifacts

    def metadata(self,d,geometry,out):
        record=dict(out,phase='primal_preprocessing',index=0,program=I.PROGRAM,scales=[1,2,3,5],solver_called=False,
            complete_columns=len(geometry['columns']),complete_monomials=len(geometry['domain']),projected_columns=242,
            compilation_work_reserve=1,case_hashes=['synthetic'],deadline_exceeded=False,
            exact_columns_hash=I.ORIGINAL.G.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in geometry['columns']]),
            exact_target_hash=I.ORIGINAL.G.digest([[list(m),str(q)] for m,q in sorted(geometry['lhs'].items())]),
            cost=dict(elapsed_seconds=1.,cpu_seconds=.5,peak_rss_kib=10,observed_threads_at_completion=1,pid=7))
        write(d/'jobs/primal.json',record)
        transport=dict(index=0,status='available',value=dict(file='jobs/primal.json',sha256=I.sha(d/'jobs/primal.json'),
            status=record['status'],cost=record['cost'],**I.FLAGS))
        return record,transport

    def protocol(self):
        return dict(schema='primitive-state-exact-row-basis-probe-v1',program=I.PROGRAM,scales=[1,2,3,5],phases=['primal_preprocessing'],
            language=I.ORIGINAL.B.SPEC,gram_specs=I.ORIGINAL.B.gram_specs(),compiler_limits=I.COMPILER_LIMITS,limits=I.LIMITS,
            parallel=I.PARALLEL,tests=I.TESTS,parent_publication='publication-012',expected_shape=I.EXPECTED_SHAPE,
            strategy='verify full15 column identities, exact augmented row basis, independent replay; no solver',
            solver_called=False,no_refit_or_source_selection=True,historical_development_scales=True,**I.FLAGS)

    def execution(self):
        return dict(results=[dict(index=0,status='missing_resource',reason='synthetic external deadline')],
            cost=dict(requested_workers=1,workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,
                worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',max_in_flight=1,
                elapsed_seconds=1.,result_bytes=0,payload_bytes=100,available=0,missing=1,errors=0))

    def test_complete_exact_pipeline_and_ledger(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry,out,artifacts=self.process(d)
            check=I.verify_state(d,out,geometry,artifacts)
            self.assertTrue(check['equation_reduction_verified']);self.assertTrue(check['ledger']['all_stages_committed'])
            record,transport=self.metadata(d,geometry,out)
            job=I.verify_job(d,transport,{'case_hashes':['synthetic']},geometry,artifacts)
            self.assertEqual(job['selected_original_row_indices'],[0]);self.assertFalse(job['certified'])
            self.assertEqual(job['mathematical_feasibility'],'UNKNOWN')

    def test_every_ledger_allocation_precision_and_budget_binding(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry,out,artifacts=self.process(d)
            for mode in ('allocation','reserve','precision','order','total','over-cap','wrong-charge'):
                state=copy.deepcopy(out);ledger=state['ledger']
                if mode=='allocation':ledger['entries'][2]['allocation']+=1
                elif mode=='reserve':ledger['entries'][1]['reserve']-=1
                elif mode=='precision':ledger['entries'][1]['precision']='allocated_unverified'
                elif mode=='order':ledger['entries'][1],ledger['entries'][2]=ledger['entries'][2],ledger['entries'][1]
                elif mode=='total':ledger['total_work_reserve']+=1
                elif mode=='over-cap':ledger['max_work']=450000001
                else:ledger['entries'][2]['charged_operations']+=1
                with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_state(d,state,geometry,artifacts)

    def test_wrong_domain_or_worker_check_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry,out,_=self.process(d)
            wrong=copy.deepcopy(geometry);wrong['domain'].reverse()
            with self.assertRaises(ValueError):I.verify_stage_artifacts(d,wrong)
            p=d/'jobs/projection-check.json';check=I.read(p);check['audit_operations']+=1;write(p,check)
            with self.assertRaises(ValueError):I.verify_stage_artifacts(d,geometry)

    def test_pending_check_file_committed_before_ledger_and_checkpoint(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry,out,artifacts=self.process(d)
            state=copy.deepcopy(out);state.update(status='missing_resource',equation_reduction_verified=False,selected_original_row_indices=None)
            checker=state['ledger']['entries'][4]
            checker.update(reserve=checker['allocation'],charged_operations=None,precision='allocated_unverified')
            producer=state['ledger']['entries'][3]
            producer.update(reserve=producer['allocation'],charged_operations=None,precision='allocated_unverified')
            # Checker allocation was reserved while producer retained its full cap.
            state['ledger']['total_work_reserve']=sum(e['reserve'] for e in state['ledger']['entries'])
            state['ledger']['remaining_work']=450000000-state['ledger']['total_work_reserve']
            state['artifacts'].pop('basis-check')
            result=I.verify_state(d,state,geometry,artifacts)
            self.assertFalse(result['equation_reduction_verified']);self.assertIn('basis_checker',result['ledger']['pending_stages'])
            state.update(status='basis_verified',equation_reduction_verified=True,selected_original_row_indices=[0])
            with self.assertRaises(ValueError):I.verify_state(d,state,geometry,artifacts)

    def test_external_failure_keeps_final_checkpoint_without_promotion(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry,out,artifacts=self.process(d)
            transport=dict(index=0,status='missing_resource',reason='worker died after checkpoint')
            check=I.verify_job(d,transport,{},geometry,artifacts)
            self.assertFalse(check['equation_reduction_verified']);self.assertIsNone(check['selected_original_row_indices'])
            self.assertTrue(check['progress']['equation_reduction_verified'])

    def test_outer_failure_metadata_retains_audited_progress_without_process_return(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry,out,artifacts=self.process(d)
            record,transport=self.metadata(d,geometry,out)
            for key in ('ledger','artifacts','original_rows','original_columns','projection_columns','retained_rows','augmented_rank','inconsistent_augmented_pivots'):
                record.pop(key,None)
            record.update(status='missing_resource',equation_reduction_verified=False,selected_original_row_indices=None,reason='failure checkpoint write also failed')
            write(d/'jobs/primal.json',record);transport['value'].update(sha256=I.sha(d/'jobs/primal.json'),status=record['status'])
            check=I.verify_job(d,transport,{'case_hashes':['synthetic']},geometry,artifacts)
            self.assertTrue(check['outer_failure_without_process_return']);self.assertFalse(check['equation_reduction_verified'])
            self.assertTrue(check['progress']['equation_reduction_verified'])

    def test_unknown_tiny_envelope_has_no_reduction_or_basis_attempt(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry=self.geometry()
            receipt=dict(schema=I.PROJECT.SCHEMA,status='unknown',complete=False,reason='receipt byte cap')
            write(d/'jobs/projection.json',receipt)
            artifacts=I.verify_stage_artifacts(d,geometry)
            self.assertFalse(artifacts['checks']['projection']['projection_authorized'])
            fake=dict(I.FLAGS,status='unknown',equation_reduction_verified=False,selected_original_row_indices=None)
            self.assertFalse(I.verify_state(d,fake,geometry,artifacts)['equation_reduction_verified'])
            write(d/'jobs/basis.json',dict(schema=I.BASIS.SCHEMA,status='unknown',complete=False,reason='operation cap'))
            with self.assertRaises(ValueError):I.verify_stage_artifacts(d,geometry)

    def test_interrupted_worker_checker_late_replay_does_not_refine_ledger(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry=self.geometry();keep,recipes=I.PROJECT.full15_recipes(geometry['shape'],geometry['offset'],I.ORIGINAL.B.gram_specs(),363)
            with patch.object(runner.PROJECT_CHECK,'verify_projection',side_effect=TimeoutError('calibration interruption')):
                out=runner.process_equations(geometry['columns'],geometry['lhs'],geometry['domain'],keep,recipes,directory=d/'jobs',
                    deadline=time.monotonic()+10,compilation_work_reserve=1)
            artifacts=I.verify_stage_artifacts(d,geometry)
            self.assertTrue(artifacts['checks']['projection']['complete'])
            check=I.verify_state(d,out,geometry,artifacts)
            self.assertFalse(check['equation_reduction_verified']);self.assertEqual(check['ledger']['pending_stages'],['projection_producer','projection_checker'])
            self.assertEqual(out['ledger']['entries'][1]['reserve'],50000000)

    def test_protocol_runtime_inventory_and_partial_byte_caps(self):
        self.assertTrue(I.verify_protocol(self.protocol()));self.assertTrue(I.verify_runtime(self.execution()))
        protocol=self.protocol();protocol['solver_called']=True
        with self.assertRaises(ValueError):I.verify_protocol(protocol)
        execution=self.execution();execution['cost']['workers']=2
        with self.assertRaises(ValueError):I.verify_runtime(execution)
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);p=d/'jobs/basis.json.tmp';p.parent.mkdir();p.write_bytes(b'x'*70000)
            receipt=dict(files_sha256={'jobs/basis.json.tmp':I.sha(p)},solver_called=False,**I.FLAGS)
            self.assertTrue(I.verify_inventory(d,receipt))
            (d/'candidate.json').write_text('{}')
            with self.assertRaises(ValueError):I.verify_inventory(d,receipt)

    def test_cumulative_independent_audit_caps(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry,_,_=self.process(d)
            for limits in [dict(max_audit_operations=1),dict(max_audit_cells=1)]:
                with self.assertRaises((OverflowError,ValueError)):I.verify_stage_artifacts(d,geometry,**limits)
            with self.assertRaises(TimeoutError):I.verify_stage_artifacts(d,geometry,deadline=time.monotonic()-1)

    def test_whole_archive_hash_closure_external_unknown_rebuild_once(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);d=root/'run';(d/'frozen_source').mkdir(parents=True);(d/'jobs').mkdir()
            names=['run_primitive_state_exact_row_basis_probe.py','check_primitive_state_exact_row_basis_probe.py']
            for name in names:
                (root/name).write_text('# synthetic frozen source\n');(d/'frozen_source'/name).write_bytes((root/name).read_bytes())
            parent={}
            for i in range(259):
                p=root/f'prior-{i}.txt';p.write_text('synthetic immutable prior\n');parent[p.name]=I.sha(p)
            for name in I.INPUTS:write(root/name,dict(files=parent) if name.endswith('manifest.json') else {})
            geometry=self.geometry();shape=dict(original_rows=2,original_columns=363,projected_columns=242,omitted_columns=121)
            with patch.object(I,'EXPECTED_SHAPE',shape):protocol=self.protocol()
            write(d/'protocol.json',protocol);write(d/'source_seal.json',{n:I.sha(root/n) for n in names})
            write(d/'input.json',dict(input_sha256={n:I.sha(root/n) for n in I.INPUTS}))
            write(d/'seal.json',{n+'_sha256':I.sha(d/(n+'.json')) for n in ['protocol','source_seal','input']})
            write(d/'run_started.json',dict(protocol_sha256=I.sha(d/'protocol.json')))
            write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 11 tests in 0.1s\n\nOK\n'))
            write(d/'execution.json',self.execution())
            files={str(p.relative_to(d)):I.sha(p) for p in d.rglob('*') if p.is_file() and 'frozen_source' not in p.parts}
            write(d/'receipt.json',dict(files_sha256=files,source_count=2,solver_called=False,**I.FLAGS))
            with patch.object(I,'ROOT',root),patch.object(I,'EXPECTED_SHAPE',shape),patch.object(I,'source_names',return_value=names),\
                 patch.object(I.ORIGINAL,'rebuild',return_value=({},geometry)) as rebuild:
                review=I.audit(d,write=True)
                self.assertTrue(review['all_passed']);self.assertFalse(review['equation_reduction_verified']);self.assertIsNone(review['selected_original_row_indices'])
                self.assertEqual(rebuild.call_count,1);self.assertEqual(review['mathematical_feasibility'],'UNKNOWN')
                with self.assertRaises(FileExistsError):I.audit(d,write=True)

if __name__=='__main__':unittest.main()
