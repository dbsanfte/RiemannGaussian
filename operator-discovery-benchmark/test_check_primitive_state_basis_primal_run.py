import ast
import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_basis_primal_run as I
import test_check_primitive_state_basis_primal as fixtures


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value,sort_keys=True,allow_nan=False))


class WholeNativeTests(unittest.TestCase):
    def fixture(self,d):
        source,trace=fixtures.NativeAuditTests().fixture();columns,lhs,domain,shape,offset,specs,indices=source
        geometry=dict(columns=columns,lhs=lhs,domain=domain,shape=shape,offset=offset,compilation=1)
        hashes={'primitive_state_basis_primal.py':'p','primitive_state_solver_trace.py':'l'};trace['source_hashes']=hashes
        check=I.CORE.verify_trace(trace,*source)
        exact=dict(verified=True,complete=True,audit_operations=10,independent_audit_work_reserve=40,**I.FLAGS)
        license=dict(indices=indices,full_source_cells=sum(map(len,columns))+len(lhs),projected_nonzeros=5,projected_source_cells=8,replay_checks=dict(projection=exact,basis=exact))
        ledger=dict(max_work=450000000,total_work_reserve=0,remaining_work=0,entries=[])
        definitions=[('compilation',1,1,1,'declared_compilation_reserve'),('exact_row_preparation',20000000,20000000,None,'allocated_unverified'),
            ('projection_replay',50000000+33554432+license['full_source_cells']+5+1,40,10,'independently_verified'),
            ('basis_replay',125000000+33554432+8+1,40,10,'independently_verified'),('native_producer',50000000,50000000,None,'allocated_unverified')]
        for name,allocation,reserve,ops,precision in definitions:ledger['entries'].append(dict(stage=name,allocation=allocation,reserve=reserve,charged_operations=ops,precision=precision))
        allocation=450000000-sum(e['reserve'] for e in ledger['entries']);ledger['entries'].append(dict(stage='native_checker',allocation=allocation,reserve=check['independent_audit_work_reserve'],charged_operations=check['audit_operations'],precision='independently_verified'))
        ledger['total_work_reserve']=sum(e['reserve'] for e in ledger['entries']);ledger['remaining_work']=450000000-ledger['total_work_reserve']
        for name,value in [('primal-trace',trace),('primal-check',check),('projection-replay',exact),('basis-replay',exact),('primal-progress',dict(trace,phase='native_returned'))]:write(d/'jobs'/(name+'.json'),value)
        write(d/'jobs/primal-progress.json.source.json',dict(trace,original_vector=None,raw_solution=None,vector_role='unavailable',phase='assembled'))
        (d/'jobs/primal-native.log').write_text(trace['retained_log']['text'])
        artifacts={name:dict(file=file,sha256=I.sha(d/'jobs'/file)) for name,file in [('trace','primal-trace.json'),('check','primal-check.json')]}
        replays={name:dict(file=name+'.json',sha256=I.sha(d/'jobs'/(name+'.json'))) for name in ('projection-replay','basis-replay')}
        record=dict(termination_status=trace['termination_status'],raw_vector_available=True,canonical_system_independently_rebuilt=True,phase='primal',index=0,program=I.PROGRAM,scales=[1,2,3,5],status='trace_verified',ledger=ledger,artifacts=artifacts,exact_replay_artifacts=replays,fresh_exact_basis_authorized=True,selected_original_indices=indices,numerical_verification_pending=False,
            complete_columns=len(columns),complete_monomials=len(domain),compilation_work_reserve=1,
            exact_columns_hash=I.ORIGINAL.G.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in columns]),exact_target_hash=I.ORIGINAL.G.digest([[list(m),str(q)] for m,q in sorted(lhs.items())]),
            cost=dict(elapsed_seconds=1.,cpu_seconds=.5,peak_rss_kib=10,observed_threads_at_completion=1,pid=7),**I.FLAGS)
        write(d/'jobs/primal.json',record);write(d/'jobs/progress.json',{k:record[k] for k in ('ledger','status','artifacts','numerical_verification_pending')}|dict(phase='trace_verified',**I.FLAGS))
        transport=dict(status='available',value=dict(file='jobs/primal.json',sha256=I.sha(d/'jobs/primal.json'),status=record['status'],cost=record['cost'],**I.FLAGS))
        protocol=dict(solver_contract=dict(fixed_options={'max_threads':1},versions={'clarabel':'synthetic'}))
        return geometry,license,hashes,record,transport,protocol

    def verify(self,d,fixture):
        geometry,license,hashes,record,transport,protocol=fixture
        with patch.object(I.ORIGINAL.B,'gram_specs',return_value={'gram':2}):
            return I.verify_job(d,transport,protocol,hashes,{},geometry,license,deadline=time.monotonic()+10,max_operations=450000000,max_cells=60000000)

    def test_complete_native_trial_and_full_canonical_rebuild(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);result=self.verify(d,self.fixture(d))
            self.assertTrue(result['terminal_numerical_diagnostics_available']);self.assertTrue(result['canonical_matrix_rebuilt'])
            self.assertEqual(result['trace_check']['diagnostics']['equality_max_abs'],3.);self.assertFalse(result['accepted_proposal'])

    def test_external_failure_never_promotes_complete_checkpoint(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=list(self.fixture(d));f[4]=dict(status='missing_resource')
            (d/'jobs/primal-trace.json').unlink();(d/'jobs/primal-check.json').unlink();(d/'jobs/primal.json').unlink();(d/'jobs/progress.json').unlink()
            result=self.verify(d,f);self.assertFalse(result['terminal_numerical_diagnostics_available']);self.assertEqual(result['trace_origin'],'completed_checkpoint_without_transport_trace')

    def test_fresh_replay_required_before_native_source(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=self.fixture(d);(d/'jobs/basis-replay.json').unlink()
            with self.assertRaises(ValueError):self.verify(d,f)

    def test_native_matrix_raw_map_and_log_tampering(self):
        for mode in ('matrix','rawmap','log','check'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as temporary:
                d=Path(temporary);f=self.fixture(d)
                if mode=='log':(d/'jobs/primal-native.log').write_text('changed')
                elif mode=='check':v=I.read(d/'jobs/primal-check.json');v['audit_operations']+=1;write(d/'jobs/primal-check.json',v)
                else:
                    v=I.read(d/'jobs/primal-trace.json')
                    if mode=='matrix':v['assembly']['canonical_system_hash']='changed'
                    else:v['original_vector'][1]=0.
                    write(d/'jobs/primal-trace.json',v)
                with self.assertRaises(ValueError):self.verify(d,f)

    def test_ledger_conservative_pending_and_tampering(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);geometry,license,_,record,_,_=self.fixture(d)
            stored={'projection':license['replay_checks']['projection'],'basis':license['replay_checks']['basis']};check=I.read(d/'jobs/primal-check.json');bindings={'projection_replay','basis_replay','native_checker'}
            ledger=record['ledger'];self.assertTrue(I.verify_ledger(ledger,geometry,license,stored,check,bindings)['all_stages_committed'])
            pending=copy.deepcopy(ledger);entry=pending['entries'][-1];entry.update(reserve=entry['allocation'],charged_operations=None,precision='allocated_unverified');pending['total_work_reserve']=sum(e['reserve'] for e in pending['entries']);pending['remaining_work']=450000000-pending['total_work_reserve']
            self.assertFalse(I.verify_ledger(pending,geometry,license,stored,check,bindings)['all_stages_committed'])
            for mode in ('allocation','precision','operations','order','total'):
                altered=copy.deepcopy(ledger)
                if mode=='allocation':altered['entries'][2]['allocation']+=1
                elif mode=='precision':altered['entries'][4]['precision']='independently_verified'
                elif mode=='operations':altered['entries'][3]['charged_operations']+=1
                elif mode=='order':altered['entries'][2],altered['entries'][3]=altered['entries'][3],altered['entries'][2]
                else:altered['total_work_reserve']+=1
                with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_ledger(altered,geometry,license,stored,check,bindings)

    def test_outer_fresh_replay_failure_retains_older_checkpoint(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=list(self.fixture(d));record=f[3]
            for p in (d/'jobs').iterdir():
                if p.name not in ('primal.json','progress.json'):p.unlink()
            record.update(status='missing_resource',numerical_verification_pending=True,artifacts={});record.pop('fresh_exact_basis_authorized');record.pop('selected_original_indices');record.pop('exact_replay_artifacts')
            record['ledger']['entries']=record['ledger']['entries'][:2];record['ledger']['total_work_reserve']=20000001;record['ledger']['remaining_work']=429999999
            old=copy.deepcopy(record['ledger']);old['entries']=old['entries'][:1];old.update(total_work_reserve=1,remaining_work=449999999)
            write(d/'jobs/progress.json',dict(phase='exact_replay_started',status='missing_resource',ledger=old,artifacts={},exact_replay_artifacts={},numerical_verification_pending=True,**I.FLAGS))
            write(d/'jobs/primal.json',record);f[4]['value'].update(status='missing_resource',sha256=I.sha(d/'jobs/primal.json'))
            result=self.verify(d,f);self.assertTrue(result['outer_partial_failure']);self.assertFalse(result['terminal_numerical_diagnostics_available'])
            self.assertEqual(result['ledger']['total_work_reserve'],20000001);self.assertIsNone(result['trace_check'])

    def test_inventory_partial_caps_and_unbound_artifact(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);p=d/'jobs/primal-progress.json.tmp';p.parent.mkdir();p.write_bytes(b'x'*70000)
            receipt=dict(files_sha256={'jobs/primal-progress.json.tmp':I.sha(p)},**I.FLAGS);self.assertTrue(I.verify_inventory(d,receipt))
            (d/'candidate.json').write_text('{}')
            with self.assertRaises(ValueError):I.verify_inventory(d,receipt)

    def test_whole_archive_exclusive_review_one_rebuild(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);d=root/'run';f=self.fixture(d);geometry,license,_,record,transport,contract=f
            names=['primitive_state_basis_primal.py','primitive_state_solver_trace.py'];(d/'frozen_source').mkdir()
            for name in names:(root/name).write_text('# synthetic immutable source\n');(d/'frozen_source'/name).write_bytes((root/name).read_bytes())
            source={n:I.sha(root/n) for n in names};trace=I.read(d/'jobs/primal-trace.json');trace['source_hashes']=source
            check=I.CORE.verify_trace(trace,geometry['columns'],geometry['lhs'],geometry['domain'],geometry['shape'],geometry['offset'],{'gram':2},license['indices'])
            write(d/'jobs/primal-trace.json',trace);write(d/'jobs/primal-check.json',check);write(d/'jobs/primal-progress.json',dict(trace,phase='native_returned'))
            write(d/'jobs/primal-progress.json.source.json',dict(trace,original_vector=None,raw_solution=None,vector_role='unavailable',phase='assembled'))
            entry=record['ledger']['entries'][-1];entry.update(reserve=check['independent_audit_work_reserve'],charged_operations=check['audit_operations'])
            record['ledger']['total_work_reserve']=sum(e['reserve'] for e in record['ledger']['entries']);record['ledger']['remaining_work']=450000000-record['ledger']['total_work_reserve']
            record['artifacts']={k:dict(file='primal-'+k+'.json',sha256=I.sha(d/'jobs'/('primal-'+k+'.json'))) for k in ('trace','check')}
            write(d/'jobs/primal.json',record);write(d/'jobs/progress.json',{k:record[k] for k in ('ledger','status','artifacts','numerical_verification_pending')}|dict(phase='trace_verified',**I.FLAGS))
            transport['value']['sha256']=I.sha(d/'jobs/primal.json')
            license.update(evidence={'synthetic':'bound'},audit_operations=20,audit_cells=10,independent_audit_work_reserve=100)
            protocol=dict(schema='primitive-state-basis-primal-run-v1',program=I.PROGRAM,scales=[1,2,3,5],phases=['primal'],language=I.ORIGINAL.B.SPEC,gram_specs={'gram':2},compiler_limits=I.COMPILER_LIMITS,limits=I.LIMITS,parallel=I.PARALLEL,tests=I.TESTS,parent_publication='publication-014',basis_run='primitive-state-exact-row-basis-probe-002',basis_evidence=license['evidence'],expected_shape=dict(original_rows=5641,original_columns=1957,selected_rows=779,scalar_offset=1597),fresh_exact_replay_required_before_solver=True,strategy='fresh independently replayed saved exact tapes; one direct native primal solve on ORIGINAL equation rows; positive augmented infinity scaling; identity full coordinates',no_refit_or_source_selection=True,historical_development_scales=True,canonical_system_independently_rebuilt=True,exact_restore_all_original_rows_required=True,**contract,**I.FLAGS)
            for n in I.INPUTS:write(root/n,{'files':{}} if n.endswith('manifest.json') else {'schema':14})
            write(d/'protocol.json',protocol);write(d/'source_seal.json',source);write(d/'input.json',dict(input_sha256={n:I.sha(root/n) for n in I.INPUTS}))
            write(d/'seal.json',{n+'_sha256':I.sha(d/(n+'.json')) for n in ('protocol','source_seal','input')})
            write(d/'run_started.json',dict(protocol_sha256=I.sha(d/'protocol.json')));write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 7 tests in 0.1s\n\nOK\n'))
            execution=dict(results=[dict(index=0,**transport)],cost=dict(requested_workers=1,workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',max_in_flight=1,elapsed_seconds=1.,result_bytes=100,payload_bytes=100,available=1,missing=0,errors=0))
            write(d/'execution.json',execution)
            files={str(p.relative_to(d)):I.sha(p) for p in d.rglob('*') if p.is_file() and 'frozen_source' not in p.parts}
            write(d/'receipt.json',dict(files_sha256=files,source_count=2,**I.FLAGS))
            with patch.object(I,'ROOT',root),patch.object(I,'source_names',return_value=names),patch.object(I.ORIGINAL.B,'gram_specs',return_value={'gram':2}),patch.object(I.ORIGINAL,'rebuild',return_value=({},geometry)) as rebuild,patch.object(I,'verify_license',return_value=license):
                review=I.audit(d,write=True);self.assertTrue(review['all_passed']);self.assertTrue(review['canonical_primal_matrix_independently_rebuilt']);self.assertEqual(rebuild.call_count,1)
                self.assertEqual(review['mathematical_feasibility'],'UNKNOWN')
                with self.assertRaises(FileExistsError):I.audit(d,write=True)

    def test_no_new_runner_producer_solver_imports(self):
        tree=ast.parse(Path(I.__file__).read_text());imports=[alias.name for n in ast.walk(tree) if isinstance(n,ast.Import) for alias in n.names]
        self.assertNotIn('run_primitive_state_basis_primal',imports);self.assertNotIn('primitive_state_basis_primal',imports);self.assertNotIn('clarabel',imports);self.assertNotIn('numpy',imports)


if __name__=='__main__':unittest.main()
