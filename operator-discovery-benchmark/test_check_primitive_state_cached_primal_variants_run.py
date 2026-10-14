import ast
import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_cached_primal_variants_run as I
import run_primitive_state_cached_primal_variants as R
import test_primitive_state_cached_primal_variants as fixtures


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value,sort_keys=True,allow_nan=False))


class WholeVariantTests(unittest.TestCase):
    def execution(self,results,workers):
        return dict(results=results,cost=dict(requested_workers=workers,workers=workers,worker_memory_bytes=3*1024**3,memory_budget_bytes=workers*3*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',max_in_flight=workers,elapsed_seconds=1.,result_bytes=100,payload_bytes=100,available=sum(r['status']=='available' for r in results),missing=sum(r['status']=='missing_resource' for r in results),errors=sum(r['status']=='error' for r in results)))

    def fixture(self,d):
        (d/'jobs').mkdir(parents=True,exist_ok=True)
        args,initial=fixtures.fixture();columns,lhs,domain,shape,offset,specs,selected=args
        geometry=dict(columns=columns,lhs=lhs,domain=domain,shape=shape,offset=offset,compilation=1)
        parent=dict(assembly=initial['assembly'],bindings=initial['parent_bindings'],indices=selected,audit_operations=20,audit_cells=10,independent_audit_work_reserve=100,parent_solver_contract=R.PREVIOUS.solver_contract())
        prep=R.process_prepare(*args,directory=d/'jobs/prepare',deadline=time.monotonic()+20,compilation_work_reserve=1,parent_assembly=initial['assembly'],parent_bindings=initial['parent_bindings'])
        self.assertEqual(prep['status'],'cache_verified');cache=I.read_cache(d/'jobs/prepare/source-cache.json');witness=I.CORE.prepare_verified_cache(cache)
        records=[dict(prep,phase='prepare',index=0,complete_columns=1,complete_monomials=1,compilation_work_reserve=1)]
        for index,v in enumerate(I.VARIANTS):
            out=R.process_variant(cache,prep['cache_binding'],v['id'],directory=d/'jobs'/v['id'],deadline=time.monotonic()+20)
            self.assertEqual(out['status'],'trace_verified');records.append(dict(out,phase='variant',index=index))
        transports=[]
        for folder,record,index in zip(['prepare']+[v['id'] for v in I.VARIANTS],records,[0,0,1]):
            record.update(deadline_exceeded=False,cost=dict(elapsed_seconds=1.,cpu_seconds=.5,peak_rss_kib=10,observed_threads_at_completion=1,pid=7));p=d/'jobs'/folder/'job.json';write(p,record)
            transports.append(dict(index=index,status='available',value=dict(file=str(p.relative_to(d)),sha256=I.sha(p),status=record['status'],cost=record['cost'],**I.FLAGS)))
        protocol=R.protocol(dict(selected_original_indices=selected,indices_hash=I.CORE.digest(selected),parent_assembly=parent['assembly'],parent_bindings=parent['bindings']))
        return dict(geometry=geometry,parent=parent,cache=cache,witness=witness,prep=self.execution([transports[0]],1),execution=self.execution(transports[1:],2),protocol=protocol,sources=cache['source_hashes'],records=records)

    def variant(self,d,f,index=0):
        return I.verify_variant_job(d,index,I.VARIANTS[index]['id'],f['execution'],f['protocol'],f['sources'],f['parent'],f['cache'],f['witness'],deadline=time.monotonic()+20,max_operations=450000000,max_cells=60000000)

    def test_complete_preparation_and_both_fixed_variants(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=self.fixture(d);prep=I.verify_preparation(d,f['prep'],f['geometry'],f['parent'],f['cache'],f['witness'].check,{})
            self.assertTrue(prep['shared_cache_available'])
            for index in range(2):
                result=self.variant(d,f,index);self.assertTrue(result['numerical_diagnostics_available']);self.assertTrue(result['cache_verification_reused']);self.assertFalse(result['accepted_proposal'])
                self.assertEqual(result['trace_check']['trace_check']['original_variables'],1)

    def test_failed_preparation_transport_keeps_cache_without_promotion(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=self.fixture(d);f['prep']['results'][0]=dict(index=0,status='error',reason='outer serialization')
            prep=I.verify_preparation(d,f['prep'],f['geometry'],f['parent'],f['cache'],f['witness'].check,{})
            self.assertFalse(prep['shared_cache_available']);self.assertTrue(prep['cache_retained'])

    def test_variant_external_failure_retains_completed_native_trace(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=self.fixture(d);f['execution']['results'][0]=dict(index=0,status='missing_resource');p=d/'jobs/qdldl_default';(p/'job.json').unlink();(p/'trace.json').unlink();(p/'check.json').unlink();(p/'progress.json').unlink()
            result=self.variant(d,f);self.assertFalse(result['numerical_diagnostics_available']);self.assertEqual(result['trace_origin'],'completed_checkpoint_without_final_transport')
            self.assertTrue(result['trace_check']['verified'])

    def test_written_check_before_checkpoint_commit_remains_nonadmitted(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=self.fixture(d);folder=d/'jobs/qdldl_default';record=f['records'][1]
            entry=record['ledger']['entries'][-1];entry.update(reserve=entry['allocation'],charged_operations=None,precision='allocated_unverified');record['ledger'].update(total_work_reserve=450000000,remaining_work=0)
            record.update(status='missing_resource',numerical_verification_pending=True);record['artifacts'].pop('check');write(folder/'job.json',record)
            write(folder/'progress.json',dict(phase='variant_check_started',status='missing_resource',ledger=record['ledger'],artifacts=record['artifacts'],variant='qdldl_default',cache_binding=record['cache_binding'],**I.FLAGS))
            f['execution']['results'][0]['value'].update(status='missing_resource',sha256=I.sha(folder/'job.json'))
            result=self.variant(d,f);self.assertFalse(result['numerical_diagnostics_available']);self.assertTrue(result['trace_check']['verified'])
            self.assertFalse(result['lifecycle']['ledger']['all_stages_committed']);self.assertEqual(result['lifecycle']['ledger']['total_work_reserve'],450000000)

    def test_blocked_stage_keeps_complete_cache_and_no_solver_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=self.fixture(d)
            for variant in I.VARIANTS:
                for p in (d/'jobs'/variant['id']).iterdir():p.unlink()
            f['execution']=dict(status='blocked',reason='shared cache gate',results=[])
            I.verify_runtime(f['execution'],f['prep'])
            for index in range(2):
                result=self.variant(d,f,index);self.assertEqual(result['transport_status'],'blocked');self.assertFalse(result['numerical_diagnostics_available']);self.assertIsNone(result['trace_check'])

    def test_actual_cache_hash_fixed_options_and_raw_trace_tampering(self):
        for mode in ('hash','options','trace','check'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as temporary:
                d=Path(temporary);f=self.fixture(d);p=d/'jobs/qdldl_default'
                if mode=='check':q=I.read(p/'check.json');q['audit_operations']+=1;write(p/'check.json',q)
                else:
                    q=I.read(p/'trace.json')
                    if mode=='hash':q['cache_binding']['cache_file_hash']='changed'
                    elif mode=='options':q['solver']['options']['static_regularization_constant']=1e-6;q['solver']['options_hash']=I.CORE.digest(q['solver']['options'])
                    else:q['assembly']['canonical_system_hash']='changed'
                    write(p/'trace.json',q)
                with self.assertRaises(ValueError):self.variant(d,f)

    def test_ledger_pending_precision_and_resource_tampering(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);f=self.fixture(d);record=f['records'][1];check=I.read(d/'jobs/qdldl_default/check.json');cells=f['cache']['assembly']['counts']['source_cells']
            self.assertTrue(I.verify_ledger(record['ledger'],1,check,variant=True,source_cells=cells)['all_stages_committed'])
            for mode in ('allocation','reserve','precision','total'):
                altered=copy.deepcopy(record['ledger'])
                if mode=='allocation':altered['entries'][1]['allocation']+=1
                elif mode=='reserve':altered['entries'][2]['reserve']-=1
                elif mode=='precision':altered['entries'][1]['precision']='independently_verified'
                else:altered['total_work_reserve']+=1
                with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_ledger(altered,1,check,variant=True,source_cells=cells)
            pending=copy.deepcopy(record['ledger']);q=pending['entries'][-1];q.update(reserve=q['allocation'],charged_operations=None,precision='allocated_unverified');pending.update(total_work_reserve=450000000,remaining_work=0)
            self.assertFalse(I.verify_ledger(pending,1,check,variant=True,source_cells=cells)['all_stages_committed'])

    def test_parent_only_declared_solver_changes_and_protocol(self):
        with tempfile.TemporaryDirectory() as temporary:
            f=self.fixture(Path(temporary));I.verify_protocol(f['protocol']);I.verify_solver_contracts(f['protocol'],f['parent']['parent_solver_contract'])
            changed=copy.deepcopy(f['protocol']);changed['solver_contracts']['qdldl_default']['fixed_options']['max_iter']+=1
            with self.assertRaises(ValueError):I.verify_solver_contracts(changed,f['parent']['parent_solver_contract'])
            execution=copy.deepcopy(f['execution']);execution['cost']['memory_budget_bytes']=7*1024**3
            with self.assertRaises(ValueError):I.verify_runtime(execution,f['prep'])

    def test_inventory_unknown_partial_bytes_no_implicit_cache_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary);p=d/'jobs/prepare/source-cache.json.tmp';p.parent.mkdir(parents=True);p.write_bytes(b'x'*70000)
            receipt=dict(files_sha256={str(p.relative_to(d)):I.sha(p)},**I.FLAGS);self.assertTrue(I.verify_inventory(d,receipt))
            (d/'unexpected.json').write_text('{}')
            with self.assertRaises(ValueError):I.verify_inventory(d,receipt)

    def test_whole_audit_one_geometry_and_one_cache_reconstruction(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);d=root/'run';f=self.fixture(d);(d/'frozen_source').mkdir();names=list(f['sources'])
            for n in names:(root/n).write_bytes((R.ROOT/n).read_bytes());(d/'frozen_source'/n).write_bytes((root/n).read_bytes())
            for n in I.INPUTS:write(root/n,dict(files={}) if n.endswith('manifest.json') else dict(schema=15))
            write(d/'protocol.json',f['protocol']);write(d/'source_seal.json',f['sources']);write(d/'input.json',dict(input_sha256={n:I.sha(root/n) for n in I.INPUTS}))
            write(d/'seal.json',{n+'_sha256':I.sha(d/(n+'.json')) for n in ('protocol','source_seal','input')});write(d/'run_started.json',dict(protocol_sha256=I.sha(d/'protocol.json')))
            write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 8 tests in 0.1s\n\nOK\n'));write(d/'preparation-execution.json',f['prep']);write(d/'execution.json',f['execution'])
            files={str(p.relative_to(d)):I.sha(p) for p in d.rglob('*') if p.is_file() and 'frozen_source' not in p.parts};write(d/'receipt.json',dict(files_sha256=files,source_count=len(names),**I.FLAGS))
            with patch.object(I,'ROOT',root),patch.object(I,'source_names',return_value=names),patch.object(I.ORIGINAL,'rebuild',return_value=({},f['geometry'])) as rebuild,patch.object(I,'verify_parent',return_value=f['parent']),patch.object(I.ORIGINAL.B,'gram_specs',return_value={'gram':1}),patch.object(I.CORE.CORE,'reconstruct',wraps=I.CORE.CORE.reconstruct) as reconstruct:
                protocol=f['protocol'];protocol['gram_specs']={'gram':1};write(d/'protocol.json',protocol)
                write(d/'seal.json',{n+'_sha256':I.sha(d/(n+'.json')) for n in ('protocol','source_seal','input')});write(d/'run_started.json',dict(protocol_sha256=I.sha(d/'protocol.json')))
                files={str(p.relative_to(d)):I.sha(p) for p in d.rglob('*') if p.is_file() and 'frozen_source' not in p.parts and p.name!='receipt.json'};write(d/'receipt.json',dict(files_sha256=files,source_count=len(names),**I.FLAGS))
                result=I.audit(d,write=True);self.assertTrue(result['all_passed']);self.assertEqual(rebuild.call_count,1);self.assertEqual(reconstruct.call_count,1)
                self.assertTrue(all(j['cache_verification_reused'] for j in result['jobs']))
                with self.assertRaises(FileExistsError):I.audit(d,write=True)

    def test_no_new_producer_runner_numerical_imports(self):
        tree=ast.parse(Path(I.__file__).read_text());names=[a.name for n in ast.walk(tree) if isinstance(n,ast.Import) for a in n.names]
        for name in ('primitive_state_cached_primal_variants','run_primitive_state_cached_primal_variants','clarabel','numpy','scipy'):self.assertNotIn(name,names)


if __name__=='__main__':unittest.main()
