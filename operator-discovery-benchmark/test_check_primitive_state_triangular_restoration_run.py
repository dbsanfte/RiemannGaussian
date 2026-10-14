import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_primitive_state_triangular_restoration_run as C
import run_primitive_state_triangular_restoration as R
import test_check_primitive_state_triangular_restoration as FIXTURE


class WholeRestorationTests(unittest.TestCase):
    def fixture(self):return FIXTURE.FullRestorationTests().fixture()
    def test_literal_protocol_sources_and_resource_alignment(self):
        license={'fixture':True};C.verify_protocol(R.protocol(license),license)
        self.assertEqual(C.LIMITS,R.LIMITS);self.assertEqual(C.INPUTS,R.INPUTS);self.assertEqual(C.TESTS,R.TESTS);self.assertEqual(C.source_names(),R.sources())
        bad=R.protocol(license);bad['original_objective_preserved']=True
        with self.assertRaises(ValueError):C.verify_protocol(bad,license)
    def test_complete_pipeline_and_external_failed_transport(self):
        args=self.fixture();reserve=1000
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);folder=d/'jobs';folder.mkdir()
            out=R.process_restore(*args[:4],directory=folder,deadline=__import__('time').monotonic()+30,input_work_reserve=reserve)
            self.assertEqual(out['status'],'restoration_verified')
            record=dict(out,phase='restore',index=0,parent_license={},input_work_reserve=reserve,cost=dict(elapsed_seconds=1,cpu_seconds=1,peak_rss_kib=1,pid=1,observed_threads_at_completion=1),deadline_exceeded=False)
            R.SOURCE.bounded_write(folder/'restoration-job.json',record,65536)
            row=dict(status='available',value=dict(file='jobs/restoration-job.json',sha256=C.sha(folder/'restoration-job.json'),status=record['status'],cost=record['cost'],**C.FLAGS))
            check=C.read(folder/'check.json');cells=sum(map(len,args[0]['original']['columns']))+len(args[0]['original']['rhs'])
            good=C.verify_job(d,row,reserve,cells,check,{})
            self.assertTrue(good['restoration_verified']);self.assertTrue(good['finite_candidate_feasible'])
            failed=C.verify_job(d,dict(status='missing_resource'),reserve,cells,check,{})
            self.assertFalse(failed['restoration_verified']);self.assertIsNone(failed['finite_candidate_feasible'])
            record['deadline_exceeded']=True;R.SOURCE.bounded_write(folder/'restoration-job.json',record,65536)
            row['value']['sha256']=C.sha(folder/'restoration-job.json')
            late=C.verify_job(d,row,reserve,cells,check,{})
            self.assertFalse(late['restoration_verified']);self.assertIsNone(late['finite_candidate_feasible'])
    def test_pending_written_check_has_full_reserve(self):
        args=self.fixture()
        with tempfile.TemporaryDirectory() as tmp:
            out=R.process_restore(*args[:4],directory=tmp,deadline=__import__('time').monotonic()+30,input_work_reserve=1000)
            check=C.read(Path(tmp)/'check.json');ledger=copy.deepcopy(out['ledger']);last=ledger['entries'][-1]
            last.update(precision='allocated_unverified',reserve=last['allocation'],charged_operations=None)
            ledger.update(total_work_reserve=450000000,remaining_work=0)
            value=C.verify_ledger(ledger,1000,check,2);self.assertFalse(value['all_stages_committed']);self.assertEqual(value['total_work_reserve'],450000000)
            ledger['entries'][1]['reserve']-=1
            with self.assertRaises(ValueError):C.verify_ledger(ledger,1000,check,2)
    def test_inventory_nested_receipt_and_unbound_temporary(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);(d/'jobs').mkdir();(d/'jobs/restoration.json.tmp').write_text('{}')
            receipt=dict(files_sha256={'jobs/restoration.json.tmp':C.sha(d/'jobs/restoration.json.tmp')},**C.FLAGS)
            self.assertFalse(C.verify_inventory(d,receipt)['temporary_files_are_evidence'])
            (d/'jobs/receipt.json').write_text('{}')
            with self.assertRaises(ValueError):C.verify_inventory(d,receipt)
            receipt['files_sha256']['jobs/receipt.json']=C.sha(d/'jobs/receipt.json')
            with self.assertRaises(ValueError):C.verify_inventory(d,receipt)
            (d/'jobs/receipt.json').unlink();del receipt['files_sha256']['jobs/receipt.json']
            (d/'jobs/frozen_source').mkdir();(d/'jobs/frozen_source/rogue').write_text('x')
            with self.assertRaises(ValueError):C.verify_inventory(d,receipt)
    def test_runtime_thread_memory_and_order_tampering(self):
        e=dict(results=[dict(index=0,status='missing_resource')],cost=dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=1,result_bytes=1,payload_bytes=1,available=0,missing=1,errors=0))
        C.verify_runtime(e)
        for k,v in [('workers',2),('numerical_threads_per_worker',2),('worker_memory_bytes',6*1024**3)]:
            bad=copy.deepcopy(e);bad['cost'][k]=v
            with self.assertRaises(ValueError):C.verify_runtime(bad)
    def test_whole_audit_caps_rejected_before_io(self):
        for kw in ({'time_limit':901},{'time_limit':True},{'max_audit_operations':450000001},{'max_audit_operations':0},{'max_audit_operations':True},{'max_audit_cells':60000001},{'max_audit_cells':False}):
            with self.assertRaises(ValueError):C.audit('/nonexistent/restoration',**kw)
    def test_archive_io_proxy_and_cap(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'x.json';p.write_text('{}')
            b=C.CORE.EXACT._Budget(None,1000,1000,4096);token=C._IO_BUDGET.set(b)
            try:C.read(p);C.sha(p)
            finally:C._IO_BUDGET.reset(token)
            self.assertEqual(b.operations,3);self.assertEqual(b.cells,1)
            with self.assertRaises(ValueError):C.read(p,1)
    def test_complete_archive_single_binding_and_replay_exclusive_review(self):
        from fractions import Fraction as F
        import primitive_state_equation_projection as PROJ
        import primitive_state_exact_row_basis as BASIS
        import time
        domain=[(i,) for i in range(5641)];n=1957;shape=[366,613];offset=1597
        specs={'full_child':15,'full_parent':15,'storage_K':15};retained,recipes,_=C.CORE.derive_projection(shape,offset,specs,n)
        columns=[{} for _ in range(n)];lhs={domain[i]:F(1) for i in range(779)}
        for i,j in enumerate(retained[:779]):columns[j][domain[i]]=F(1)
        for i in range(779,5641):columns[0][domain[i]]=F(1);lhs[domain[i]]=F(1)
        for j,recipe in recipes.items():
            for k,q in recipe.items():
                for m,v in columns[k].items():columns[j][m]=q*v
        rows,rhs,projection=PROJ.project_equations(columns,lhs,domain,retained,recipes,deadline=time.monotonic()+30)
        _,_,basis=BASIS.reduce_rows(rows,rhs,len(retained),deadline=time.monotonic()+30)
        cache={'original':dict(columns=[[[m[0],str(v)] for m,v in sorted(col.items())] for col in columns],rhs=[str(lhs.get(m,F(0))) for m in domain],monomials=[list(m) for m in domain],shape=shape,offset=offset,specs=[[k,v] for k,v in sorted(specs.items())],selected_original_indices=list(range(779)))}
        trace={'original_vector':[0.0]*n}
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);d=root/'run';d.mkdir();(d/'jobs').mkdir();(d/'frozen_source').mkdir()
            (root/'synthetic.py').write_text('VALUE=1\n');(d/'frozen_source/synthetic.py').write_bytes((root/'synthetic.py').read_bytes())
            inputnames=['cache.json','trace.json','basis.json','projection.json']
            for name,value in zip(inputnames,(cache,trace,basis,projection)):(root/name).write_bytes(C.CORE.encoded(value))
            source={'synthetic.py':C.sha(root/'synthetic.py')};license={'input_file_hashes':{name:C.sha(root/name) for name in inputnames}}
            reserve=4*sum((root/name).stat().st_size for name in inputnames)+12*(root/'synthetic.py').stat().st_size+1048576+1
            protocol=R.protocol(license);inputs=dict(input_sha256=license['input_file_hashes'],binding_work_reserve=reserve)
            for name,value in [('protocol',protocol),('source_seal',source),('input',inputs)]:R.SOURCE.bounded_write(d/(name+'.json'),value,65536)
            R.SOURCE.bounded_write(d/'seal.json',{name+'_sha256':C.sha(d/(name+'.json')) for name in ('protocol','source_seal','input')},65536)
            R.SOURCE.bounded_write(d/'run_started.json',dict(protocol_sha256=C.sha(d/'protocol.json')),65536)
            R.SOURCE.bounded_write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 1 test in 0.1s\n\nOK\n'),65536)
            out=R.process_restore(cache,trace,basis,projection,directory=d/'jobs',deadline=time.monotonic()+30,input_work_reserve=reserve)
            self.assertEqual(out['status'],'restoration_verified')
            cost=dict(elapsed_seconds=1,cpu_seconds=1,peak_rss_kib=1,pid=1,observed_threads_at_completion=1)
            record=dict(out,phase='restore',index=0,parent_license=license,input_work_reserve=reserve,cost=cost,deadline_exceeded=False)
            R.SOURCE.bounded_write(d/'jobs/restoration-job.json',record,65536)
            execution=dict(results=[dict(index=0,status='available',value=dict(file='jobs/restoration-job.json',sha256=C.sha(d/'jobs/restoration-job.json'),status=record['status'],cost=cost,**C.FLAGS))],cost=dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=1,result_bytes=1,payload_bytes=1,available=1,missing=0,errors=0))
            R.SOURCE.bounded_write(d/'execution.json',execution,65536)
            inventory={str(p.relative_to(d)):C.sha(p) for p in d.rglob('*') if p.is_file() and 'frozen_source' not in p.parts}
            R.SOURCE.bounded_write(d/'receipt.json',dict(files_sha256=inventory,source_count=1,**C.FLAGS),65536)
            with patch.object(C,'ROOT',root),patch.object(C,'INPUTS',inputnames),patch.object(C,'CACHE','cache.json'),patch.object(C,'TRACE','trace.json'),patch.object(C,'BASIS','basis.json'),patch.object(C,'PROJECTION','projection.json'),patch.object(C,'source_names',return_value=['synthetic.py']),patch.object(C,'verify_parent',return_value=(license,309,285)) as parent,patch.object(C.CORE,'verify_restoration',wraps=C.CORE.verify_restoration) as replay:
                result=C.audit(d,write=True);self.assertTrue(result['job']['restoration_verified']);self.assertTrue(result['job']['finite_candidate_feasible'])
                self.assertEqual(parent.call_count,1);self.assertEqual(replay.call_count,1)
                with self.assertRaises(FileExistsError):C.audit(d,write=True)
                self.assertEqual(parent.call_count,1);self.assertEqual(replay.call_count,1)
    def test_auditor_does_not_import_new_producer_runner_or_solver(self):
        tree=__import__('ast').parse(Path(C.__file__).read_text());imports=[]
        for node in __import__('ast').walk(tree):
            if isinstance(node,__import__('ast').Import):imports.extend(a.name for a in node.names)
            elif isinstance(node,__import__('ast').ImportFrom):imports.append(node.module)
        self.assertFalse(set(imports)&{'run_primitive_state_triangular_restoration','primitive_state_triangular_restoration','numpy','scipy','clarabel','cvxpy'})

if __name__=='__main__':unittest.main()
