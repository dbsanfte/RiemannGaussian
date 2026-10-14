import copy
from fractions import Fraction as F
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_free_cone_search_run as C
import run_primitive_state_free_cone_search as R
import test_run_primitive_state_free_cone_search as FIXTURE


class WholeFreeSearchTests(unittest.TestCase):
    def cost(self):return dict(elapsed_seconds=1,cpu_seconds=1,peak_rss_kib=1,pid=1,observed_threads_at_completion=1)
    def test_actual_parent_protocol_and_source_resource_literals(self):
        license=R.load_license();C.verify_protocol(R.protocol(license),license)
        self.assertEqual(C.INPUTS,R.INPUTS);self.assertEqual(C.LIMITS,R.LIMITS);self.assertEqual(C.TESTS,R.TESTS);self.assertEqual(C.source_names(),R.sources())
        bad=copy.deepcopy(R.protocol(license));bad['precision']['PSD_eigh']='80digits'
        with self.assertRaises(ValueError):C.verify_protocol(bad,license)
    def pipeline(self,d,license,reserve=1000):
        (d/'jobs').mkdir(exist_ok=True)
        out=R.process_search(license,directory=d/'jobs',deadline=time.monotonic()+30,input_work_reserve=reserve)
        record=dict(out,phase='search',index=0,parent_license={},input_work_reserve=reserve,cost=self.cost(),deadline_exceeded=False)
        R.SOURCE.bounded_write(d/'jobs/search-job.json',record,65536)
        row=dict(status='available',value=dict(file='jobs/search-job.json',sha256=C.sha(d/'jobs/search-job.json'),status=record['status'],cost=record['cost'],**C.FLAGS))
        return record,row,C.read(d/'jobs/check.json')
    def test_endpoint_available_external_failure_and_deadline(self):
        license=FIXTURE.synthetic_license()
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);record,row,check=self.pipeline(d,license)
            out=C.verify_job(d,row,1000,license.source['source_cells'],check,{})
            self.assertTrue(out['endpoint_verified']);self.assertTrue(out['finite_candidate_feasible'])
            out=C.verify_job(d,dict(status='missing_resource'),1000,license.source['source_cells'],check,{})
            self.assertFalse(out['endpoint_verified']);self.assertIsNone(out['finite_candidate_feasible'])
            record.update(status='missing_resource',endpoint_verified=False,finite_candidate_feasible=None,deadline_exceeded=True)
            R.SOURCE.bounded_write(d/'jobs/search-job.json',record,65536);row['value'].update(status=record['status'],sha256=C.sha(d/'jobs/search-job.json'))
            out=C.verify_job(d,row,1000,license.source['source_cells'],check,{})
            self.assertFalse(out['endpoint_verified']);self.assertTrue(out['deadline_exceeded'])
    def test_pending_check_reservation_and_producer_refinement_tamper(self):
        license=FIXTURE.synthetic_license()
        with tempfile.TemporaryDirectory() as tmp:
            record,row,check=self.pipeline(Path(tmp),license);ledger=copy.deepcopy(record['ledger']);last=ledger['entries'][-1]
            last.update(reserve=last['allocation'],charged_operations=None,precision='allocated_unverified');ledger.update(total_work_reserve=450000000,remaining_work=0)
            out=C.verify_ledger(ledger,1000,check,license.source['source_cells']);self.assertFalse(out['all_stages_committed']);self.assertEqual(out['total_work_reserve'],450000000)
            ledger['entries'][2].update(precision='independently_verified',reserve=1,charged_operations=1)
            with self.assertRaises(ValueError):C.verify_ledger(ledger,1000,check,license.source['source_cells'])
    def test_bound_check_and_trace_tampering(self):
        license=FIXTURE.synthetic_license()
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);record,row,check=self.pipeline(d,license)
            changed=copy.deepcopy(check);changed['finite_candidate_feasible']=False
            R.SOURCE.bounded_write(d/'jobs/check.json',changed,8388608)
            with self.assertRaises(ValueError):C.verify_job(d,row,1000,license.source['source_cells'],check,{})
    def test_caps_and_exclusive_write_are_early(self):
        for kw in ({'time_limit':901},{'time_limit':True},{'max_audit_operations':False},{'max_audit_operations':450000001},{'max_audit_cells':60000001}):
            with self.assertRaises(ValueError):C.audit('/missing/fixture',**kw)
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp)/'independent_verification.json').write_text('{}')
            with patch.object(C.CORE,'load_verified_license',side_effect=AssertionError('expensive license call')):
                with self.assertRaises(FileExistsError):C.audit(tmp,write=True)
    def test_unknown_outer_failure_stale_progress_preserves_reserves(self):
        license=FIXTURE.synthetic_license()
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);record,row,check=self.pipeline(d,license)
            record.update(status='missing_resource',endpoint_verified=False,finite_candidate_feasible=None);record.pop('ledger')
            R.SOURCE.bounded_write(d/'jobs/search-job.json',record,65536);row['value'].update(status='missing_resource',sha256=C.sha(d/'jobs/search-job.json'))
            out=C.verify_job(d,row,1000,license.source['source_cells'],check,{})
            self.assertFalse(out['endpoint_verified']);self.assertTrue(out['lifecycle']['outer_partial_failure'])
    def test_inventory_exact_root_exclusions_and_tmp_caps(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);(d/'jobs').mkdir();p=d/'jobs/proposal.json.tmp';p.write_text('{}')
            receipt=dict(files_sha256={'jobs/proposal.json.tmp':C.sha(p)},**C.FLAGS)
            self.assertFalse(C.verify_inventory(d,receipt)['temporary_files_are_evidence'])
            (d/'jobs/receipt.json').write_text('{}')
            with self.assertRaises(ValueError):C.verify_inventory(d,receipt)
            receipt['files_sha256']['jobs/receipt.json']=C.sha(d/'jobs/receipt.json')
            with self.assertRaises(ValueError):C.verify_inventory(d,receipt)
    def test_full_synthetic_archive_one_license_and_endpoint_pass(self):
        import primitive_state_equation_projection as PROJ
        import primitive_state_exact_row_basis as BASIS
        domain=[(i,) for i in range(5641)];shape=[366,613];offset=1597;n=1957
        specs={'full_child':15,'full_parent':15,'storage_K':15};retained,recipes,_=C.CORE.EXACT.derive_projection(shape,offset,specs,n)
        columns=[{} for _ in range(n)];lhs={domain[i]:F(1) for i in range(779)}
        for i,j in enumerate(retained[:779]):columns[j][domain[i]]=F(1)
        for i in range(779,5641):columns[0][domain[i]]=F(1);lhs[domain[i]]=F(1)
        for j,recipe in recipes.items():
            for k,q in recipe.items():
                for m,v in columns[k].items():columns[j][m]=q*v
        rows,rhs,projection=PROJ.project_equations(columns,lhs,domain,retained,recipes,deadline=time.monotonic()+30)
        _,_,basis=BASIS.reduce_rows(rows,rhs,len(retained),deadline=time.monotonic()+30)
        cache={'original':dict(columns=[[[m[0],str(v)] for m,v in sorted(col.items())] for col in columns],rhs=[str(lhs.get(m,F(0))) for m in domain],monomials=[list(m) for m in domain],shape=shape,offset=offset,specs=[[k,v] for k,v in sorted(specs.items())],selected_original_indices=list(range(779)))}
        trace={'original_vector':[0.0]*n};parent=R.P.EXACT.restore(cache,trace,basis,projection,deadline=time.monotonic()+30)
        budget=C.CORE.EXACT.EXACT._Budget(None,10000000,10000000,4096);source=C.CORE.CACHE_CHECK.decode_original(cache,budget)
        pivots=basis['pivot_columns'];free=[i for i in range(1224) if i not in pivots];vector=list(map(F,parent['restored_projected_vector']))
        summary=dict(normalized_basis_hash=parent['normalized_basis_hash'],rank=779,free_count=445,original_variables=1957,original_rows=5641,projected_variables=1224,retained_indices=retained,parent_projected_hash=C.CORE.digest(parent['restored_projected_vector']),parent_free_hash=C.CORE.digest([parent['restored_projected_vector'][i] for i in free]),audit_operations=1,audit_cells=1)
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);d=root/'run';d.mkdir();(d/'jobs').mkdir();(d/'frozen_source').mkdir()
            for name in C.INPUTS:
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('{}')
            for name,value in [(C.CACHE,cache),(C.BASIS,basis),(C.PROJECTION,projection),(C.PARENT+'/jobs/restoration.json',parent),(C.CORE.MANIFEST,{'files':{'fixture':'abc'}})]:
                (root/name).write_bytes(C.CORE.encoded(value))
            bindings={name:C.sha(root/name) for name in C.INPUTS}
            license=C.CORE._EndpointLicense(C.CORE._TOKEN,source,summary,vector,pivots,free,bindings,cache=cache,basis=basis,projection=projection,parent_restoration=parent)
            protocol_license=C.parent_protocol_license(license)
            (root/'synthetic.py').write_text('VALUE=1\n');(d/'frozen_source/synthetic.py').write_bytes((root/'synthetic.py').read_bytes());sources={'synthetic.py':C.sha(root/'synthetic.py')}
            reserve=4*sum((root/name).stat().st_size for name in C.INPUTS)+12*(root/'synthetic.py').stat().st_size+1048576+1
            for name,value in [('protocol',R.protocol(protocol_license)),('source_seal',sources),('input',dict(input_sha256=bindings,binding_work_reserve=reserve))]:R.SOURCE.bounded_write(d/(name+'.json'),value,65536)
            R.SOURCE.bounded_write(d/'seal.json',{name+'_sha256':C.sha(d/(name+'.json')) for name in ('protocol','source_seal','input')},65536)
            R.SOURCE.bounded_write(d/'run_started.json',dict(protocol_sha256=C.sha(d/'protocol.json')),65536)
            R.SOURCE.bounded_write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 1 test in 0.1s\n\nOK\n'),65536)
            out=R.process_search(license,directory=d/'jobs',deadline=time.monotonic()+30,input_work_reserve=reserve);self.assertEqual(out['status'],'endpoint_verified',out.get('reason'))
            record=dict(out,phase='search',index=0,parent_license=protocol_license,input_work_reserve=reserve,license_loader_cost=dict(audit_operations=1,audit_cells=1),cost=self.cost(),deadline_exceeded=False)
            R.SOURCE.bounded_write(d/'jobs/search-job.json',record,65536)
            execution=dict(results=[dict(index=0,status='available',value=dict(file='jobs/search-job.json',sha256=C.sha(d/'jobs/search-job.json'),status=record['status'],cost=record['cost'],**C.FLAGS))],cost=dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=1,result_bytes=1,payload_bytes=1,available=1,missing=0,errors=0))
            R.SOURCE.bounded_write(d/'execution.json',execution,65536)
            files={str(p.relative_to(d)):C.sha(p) for p in d.rglob('*') if p.is_file() and 'frozen_source' not in p.parts}
            R.SOURCE.bounded_write(d/'receipt.json',dict(files_sha256=files,source_count=1,**C.FLAGS),65536)
            with patch.object(C,'ROOT',root),patch.object(C,'source_names',return_value=['synthetic.py']),patch.object(C.CORE,'load_verified_license',return_value=license) as loader,patch.object(C.CORE,'verify_search',wraps=C.CORE.verify_search) as endpoint_replay:
                result=C.audit(d,write=True);self.assertTrue(result['job']['endpoint_verified']);self.assertTrue(result['job']['finite_candidate_feasible'])
                self.assertEqual(loader.call_count,1);self.assertEqual(endpoint_replay.call_count,1);self.assertFalse(result['full_elimination_replayed'])
                self.assertEqual(set(result['input_sha256']),{'protocol','source_seal','input','seal','tests','execution','receipt'})
                with self.assertRaises(FileExistsError):C.audit(d,write=True)
                self.assertEqual(loader.call_count,1)
    def test_no_producer_or_numerical_library_imports(self):
        import ast
        for module in (C,C.CORE):
            imports=[]
            for node in ast.walk(ast.parse(Path(module.__file__).read_text())):
                if isinstance(node,ast.Import):imports.extend(a.name for a in node.names)
                elif isinstance(node,ast.ImportFrom):imports.append(node.module)
            self.assertFalse(set(imports)&{'primitive_state_free_cone_search','run_primitive_state_free_cone_search','mpmath','numpy','scipy','clarabel','cvxpy'})

if __name__=='__main__':unittest.main()
