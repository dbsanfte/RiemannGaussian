import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import publish_cancellation_primitive_state_solver_trace as P
import test_check_primitive_state_solver_trace_run as fixtures


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,sort_keys=True,allow_nan=False))


class PublisherTests(unittest.TestCase):
    def previous(self,phase):
        receipt=dict(original_hash=phase+'-original',original_rows=2,variables=3)
        numerical=dict(transformation_receipt=receipt)
        return dict(program=P.CHECK.PROGRAM,scales=[1,2,3,5],
            **{key:([phase+'-'+key] if key!='gram_specs' else P.CHECK.B.gram_specs()) for key in P.SOURCE_FIELDS},
            synthesis=dict(diagnostics={('proposal_diagnostics' if phase=='dual' else 'numerical_proposal'):numerical}))

    def archive(self,root):
        run=root/'run';prior=root/'previous-run';(run/'frozen_source').mkdir(parents=True);(run/'jobs').mkdir()
        names=['primitive_state_solver_trace.py','primitive_state_numerical_proposals.py']
        for name in names:
            (root/name).write_text('# synthetic sealed source\n');(run/'frozen_source'/name).write_text('# synthetic sealed source\n')
        protocol=fixtures.ArchiveAuditTests().protocol();execution=fixtures.ArchiveAuditTests().execution()
        checks=[]
        for i,phase in enumerate(P.CHECK.PHASES):
            previous=self.previous(phase);write(prior/f'jobs/{phase}-000.json',previous)
            if phase=='dual':
                cost=dict(elapsed_seconds=1.,cpu_seconds=.5,peak_rss_kib=10,observed_threads_at_completion=1,pid=7)
                trace=dict(schema='primitive-state-solver-trace-v1',kind='support',solver=dict(name='scipy-highs',versions={'scipy':'1'},
                    options=dict(time_limit=30.,threads=1,parallel=False,disp=True)),original_vector=[1.,2.,3.],vector_role='raw_failed_last_iterate',
                    termination_status=4,termination_message='synthetic numerical failure',
                    diagnostics={'equality_max_abs':999.},transformation_receipt=P.previous_numerical_receipt(previous),**P.FLAGS)
                write(run/'jobs/dual-trace.json',trace);write(run/'jobs/dual-progress.json',trace)
                record=dict(phase=phase,index=i,program=P.CHECK.PROGRAM,scales=[1,2,3,5],status='trace_available',cost=cost,
                    trace_file='jobs/dual-trace.json',trace_sha256=P.sha(run/'jobs/dual-trace.json'),complete_columns=3,complete_monomials=1,
                    **{key:previous[key] for key in P.SOURCE_FIELDS},**P.FLAGS)
                write(run/'jobs/dual.json',record)
                execution['results'][i]=dict(index=i,status='available',value=dict(file='jobs/dual.json',sha256=P.sha(run/'jobs/dual.json'),
                    status=record['status'],cost=cost,**P.FLAGS))
                check=dict(phase=phase,transport_status='available',worker_status='trace_available',unknown_mathematical_feasibility=True,trace_retained=True,
                    trace_check=dict(verified=True,diagnostics=dict(equality_max_abs=.25,scaled_equality_max_abs=.125,nonnegative_min=1.),
                        coefficient_metrics={'min_nonzero':1.},rounding='synthetic binary64',canonical_system_independently_rebuilt=True,**P.FLAGS),
                    progress=dict(retained=True,terminal_trace_equal=True,partial_only=False),**P.FLAGS)
            else:
                check=dict(phase=phase,transport_status='missing_resource',worker_status=None,unknown_mathematical_feasibility=True,
                    trace_retained=False,trace_check=None,progress=dict(retained=False),**P.FLAGS)
            checks.append(check)
        execution['cost'].update(available=1,missing=1)
        for name,value in [('protocol',protocol),('source_seal',{name:P.sha(root/name) for name in names}),('input',{}),('seal',{}),
                           ('tests',dict(returncode=0,stdout='',stderr='Ran 25 tests in 0.1s\n\nOK\n')),('execution',execution),
                           ('run_started',dict(protocol_sha256=None))]:write(run/(name+'.json'),value)
        write(run/'run_started.json',dict(protocol_sha256=P.sha(run/'protocol.json')))
        self.reseal(run,len(names))
        review=dict(schema='primitive-state-solver-trace-independent-review-v1',all_passed=True,mathematical_feasibility='UNKNOWN',
            numerical_diagnostics_only=True,canonical_primal_matrix_independently_rebuilt=False,arithmetic_rebuilds=1,geometry_rebuilds=1,
            source_count=len(names),complete_original_columns=3,complete_original_monomials=1,redundant_storage_cross_columns=0,checks=checks,
            input_sha256={n:P.sha(run/n) for n in ['protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json']},**P.FLAGS)
        write(run/'independent_verification.json',review)
        return run,prior,names

    def reseal(self,run,count):
        hashes={str(p.relative_to(run)):P.sha(p) for p in run.rglob('*') if p.is_file() and 'frozen_source' not in p.parts and p.name not in ('receipt.json','independent_verification.json')}
        write(run/'receipt.json',dict(files_sha256=hashes,source_count=count,**P.FLAGS))

    def contexts(self,root,run,prior,names):
        import run_primitive_state_solver_trace as runner
        return [patch.object(P,'ROOT',root),patch.object(P,'RUN',run),patch.object(P.OLD,'RUN',prior),
                patch.object(runner,'validate',return_value=None),patch.object(runner,'sources',return_value=names),
                patch.object(P.CHECK,'source_names',return_value=names)]

    def completed(self,root,run,prior,names):
        import contextlib
        with contextlib.ExitStack() as stack:
            for context in self.contexts(root,run,prior,names):stack.enter_context(context)
            return P.completed_archive()

    def test_failed_raw_iterate_publication_uses_independent_metrics(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);run,prior,names=self.archive(root)
            stage=self.completed(root,run,prior,names)
            with patch.object(P,'RUN',run):report=P.report(dict(stage=stage,priors={}))
            self.assertEqual(report['jobs'][0]['archived_vector_independent_residuals_and_signs']['equality_max_abs'],.25)
            self.assertEqual(report['jobs'][0]['termination_status'],4)
            self.assertEqual(report['jobs'][1]['transport_status'],'missing_resource')
            self.assertEqual(report['mathematical_feasibility'],'UNKNOWN')
            self.assertFalse(report['critical_finite_certificate_found']);self.assertFalse(report['infeasibility_proved'])
            self.assertEqual(report['resources']['worker_memory_bytes'],3*1024**3)
            self.assertEqual(report['resources']['cooperative_seconds'],900)
            self.assertTrue(report['jobs'][0]['unchanged_source_comparisons']['original_equations_compared'])
            self.assertTrue(not (root/'publication-012').exists())

    def test_changed_original_system_rejected(self):
        previous=self.previous('dual');record={key:previous[key] for key in P.SOURCE_FIELDS}
        record.update(program=previous['program'],scales=previous['scales'])
        trace=dict(transformation_receipt=P.previous_numerical_receipt(previous))
        self.assertTrue(P.unchanged_sources(record,trace,previous)['original_equations_compared'])
        for key in P.SOURCE_FIELDS:
            bad=copy.deepcopy(record);bad[key]=['changed']
            with self.assertRaises(ValueError):P.unchanged_sources(bad,trace,previous)
        for key in ('original_hash','original_rows','variables'):
            bad=copy.deepcopy(trace);bad['transformation_receipt'][key]='changed'
            with self.assertRaises(ValueError):P.unchanged_sources(record,bad,previous)

    def test_missing_or_nonindependent_review_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);run,prior,names=self.archive(root)
            path=run/'independent_verification.json';original=P.read(path)
            for key,value in [('all_passed',False),('mathematical_feasibility','infeasible'),('canonical_primal_matrix_independently_rebuilt',True),('certified',True)]:
                bad=copy.deepcopy(original);bad[key]=value;write(path,bad)
                with self.assertRaises(ValueError):self.completed(root,run,prior,names)
            write(path,original);path.unlink()
            with self.assertRaises(FileNotFoundError):self.completed(root,run,prior,names)

    def test_review_and_receipt_tampering_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);run,prior,names=self.archive(root)
            review=run/'independent_verification.json';original=P.read(review)
            bad=copy.deepcopy(original);bad['input_sha256'].pop('receipt.json');write(review,bad)
            with self.assertRaises(ValueError):self.completed(root,run,prior,names)
            write(review,original);(run/'jobs/dual-trace.json').write_text('{}')
            with self.assertRaises(ValueError):self.completed(root,run,prior,names)

    def test_status_and_exact_proof_promotion_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);run,prior,names=self.archive(root)
            path=run/'independent_verification.json';original=P.read(path)
            for key,value in [('transport_status','missing_resource'),('worker_status','finite_PSD_certificate')]:
                bad=copy.deepcopy(original);bad['checks'][0][key]=value;write(path,bad)
                with self.assertRaises(ValueError):self.completed(root,run,prior,names)
            bad=copy.deepcopy(original);bad['checks'][0]['trace_check']['certified']=True;write(path,bad)
            with self.assertRaises(ValueError):self.completed(root,run,prior,names)

    def test_synthetic_publication_binds_new_sources_and_updates_pointer(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);base=root/'results';previous=base/'publication-011';previous.mkdir(parents=True)
            run=base/'run';run.mkdir()
            for name in [P.NOTE,P.SELF,P.TEST,'source.py']:(root/name).write_text('# synthetic publication input\n')
            write(previous/'manifest.json',{'files':{}});write(previous/'report.json',{'schema':11})
            oldpointer=dict(publication='publication-011',manifest_sha256=P.sha(previous/'manifest.json'),report_sha256=P.sha(previous/'report.json'))
            write(base/'latest.json',oldpointer);write(run/'receipt.json',{})
            inputs=dict(stage=dict(source={'source.py':P.sha(root/'source.py')}),coordinate_supplement=dict(source={}))
            with patch.object(P,'ROOT',root),patch.object(P,'BASE',base),patch.object(P,'RUN',run),patch.object(P,'SUPPLEMENT',root/'synthetic-supplement'),patch.object(P,'PREVIOUS',previous),\
                 patch.object(P,'load_inputs',return_value=inputs),patch.object(P,'publisher_sources',return_value=[P.SELF,P.TEST]),\
                 patch.object(P,'report',return_value=dict(schema=12,diagnostic_only=True,**P.FLAGS)):
                result=P.publish()
            self.assertEqual(result['publication'],'publication-012')
            out=base/'publication-012';manifest=P.read(out/'manifest.json');P.bind(root,manifest['files'])
            for name in [P.SELF,P.TEST,'source.py',P.NOTE]:self.assertIn(name,manifest['files'])
            self.assertEqual((out/P.NOTE).read_bytes(),(root/P.NOTE).read_bytes())
            self.assertEqual((out/'frozen_source'/P.SELF).read_bytes(),(root/P.SELF).read_bytes())
            pointer=P.read(base/'latest.json');self.assertEqual(pointer['manifest_sha256'],P.sha(out/'manifest.json'))
            self.assertEqual(pointer['publication'],'publication-012');self.assertFalse(pointer['infeasibility_proved'])

    def supplement(self,root):
        import test_check_primitive_state_raw_iterate as raw_fixtures
        run=root/'run';supplement=root/'supplement';(supplement/'frozen_source').mkdir(parents=True)
        trace=raw_fixtures.fixture();trace['transformation_receipt']=dict(original_rows=2,variables=5,retained_indices=[0,1],original_hash='exact-original')
        trace.update(original_system_hash='original-system',termination_status='synthetic-failure')
        for name in ['receipt.json','independent_verification.json','protocol.json','source_seal.json','jobs/primal-trace.json','jobs/primal.json']:
            write(run/name,trace if name=='jobs/primal-trace.json' else {})
        source={}
        for name in P.RAW_SOURCES:
            (root/name).write_text('# synthetic replay source\n');(supplement/'frozen_source'/name).write_bytes((root/name).read_bytes())
            source[name]=P.sha(root/name)
        coordinate=P.RAW.replay(trace)
        corrected=dict(verified=True,canonical_system_independently_rebuilt=False,transformation=dict(original_rows=2,reduced_rows=2,variables=5),
            diagnostics=dict(nonnegative_min=-3.,equality_max_abs=.5),rounding='binary64 synthetic',**P.FLAGS)
        report=dict(schema='primitive-state-native-coordinate-independent-review-v1',all_passed=True,canonical_matrix_independently_rebuilt=False,
            source_sha256=source,input_sha256={str(p.relative_to(root)):P.sha(p) for p in run.rglob('*') if p.is_file()},
            tests_passed=7,full_arithmetic_rebuilds=1,geometry_rebuilds=1,canonical_variable_map_independently_derived=False,
            original_trace_modified=False,solver_rerun=False,refitted=False,numerical_diagnostics_only=True,mathematical_feasibility='UNKNOWN',
            scalar_projection_was_applied_to_archived_vector=True,original_trace_sha256=P.sha(run/'jobs/primal-trace.json'),
            original_system_hash=trace['original_system_hash'],exact_equation_source_hash='exact-original',native_termination_status=trace['termination_status'],
            coordinate_replay=coordinate,corrected_original_equation_check=corrected,**P.FLAGS)
        write(supplement/'input.json',dict(source_sha256=source,input_sha256=report['input_sha256'],**P.FLAGS))
        write(supplement/'report.json',report);write(supplement/'tests.json',dict(returncode=0,stdout='',stderr='Ran 7 tests in 0.1s\n\nOK\n'))
        self.supplement_seal(supplement)
        return run,supplement,report

    def supplement_seal(self,supplement):
        write(supplement/'seal.json',dict(files_sha256={str(p.relative_to(supplement)):P.sha(p) for p in supplement.rglob('*') if p.is_file() and p.name!='seal.json'},**P.FLAGS))

    def test_native_coordinate_supplement_binds_projection_and_raw_signs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);run,supplement,report=self.supplement(root)
            with patch.object(P,'ROOT',root),patch.object(P,'RUN',run),patch.object(P,'SUPPLEMENT',supplement):
                result=P.coordinate_supplement()
                self.assertEqual(result['report']['coordinate_replay']['changed_coordinate_count'],1)
                self.assertEqual(result['report']['corrected_original_equation_check']['diagnostics']['nonnegative_min'],-3.)
                self.assertEqual(result['tests_passed'],7)
                for mode in ('raw-vector','sign','canonical-claim','missing-input'):
                    bad=copy.deepcopy(report)
                    if mode=='raw-vector':bad['coordinate_replay']['original_vector'][0]=0.
                    elif mode=='sign':bad['corrected_original_equation_check']['diagnostics']['nonnegative_min']=0.
                    elif mode=='canonical-claim':bad['canonical_matrix_independently_rebuilt']=True
                    else:bad['input_sha256'].pop(next(iter(bad['input_sha256'])))
                    write(supplement/'report.json',bad);self.supplement_seal(supplement)
                    with self.assertRaises(ValueError):P.coordinate_supplement()

    def test_missing_native_coordinate_supplement_cannot_publish(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(P,'SUPPLEMENT',Path(temporary)/'missing'):
                with self.assertRaises(FileNotFoundError):P.coordinate_supplement()

    def test_publish_requires_correct_latest_parent_before_writes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);base=root/'results';previous=base/'publication-011';previous.mkdir(parents=True)
            write(previous/'manifest.json',{});write(previous/'report.json',{})
            write(base/'latest.json',dict(publication='publication-010',manifest_sha256='bad',report_sha256='bad'))
            with patch.object(P,'BASE',base),patch.object(P,'PREVIOUS',previous),patch.object(P,'load_inputs',return_value={}):
                with self.assertRaises(ValueError):P.publish()
            self.assertFalse((base/'publication-012').exists())
            self.assertEqual(P.read(base/'latest.json')['publication'],'publication-010')

if __name__=='__main__':unittest.main()
