"""Saved36 uniform rank-admission bindings; no mathematical/scientific replay."""
import json,time
from fractions import Fraction as Q
import run_mobius_dense_completion_082 as R
import run_mobius_dense_rank_obstruction_082 as FOLLOW

def load(path):return json.loads(path.read_text())
def require(ok,reason):
    if not ok:raise ValueError(reason)

def main():
    start=time.monotonic();target=R.OUT/'saved_rank_artifact_admission_082_attempt002.json'
    if target.exists():raise FileExistsError('preserve audit attempt')
    result=dict(schema='saved-rank-artifact-audit-v1',scientific_or_mathematical_admissions_replayed=False,new_source_values_queried=False,hashes_used=False)
    try:
        require(load(R.OUT/'saved_artifact_admission_082.json')['status']=='VERIFIED_SAVED_DENSE_ARTIFACT_BINDING','main audit receipt')
        require(sum(R.validate_parent())==566,'older provenance')
        for name in R.FILES:require((R.ROOT/name).read_bytes()==(R.OUT/'source_snapshot'/name).read_bytes(),'main frozen '+name)
        for name in FOLLOW.FILES:require((R.ROOT/name).read_bytes()==(R.OUT/'rank_source_snapshot'/name).read_bytes(),'rank frozen '+name)
        roster=load(R.OUT/'frozen_task_roster.json');rank=load(R.OUT/'rank_obstruction_results.json');rows=rank['rows'];require(len(rows)==36 and len({r['id'] for r in rows})==36,'36 unique rows')
        expected={}
        for t in roster['tasks']:
            search=load(R.OUT/('search_'+t['id']+'.json'));expected[t['id']]=(t['source_id'],search['program'])
        for i,t in enumerate(roster['sublinear_obstructions']):expected['sublinear_'+str(i).zfill(2)]=(t['source_id'],t['program'])
        require(set(expected)=={r['id'] for r in rows},'complete roster IDs')
        integration=load(R.ROOT/'mobius_dense_rank_obstruction_independent_audit_082.json');require(integration['status']=='PASS' and integration['case_count']==24,'retained integration receipt')
        cases={(r['source'],r['memory'],r['family']):r for r in integration['cases']};families={f['id']:i for i,f in enumerate(R.families())};tasks={t['id']:t for t in roster['tasks']}
        for row in rows:
            source,p=expected[row['id']];require(row['source_id']==source and row['program']==p,'exact LP/sublinear program binding')
            cert,a=row['certificate'],row['admission'];require(cert['schema']=='dense-rank-interval-v1' and a['status']=='VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION','certificate admission schema')
            for k in ('tau','threshold','H00','lower_coefficient'):require(cert[k]==a[k],'admission '+k)
            require(Q(cert['tau'])>0 and Q(cert['lower_coefficient'])==Q(cert['H00'])*Q(cert['tau'])**2,'positive exact lower coefficient')
            H=Q(1)+sum((Q(r['weight'])*Q(r['a'][0])**2 for r in p['rays']),Q(0));require(H==Q(cert['H00']),'exact energy binding')
            intervals=cert['intervals'];require(len(intervals)==a['interval_count'],'interval count')
            require(a['source_moments']==['1']+['0']*p['memory'] and a['profile_moments']==['0']*len(p['profiles']),'admitted null moments')
            for i in range(p['memory']+1):require(sum(Q(v['t'])*Q(v['source'][i]) for v in intervals)==int(i==0),'saved exact source moment')
            for j in range(len(p['profiles'])):require(sum(Q(v['t'])*v['profiles'][j] for v in intervals)==0,'saved exact profile moment')
            previous=Q(0)
            for v in intervals:
                l,h,t=Q(v['left']),Q(v['right']),Q(v['t']);require(previous<=l<h and t!=0,'interval ordering/disjoint/nonzero')
                require(Q(cert['tau'])<=(h-l)/(4*abs(t)),'population feasibility tau');previous=h
            require(a['uniform_completion_price_obstruction_proved'] is True and a['actual_arithmetic_drift_refuted'] is False and a['uniform_source_bound_proved'] is False and a['RH_proved'] is False,'obstruction scope')
            require(row['checker_operations']==a['ops'],'checker ops correspondence')
            if row['id'] in tasks:
                task=tasks[row['id']];case=cases[(R.SPEC['source_ids'].index(source),p['memory'],families[task['family_id']])]
                require(case['certificate']==cert and row['constructor_operations']==0,'retained exact certificate reuse')
        selected=load(R.OUT/'frozen_candidates.json')['candidates'];index={r['id']:r for r in rows}
        require(all(index[c['id']]['program']==c['program'] for c in selected),'selected8 inclusion')
        feedback=load(R.OUT/'postrun_next_search_input.json');require(feedback['admitted_obstructions']==[{k:r[k] for k in ('id','program','certificate','admission')} for r in rows],'feedback36 correspondence')
        require(feedback['finite_candidates']==[dict(id=c['id'],program=c['program']) for c in selected],'feedback selected8')
        require(feedback['original_signed_bound_still_unpaid'] is True and feedback['uniform_growth_proved'] is False and feedback['RH_proved'] is False,'feedback honest scope')
        require(rank['independent_price_checks']==sum(r['checker_operations'] for r in rows) and rank['new_constructor_operations']==sum(r['constructor_operations'] for r in rows),'rank ops totals')
        require(rank['uniform_price_obstructions']==36 and rank['finite_full_profile_programs']==24 and rank['sublinear_programs']==12 and rank['arithmetic_sign_queries']==0,'rank counts')
        mainreport=load(R.OUT/'report.json');require(mainreport['elapsed_seconds']+rank['elapsed_seconds']<7200 and max(mainreport['conservative_process_peak_sum_bytes'],rank['peak_rss_bytes'])<16*1024**3,'combined sequential resource envelope')
        names=['mobius_dense_completion_search_082_development.json','mobius_dense_completion_checker_082_development.json','mobius_dense_rank_obstruction_082_development.json','mobius_dense_rank_obstruction_checker_082_development.json'];distinct=executions=passed=failed=0
        for name in names:
            r=load(R.ROOT/name)
            if 'test_attempts' in r:
                distinct+=max(x['tests_run'] for x in r['test_attempts']);executions+=sum(x['tests_run'] for x in r['test_attempts']);passed+=sum(x['tests_run'] for x in r['test_attempts'] if x['status']=='PASS')
            else:
                distinct+=r['distinct_tests']
                for attempt in r['attempts']:
                    executions+=attempt['tests'];passed+=attempt['passed'] if 'passed' in attempt else (attempt['tests'] if attempt['exit_code']==0 else 0);failed+=attempt.get('failed',0)
        require((distinct,executions,passed,failed)==(40,65,64,1),'retained test accounting')
        result.update(status='VERIFIED_SAVED_UNIFORM_RANK_ARTIFACT_BINDING',uniform_price_obstructions=36,full_roster_programs=24,sublinear_programs=12,selected_candidates_included=8,preserved_older_files=566,preserved_main_files=13,preserved_rank_files=10,distinct_tests=distinct,test_executions=executions,passed_executions=passed,retained_failed_executions=failed,combined_elapsed_seconds=mainreport['elapsed_seconds']+rank['elapsed_seconds'],uniform_source_bound_proved=False,RH_proved=False)
    except Exception as e:result.update(status='INVALID',reason=str(e))
    result['elapsed_seconds']=time.monotonic()-start
    with target.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps(result))

if __name__=='__main__':main()
