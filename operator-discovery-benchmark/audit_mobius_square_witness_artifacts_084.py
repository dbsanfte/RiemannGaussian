"""Saved fixed-operator fake-sign witness binding; no matrix/science replay."""
import json,time
from fractions import Fraction as Q
import run_mobius_coupled_square_084 as M
import run_mobius_square_witness_084 as W

def load(n):return json.loads((M.OUT/n).read_text())
def need(ok,msg):
    if not ok:raise ValueError(msg)
def main():
    path=M.OUT/'independent_witness_artifact_audit_084.json'
    if path.exists():raise FileExistsError('preserve attempt')
    start=time.monotonic();result=dict(schema='square-witness-artifact-audit-v1',full_matrix_science_replayed=False,unknown_signed_data_queried=False,hashes_used=False)
    try:
        need(load('independent_square_artifact_audit_084.json')['status']=='VERIFIED_COUPLED_SQUARE_ARTIFACT_BINDING','separate main admission')
        report=load('witness_report.json');protocol=load('witness_protocol.json');need(all(protocol[k]==v for k,v in W.SPEC.items()),'witness protocol SPEC')
        need(protocol['source_files']==W.FILES,'witness source roster');need(sum(M.validate_parent())==638,'older preservation')
        for n in M.FILES:need((M.ROOT/n).read_bytes()==(M.OUT/'source_snapshot'/n).read_bytes(),'main snapshot '+n)
        for n in W.FILES:need((M.ROOT/n).read_bytes()==(M.OUT/'witness_source_snapshot'/n).read_bytes(),'witness snapshot '+n)
        candidates=load('frozen_candidates.json')['candidates'];parents=load('validation_draw.json')['parents']
        expected=[dict(candidate_id=c['id'],u=u)for c in candidates for u in parents];roster=load('witness_frozen_tasks.json')
        need(roster['tasks']==expected and roster['all_candidates_and_parents_retained'] is True,'all fixed cases retained')
        need((M.OUT/'report.json').stat().st_mtime_ns<=(M.OUT/'witness_frozen_tasks.json').stat().st_mtime_ns,'post-main diagnostic chronology')
        expectedids={e['candidate_id']+'_'+str(e['u']):e for e in expected};outcomes={r['id']:r for r in report['outcomes']};need(set(outcomes)==set(expectedids),'complete outcome IDs')
        bycandidate={c['id']:c for c in candidates};good=[];rows=[]
        for uid,e in expectedids.items():
            row=load('witness_'+uid+'.json');rows.append(row);need(all(row[k]==v for k,v in outcomes[uid].items()),'pool saved outcome')
            need(row['id']==uid and row['candidate_id']==e['candidate_id'] and row['u']==e['u'],'case identity')
            if row['status']!='EXACT_FIXED_OPERATOR_OBSTRUCTION_WITNESS':need(row['status']=='WITNESS_FAILED' and 'error'in row,'retained witness failure');continue
            good.append(row);c=bycandidate[e['candidate_id']];u=e['u'];cert=row['certificate'];a=row['admission']
            need(a['status']=='VERIFIED_FINITE_FIXED_OPERATOR_SQUARE_LOWER_BOUND' and a['u']==u,'independent fixed witness admission')
            need(cert['lower_bound']==a['lower_bound'] and cert['squarefree_count']==a['squarefree_count'],'witness correspondence')
            signs=cert['signs'];need(len(signs)==a['effective_dimension'] and signs[0]==1 and all(type(v)is int and v in (-1,1)for v in signs),'complete artificial Boolean signs')
            need(len(row['attempts'])==1+min(4,len(signs))+16 and Q(cert['lower_bound'])==max(Q(r['exact_value'])for r in row['attempts']),'all starts/max retained witness')
            need(Q(row['lower_bound_over_u'])==Q(cert['lower_bound'])/u,'exact witness ratio')
            tests=[dict(**h,impossible_for_any_square_with_frozen_constant=not M.TARGET.exact_power_comparison(cert['lower_bound'],u,h['j'],h['constant']))for h in c['calibrated_growth_hypotheses']]
            need(row['growth_obstructions']==tests,'exact frozen-constant obstruction tests')
            validation=load('validation_'+c['id']+'.json');need(validation['program']==c['program'],'same frozen complete operator');upper=next(r for r in validation['rows']if r['u']==u)
            if upper['status']=='EXACT_SQUARE_PROPOSAL':need(row['verified_upper_bound']==upper['certificate']['price'] and Q(cert['lower_bound'])<=Q(row['verified_upper_bound']),'exact witness below admitted square price')
            for k in ('all_positive_square_completions_bound','fixed_operator_only','artificial_signs_not_actual_Mobius'):need(a[k] is True,'positive witness scope '+k)
            for k in ('whole_theta_grammar_bound','actual_signed_drift_lower_bound_proved','uniform_obstruction_proved','RH_proved'):need(a[k] is False,'limited witness scope '+k)
        aggregate=[dict(j=j,tested=len(good),obstructed=sum(t['impossible_for_any_square_with_frozen_constant']for r in good for t in r['growth_obstructions']if t['j']==j))for j in M.SPEC['diagnostic_exponent_parameters']]
        need(report['growth_obstructions_by_j']==aggregate,'all finite obstruction totals')
        need(report['status']=='COMPLETE_FIXED_OPERATOR_SQUARE_OBSTRUCTION_DIAGNOSTIC' and report['tasks']==len(expected) and report['admitted']==len(good),'report complete counts')
        need(report['search_operations']==sum(r.get('ops',0)for r in rows) and report['checker_operations']==sum(r['admission']['ops']for r in good),'operation accounting')
        for k in ('posthoc_on_existing_geometries','fixed_operator_only'):need(report[k] is True,'posthoc report '+k)
        for k in ('actual_signed_drift_lower_bound_proved','whole_theta_grammar_obstruction','uniform_obstruction_proved','RH_proved'):need(report[k] is False,'report limitedscope '+k)
        need(report['elapsed_seconds']<7200 and max(report['sampled_aggregate_peak_rss_bytes'],report['conservative_process_peak_sum_bytes'])<16*1024**3,'resource envelope')
        result.update(status='VERIFIED_SQUARE_WITNESS_ARTIFACT_BINDING',registered_cases=len(expected),admitted_witnesses=len(good),growth_obstructions_by_j=aggregate,older_files_preserved=638,main_files_preserved=14,witness_files_preserved=len(W.FILES),fixed_operator_only=True,actual_signed_drift_lower_bound_proved=False,uniform_obstruction_proved=False,RH_proved=False)
    except Exception as e:result.update(status='INVALID',reason=str(e))
    result['elapsed_seconds']=time.monotonic()-start;path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
