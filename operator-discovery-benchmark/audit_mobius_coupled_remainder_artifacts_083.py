"""Bind saved complete residual admissions without matrix/science replay."""
import json,time
from fractions import Fraction as Q
import run_mobius_coupled_completion_083 as M
import run_mobius_coupled_remainder_083 as R

def load(name):return json.loads((M.OUT/name).read_text())
def need(ok,msg):
    if not ok:raise ValueError(msg)

def main():
    target=M.OUT/'saved_remainder_artifact_admission_083_attempt002.json'
    if target.exists():raise FileExistsError('preserve existing attempt')
    start=time.monotonic();result=dict(schema='coupled-remainder-artifact-audit-v1',full_matrix_science_replayed=False,unknown_signed_data_queried=False,hashes_used=False)
    try:
        report=load('remainder_report.json');protocol=load('remainder_protocol.json')
        need(load('independent_artifact_audit_083.json')['status']=='VERIFIED_COUPLED_ARTIFACT_BINDING','main binding admission')
        need(sum(M.validate_parent())==598,'older598 binding')
        for name in M.FILES:need((M.ROOT/name).read_bytes()==(M.OUT/'source_snapshot'/name).read_bytes(),'main snapshot '+name)
        for name in R.FILES:need((M.ROOT/name).read_bytes()==(M.OUT/'remainder_source_snapshot'/name).read_bytes(),'residual snapshot '+name)
        selected=[c for c in load('frozen_candidates.json')['candidates'] if 'outer_certificate' in c]
        parents=load('validation_draw.json')['parents'];ids=[c['id'] for c in selected]
        need(len(selected)==2 and len(parents)==6,'two fixed winners/six fixed parents')
        need(protocol['source_files']==R.FILES and protocol['selected_ids']==ids and protocol['parents']==parents,'residual protocol frozen bindings')
        for k in ('full_raw_outer_block_not_effective_anchor_subtraction','new_target_not_old_science_replay','all_selected_proof_family_winners_included','no_reselection'):need(protocol[k] is True,'protocol '+k)
        need(protocol['unknown_composite_signs_used'] is False,'no unknown signs')
        need(report['status']=='COMPLETE_EXACT_REMAINDER_COMPILATION' and report['admitted_rows']==12,'complete residual report')
        need(report['candidate_ids']==ids and report['parents']==parents,'report target roster')
        expected=[(c,u) for c in selected for u in parents];need(len(report['rows'])==len(report['outcomes'])==12,'complete twelve rows')
        byid={c['id']+'_'+str(u):(c,u)for c,u in expected}
        need({r['id']for r in report['rows']}==set(byid),'complete row identifiers')
        outcomes={r['id']:r for r in report['outcomes']}
        need(set(outcomes)==set(byid),'complete pool identifiers')
        for row in report['rows']:
            candidate,u=byid[row['id']];outcome=outcomes[row['id']]
            rid=candidate['id']+'_'+str(u);need(row==load('remainder_'+rid+'.json'),'saved row equality')
            need(row['id']==rid and row['candidate_id']==candidate['id'] and row['u']==u and row['status']=='VERIFIED','row target binding')
            need(all(row[k]==v for k,v in outcome.items()),'pool outcome binding')
            c=row['certificate'];a=row['admission'];d=row['diagnostics']
            need(a['status']=='VERIFIED_FINITE_COUPLED_REMAINDER_UPPER_BOUND' and a['u']==u,'independent residual admission')
            for k in ('squarefree_count','price','row_prices'):need(c[k]==a[k],'certificate correspondence '+k)
            need(len(c['row_prices'])==a['effective_dimension'] and sum(map(Q,c['row_prices']))==Q(c['price']),'Boolean signed trace rowprice sum')
            for k in ('signed_trace','anchor_constant','anchor_composite_absolute_price','composite_composite_absolute_price'):need(d[k]==a[k],'diagnostic correspondence '+k)
            need(Q(a['signed_trace'])==Q(a['anchor_constant'])+Q(a['composite_signed_trace']),'anchor trace decomposition')
            need(Q(c['price'])==Q(a['signed_trace'])+Q(a['anchor_composite_absolute_price'])+Q(a['composite_composite_absolute_price']),'complete residual price decomposition')
            need(Q(a['anchor_composite_absolute_price'])>=0 and Q(a['composite_composite_absolute_price'])>=0,'absolute edge prices')
            for k in ('prime_signs_anchored','complete_outer_certificate_bound','negative_Gram_removed','complete_cross_kernel_retained'):need(a[k] is True,'complete residual scope '+k)
            need(a['price_subtraction_used'] is False and a['uniform_remainder_bound_proved'] is False,'finite scope')
            outer=Q(candidate['outer_certificate']['uniform_bound_coefficient']);need(Q(a['outer_uniform_bound_coefficient'])==outer,'same-program uniform outer')
            need(Q(row['paid_outer_bound'])==outer*u and Q(row['combined_valid_drift_bound'])==outer*u+Q(c['price']),'complete valid drift sum')
            need(Q(row['remainder_price_over_u'])==Q(c['price'])/u and Q(row['remainder_price_over_u2'])==Q(c['price'])/(u*u),'exact residual ratios')
            need(d['prime_anchor'] is True and d['effective_dimension']==a['effective_dimension'],'diagnostic anchor geometry')
        need(report['constructor_operations']==sum(r['ops']for r in report['rows']),'constructor operation accounting')
        need(report['independent_checker_operations']==sum(r['admission']['ops']for r in report['rows']),'checker operation accounting')
        need(report['elapsed_seconds']<M.SPEC['module_seconds'],'elapsed resource envelope')
        for k in ('sampled_aggregate_peak_rss_bytes','conservative_process_peak_sum_bytes'):need(report[k]<M.SPEC['max_aggregate_bytes'],'resource '+k)
        for obj in (report,protocol):
            for k in ('uniform_original_source_bound_proved','RH_proved'):need(obj[k] is False,'scope '+k)
        need(report['uniform_remaining_bound_proved'] is False,'unpaid uniform residual')
        result.update(status='VERIFIED_COUPLED_REMAINDER_ARTIFACT_BINDING',rows_bound=12,candidates_bound=2,parents=parents,older_files_preserved=598,main_files_preserved=19,residual_files_preserved=len(R.FILES),constructor_operations=report['constructor_operations'],independent_checker_operations=report['independent_checker_operations'],reported_resources_within_envelope=True,uniform_remainder_bound_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)
    except Exception as e:result.update(status='INVALID',reason=str(e))
    result['elapsed_seconds']=time.monotonic()-start;target.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
    return result
if __name__=='__main__':main()
