"""Independent saved084 bindings, no matrix/science replay or unknown signs."""
import json,random,time
from copy import deepcopy
from fractions import Fraction as Q
import run_mobius_coupled_square_084 as R
import check_mobius_coupled_outer_control_083 as OC

def load(name):return json.loads((R.OUT/name).read_text())
def need(ok,msg):
    if not ok:raise ValueError(msg)

def upper(row,u):
    c=row['certificate'];a=row.get('upper_admission',row.get('admission'))
    need(a['status']=='VERIFIED_FINITE_COUPLED_SQUARE_BOUND' and a['u']==u,'finite square admission')
    for k in ('price','row_prices','squarefree_count'):need(c[k]==a[k],'upper certificate '+k)
    need(sum(map(Q,c['row_prices']))==Q(c['price']) and len(c['row_prices'])==a['effective_dimension'],'complete Boolean rows')
    L=c['factor_numerators'];den=int(c['factor_denominator']);need(len(L)==a['effective_dimension'],'complete factor coordinates')
    rank=len(L[0])if L else 0;need(all(len(r)==rank for r in L) and rank==a['factor_rank'],'factor rank')
    trace=sum((Q(int(v)**2,den**2)for r in L for v in r),Q(0));need(trace==Q(a['factor_trace']),'exact positive factor trace')
    d=row['diagnostics'];need(Q(d['factor_trace'])==trace and d['rank']==rank and d['effective_dimension']==a['effective_dimension'],'factor diagnostics')
    need(d['old_residual_price']==a['old_residual_price'],'L0 baseline binding')
    need(Q(c['price'])<=Q(d['old_residual_price']),'zero-factor fallback guarantee')
    need(Q(a['signed_trace'])+Q(a['absolute_cross_price'])==Q(c['price']),'complete price decomposition')
    for k in ('exact_positive_square_verified','complete_outer_certificate_bound','negative_original_Gram_removed','prime_signs_anchored'):need(a[k] is True,'upper scope '+k)
    need(a['uniform_remaining_bound_proved'] is False,'finite upper scope')
    need(Q(row['price_over_u'])==Q(c['price'])/u and Q(row['price_over_u2'])==Q(c['price'])/(u*u),'exact ratios')

def main():
    path=R.OUT/'independent_square_artifact_audit_084.json'
    if path.exists():raise FileExistsError('preserve audit attempt')
    start=time.monotonic();out=dict(schema='coupled-square-artifact-audit-v1',full_matrix_science_replayed=False,unknown_signed_data_queried=False,hashes_used=False)
    try:
        report=load('report.json');counts=R.validate_parent();need(sum(counts)==638,'638 older bytes')
        for n in R.FILES:need((R.ROOT/n).read_bytes()==(R.OUT/'source_snapshot'/n).read_bytes(),'frozen084 '+n)
        protocol=load('protocol.json');need(all(protocol[k]==v for k,v in R.SPEC.items()),'SPEC binding');need(protocol['source_files']==R.FILES,'source roster')
        prior=json.loads((R.PRIOR.OUT/'frozen_candidates.json').read_text())['candidates'];parents=[c for c in prior if 'outer_certificate'in c]
        expected=[]
        for source in R.SPEC['source_ids']:
            parent=next(c for c in parents if c['source_id']==source)
            for family in R.SPEC['families']:expected.append(dict(id=source+'_'+family,source_id=source,family_id=family,parent_id=parent['id'],program=R.make_program(parent['program'],family)))
        roster=load('frozen_task_roster.json');need(roster['tasks']==expected and roster['registered_before_calibration'] is True,'prospective eight roster')
        known=load('prior_parent_inventory.json');need(known==R.inventory(),'prior inventory')
        rows=[load('search_'+t['id']+'.json')for t in expected];outcomes={r['id']:r for r in report['discovery']};need(set(outcomes)=={t['id']for t in expected},'all discovery outcomes')
        admitted=[]
        for task,row in zip(expected,rows):
            need(all(row[k]==v for k,v in outcomes[task['id']].items()),'discovery outcome binding')
            need(all(row[k]==task[k]for k in ('id','source_id','family_id')) and row['u']==1024,'discovery identity')
            if row['status']!='EXACT_SQUARE_PROPOSAL':
                need(row['status']in ('RESOURCE_REJECTED','TASK_FAILED','SCS_NO_PROPOSAL','EXACT_AFFINE_RECONSTRUCTION_FAILED'),'retained failure status');continue
            admitted.append(row);p=deepcopy(row['program']);base=deepcopy(task['program'])
            for t in p['coupled_terms']:need(-16<=Q(t['theta'])<=16,'theta boxes');t['theta']='0'
            for t in base['coupled_terms']:t['theta']='0'
            need(p==base,'complete source/energy/Gram/template binding')
            upper(row,1024)
            coeff={4:Q(-1),5:Q(1),8:Q(1),10:Q(-1)}
            if row['source_id']=='q1_p04':
                for k,v in list(coeff.items()):coeff[k*3]=coeff.get(k*3,Q(0))+Q(3547,8192)*v
            need(row['program']['kernel']==[dict(divisor=k,weight=str(v))for k,v in sorted(coeff.items())if v],'independent exact fixed source kernel')
            need(row['conditional_target']==R.TARGET.compile_target(row['program'],R.transfer(row['source_id'])),'exact conditional fixed-kernel transfer')
            need(row['calibrated_growth_hypotheses']==R.growth_constants(row['certificate']['price'],1024),'minimal exact finite growth constants')
            a=row['dual_admission'];d=row['dual'];need(a['status']=='VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND' and a['u']==1024,'dual status')
            need(d['lower_bound']==a['lower_bound'] and d['squarefree_count']==a['squarefree_count'],'dual saved certificate')
            eq=OC.equality_constraints(row['program']);nt=len(row['program']['coupled_terms']);grams=list(map(Q,row['program']['gram_weights']))
            rhs=[Q(b)-sum((Q(v)*g for v,g in zip(e[nt:],grams)),Q(0))for e,b in zip(eq['rows'],eq['rhs'])]
            need(list(map(Q,a['equality_rhs']))==rhs and len(d['equality_multipliers'])==len(rhs),'independent equality RHS')
            need(len(a['template_functionals'])==len(a['adjusted_functionals'])==nt,'complete dual roster')
            expectedadjusted=[Q(v)+sum((Q(l)*Q(e[k])for l,e in zip(d['equality_multipliers'],eq['rows'])),Q(0))for k,v in enumerate(a['template_functionals'])]
            need(list(map(Q,a['adjusted_functionals']))==expectedadjusted,'exact dual equality adjustments')
            den=int(d['factor_denominator']);need(len(d['factor_numerators'])==a['effective_dimension'] and all(sum(int(v)**2 for v in rr)<=den*den for rr in d['factor_numerators']),'exact dual PSD row-norm slack')
            need(Q(a['lower_bound'])==Q(a['base_functional'])-sum((Q(l)*Q(b)for l,b in zip(d['equality_multipliers'],a['equality_rhs'])),Q(0))-16*sum(map(lambda x:abs(Q(x)),a['adjusted_functionals'])),'exact dual price formula')
            need(Q(row['exact_gap'])==Q(row['certificate']['price'])-Q(d['lower_bound'])>=0,'exact primal dual gap')
            need(a['all_theta_boxes_and_outer_equalities_bound'] is True and a['actual_signed_drift_lower_bound_proved'] is False,'dual cone scope')
        frozen=load('frozen_candidates.json');selected=[{k:r[k]for k in ('id','source_id','family_id','program','outer_certificate','certificate','dual','calibrated_growth_hypotheses')}for r in admitted]
        need(frozen['candidates']==selected and frozen['all_admitted_families_retained'] is True and frozen['operator_frozen_before_draw'] is True,'retain all admitted families')
        rng=random.Random(R.SPEC['seed']);excluded=set(known['parents']);us=[];draws=[]
        for lo,hi in R.SPEC['validation_bands']:
            accepted=0
            while accepted<R.SPEC['fresh_parents_per_band']:
                u=rng.randint(lo,hi);ok=u not in excluded;draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED'if ok else'REJECTED_PREVIOUS_OR_DUPLICATE'))
                if ok:us.append(u);excluded.add(u);accepted+=1
        us.sort();draw=load('validation_draw.json');need(draw['parents']==us and draw['draws']==draws and draw['drawn_after_operator_freeze'] is True,'reproducible fresh draw')
        need((R.OUT/'frozen_candidates.json').stat().st_mtime_ns<=(R.OUT/'validation_draw.json').stat().st_mtime_ns,'freeze before draw timestamp support')
        checks=[];good=[]
        valout={v['id']:v for v in report['validation']};need(set(valout)=={c['id']for c in selected},'all candidate validation outcomes')
        for c in selected:
            v=load('validation_'+c['id']+'.json');checks.append(v);need(v['program']==c['program'] and v['outer_certificate']==c['outer_certificate'],'unchanged operator and outer proof')
            need(all(v[k]==x for k,x in valout[c['id']].items()),'validation pool binding')
            need([r['u']for r in v['rows']]==us,'all four parents')
            need(v['operator_coefficients_frozen'] is True and v['new_auxiliary_factor_searches'] is True and v['new_unknown_sign_data'] is False,'new auxiliary scope')
            for row in v['rows']:
                if row['status']!='EXACT_SQUARE_PROPOSAL':continue
                good.append(row);upper(row,row['u']);need(row['operator_optimized'] is False,'no theta retuning')
                expectedtests=[dict(**h,passes=R.TARGET.exact_power_comparison(row['certificate']['price'],row['u'],h['j'],h['constant']))for h in c['calibrated_growth_hypotheses']]
                need(row['calibrated_growth_tests']==expectedtests,'finite growth tests')
        need(report['tasks']==8 and report['admitted_proposals']==report['frozen_operators']==len(admitted),'report discovery totals')
        need(report['new_auxiliary_rows']==4*len(admitted) and report['independently_admitted_auxiliary_rows']==len(good),'report full validation totals')
        need(report['new_geometry_parents']==us,'report draw')
        growth=[dict(j=j,passes=sum(t['passes']for rr in good for t in rr['calibrated_growth_tests']if t['j']==j),tested=sum(t['j']==j for rr in good for t in rr['calibrated_growth_tests']))for j in R.SPEC['diagnostic_exponent_parameters']]
        need(report['growth_hypotheses_by_j']==growth,'complete finite growth summary')
        need(report['constructor_operations']==sum(r.get('ops',0)for r in rows)+sum(r.get('ops',0)for r in good),'constructor accounting')
        need(report['independent_discovery_operations']==sum(r['upper_admission']['ops']+r['dual_admission']['ops']for r in admitted),'discovery accounting')
        need(report['independent_validation_operations']==sum(r['admission']['ops']for r in good),'validation accounting')
        for k in ('uniform_remaining_bound_proved','uniform_source_bound_proved','RH_proved','unknown_composite_signs_used','observed_full_source_values_used'):need(report[k] is False,'scope '+k)
        need(report['elapsed_seconds']<R.SPEC['module_seconds'] and max(report['sampled_aggregate_peak_rss_bytes'],report['conservative_process_peak_sum_bytes'])<R.SPEC['max_aggregate_bytes'],'resource envelope')
        out.update(status='VERIFIED_COUPLED_SQUARE_ARTIFACT_BINDING',programs_bound=8,admitted_operators=len(admitted),primal_dual_discovery_pairs=len(admitted),new_factor_rows=len(good),parents=us,older_files_preserved=638,stage_files_preserved=len(R.FILES),conditional_targets_bound=len(admitted),uniform_remaining_bound_proved=False,RH_proved=False)
    except Exception as e:out.update(status='INVALID',reason=str(e))
    out['elapsed_seconds']=time.monotonic()-start;path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
