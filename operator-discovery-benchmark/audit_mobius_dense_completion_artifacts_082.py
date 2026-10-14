"""Read-only saved-artifact binding audit; no science or checker replay.
Exact saved arithmetic and direct provenance byte comparison only; no hashes.
"""
import json,random,time
from fractions import Fraction as Q
from pathlib import Path
import run_mobius_dense_completion_082 as R

def load(name):return json.loads((R.OUT/name).read_text())
def require(condition,message):
    if not condition:raise ValueError(message)

def main():
    start=time.monotonic();out={'schema':'saved-dense-artifact-audit-v1','new_source_values_queried':False,'old_science_or_tests_replayed':False,'hashes_used':False};receipt=R.OUT/'saved_artifact_admission_082.json'
    if receipt.exists():raise FileExistsError('preserve audit attempt '+str(receipt))
    try:
        counts=R.validate_parent();require(sum(counts)==566,'older provenance count')
        for name in R.FILES:require((R.ROOT/name).read_bytes()==(R.OUT/'source_snapshot'/name).read_bytes(),'stage bytes '+name)
        protocol=load('protocol.json');require(all(protocol[k]==v for k,v in R.SPEC.items()),'protocol SPEC')
        require(protocol['families']==R.families() and protocol['energies']==R.energies(),'frozen grammar binding')
        require(protocol['source_files']==R.FILES and protocol['prior_byte_preserved_files']==566,'protocol preservation')
        metadata=load('source_metadata.json');require(metadata==json.loads((R.PRIOR.OUT/'source_metadata.json').read_text()),'source metadata previous stage')
        known=load('prior_parent_inventory.json');require(known==R.inventory(),'parent inventory reproduction')
        tasks=[]
        for source in R.SPEC['source_ids']:
            for energy in R.energies():
                for family in R.families():
                    tasks.append(dict(id=source+'_'+energy['id']+'_'+family['id'],source_id=source,energy_id=energy['id'],family_id=family['id'],program=R.make_program(metadata[source]['fixed_kernel'],energy,family['profiles'])))
        roster=load('frozen_task_roster.json');require(roster['tasks']==tasks and len(tasks)==24,'24 complete task source/energy/profile binding')
        report=load('report.json');searches=[]
        for task in tasks:
            row=load('search_'+task['id']+'.json');searches.append(row)
            for key in ('id','source_id','energy_id','family_id'):require(row[key]==task[key],task['id']+' '+key)
            p=row['program'];base=task['program'];require({k:v for k,v in p.items() if k not in ('theta','gram_weights')}=={k:v for k,v in base.items() if k not in ('theta','gram_weights')},'program geometry changed')
            require(row['status']=='LP_PROPOSAL' and row['u']==R.SPEC['calibration_parent'],'discovery outcome')
            cert=row['certificate'];upper=row['upper_admission'];dual=row['dual'];adual=row['dual_admission'];baseline=row['same_geometry_zero_parameter_baseline'];ab=row['baseline_admission']
            for c,a in ((cert,upper),(baseline,ab)):
                require(a['status']=='VERIFIED_FINITE_DENSE_UPPER_BOUND','upper status')
                for k in ('group_count','squarefree_count','price','row_prices'):require(c[k]==a[k],'upper certificate/admission '+k)
                require(a['u']==row['u'],'upper parent')
                require(len(c['row_prices'])==c['group_count'] and all(Q(x)>=0 for x in c['row_prices']) and sum(map(Q,c['row_prices']))==Q(c['price']),'rowprice sum')
            require(adual['status']=='VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND' and adual['u']==row['u'] and adual['lower_bound']==dual['lower_bound'],'dual correspondence')
            G=cert['group_count'];require(len(dual['lambda'])==G and len(dual['nu'])==G*(G-1)//2,'dual shape')
            lambdas=list(map(Q,dual['lambda']));nus=list(map(Q,dual['nu']));require(all(0<=x<=1 for x in lambdas),'dual lambda bounds')
            index=0
            for g in range(G):
                for h in range(g+1,G):require(abs(nus[index])<=lambdas[g]+lambdas[h],'dual nu bounds');index+=1
            recomputed=Q(adual['base_functional'])-16*sum(abs(Q(v)) for v in adual['zero_template_functionals'])+16*sum(min(Q(0),Q(v)) for v in adual['gram_template_functionals'])
            require(recomputed==Q(dual['lower_bound']),'exact dual box price')
            require(Q(row['exact_gap'])==Q(cert['price'])-Q(dual['lower_bound']) and Q(row['exact_gap'])>=0,'exact primal/dual gap')
            for k,expected in [('price_over_u',Q(cert['price'])/row['u']),('price_over_u2',Q(cert['price'])/row['u']**2),('lower_price_over_u2',Q(dual['lower_bound'])/row['u']**2)]:require(Q(row[k])==expected,'price ratio')
            require(row['signs_or_source_values_used'] is False and row['uniform_growth_proved'] is False and row['RH_proved'] is False,'discovery proof scope')
        selected=[]
        for source in R.SPEC['source_ids']:
            for family in R.families():
                best=min((r for r in searches if r['source_id']==source and r['family_id']==family['id']),key=lambda r:(Q(r['certificate']['price']),r['id']))
                selected.append({k:best[k] for k in ('id','source_id','energy_id','family_id','program','u','certificate','dual')})
        frozen=load('frozen_candidates.json');require(frozen['candidates']==selected and frozen['selected_before_draw'] is True,'actual exact selection/freeze')
        rng=random.Random(R.SPEC['seed']);excluded=set(known['parents']);draws=[];us=[]
        for lo,hi in R.SPEC['validation_bands']:
            accepted=0
            while accepted<R.SPEC['fresh_parents_per_band']:
                u=rng.randint(lo,hi);ok=u not in excluded;draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED' if ok else 'REJECTED_PREVIOUS_OR_DUPLICATE'))
                if ok:us.append(u);excluded.add(u);accepted+=1
        us.sort();draw=load('validation_draw.json');require(draw['parents']==us and draw['draws']==draws and draw['seed']==R.SPEC['seed'],'draw reproduction')
        require(draw['drawn_after_formula_freeze'] is True and draw['source_signs_not_used'] is True,'draw scope')
        require((R.OUT/'frozen_candidates.json').stat().st_mtime_ns<=(R.OUT/'validation_draw.json').stat().st_mtime_ns,'saved chronology')
        validations=[]
        for candidate in selected:
            v=load('validation_'+candidate['id']+'.json');validations.append(v)
            require(v['program']==candidate['program'] and v['id']==candidate['id'],'validation formula binding')
            require([r['u'] for r in v['rows']]==us,'48 validation parent binding')
            for row in v['rows']:
                c,a=row['certificate'],row['admission'];require(a['status']=='VERIFIED_FINITE_DENSE_UPPER_BOUND' and a['u']==row['u'],'validation admission')
                for k in ('group_count','squarefree_count','price','row_prices'):require(c[k]==a[k],'validation certificate correspondence')
                require(sum(map(Q,c['row_prices']))==Q(c['price']) and all(Q(x)>=0 for x in c['row_prices']),'validation price sum')
                require(Q(row['price_over_u'])==Q(c['price'])/row['u'] and Q(row['price_over_u2'])==Q(c['price'])/row['u']**2,'validation ratios')
            require(v['new_arithmetic_horizon'] is False and v['uniform_growth_proved'] is False and v['uniform_original_source_bound_proved'] is False and v['RH_proved'] is False,'validation scope')
        require(report['tasks']==24 and report['admitted_proposals']==24 and report['independent_discovery_upper_checks']==48 and report['independent_dual_checks']==24 and report['validation_rows']==48,'report counts')
        require(report['selected_candidates']==8 and report['fresh_geometry_parents']==us and report['prior_byte_preserved_files']==566 and report['stage_frozen_files']==13,'report binding')
        require(report['constructor_operations']==sum(r['ops']+r['baseline_constructor_operations'] for r in searches)+sum(row['ops'] for v in validations for row in v['rows']),'constructor accounting')
        require(report['independent_discovery_operations']==sum(r[k]['ops'] for r in searches for k in ('upper_admission','dual_admission','baseline_admission')),'discovery checker accounting')
        require(report['independent_validation_operations']==sum(row['admission']['ops'] for v in validations for row in v['rows']),'validation checker accounting')
        require(report['elapsed_seconds']<R.SPEC['module_seconds'] and report['sampled_aggregate_peak_rss_bytes']<R.SPEC['max_aggregate_bytes'] and report['conservative_process_peak_sum_bytes']<R.SPEC['max_aggregate_bytes'],'reported stage resource envelope')
        require(report['independently_admitted_uniform_obstruction_certificates']==0 and len(roster['sublinear_obstructions'])==report['reviewed_analytic_sublinear_obstruction_proposals']==12,'sublinear analytic scope')
        for key in ('signs_or_source_values_used','uniform_growth_proved','uniform_original_source_bound_proved','RH_proved'):require(report[key] is False,'report false claim '+key)
        feedback=load('next_search_input.json');require(feedback['finite_candidates']==[dict(id=c['id'],program=c['program']) for c in selected],'feedback candidates')
        require(feedback['sublinear_obstructions']==roster['sublinear_obstructions'] and feedback['uniform_growth_proved'] is False and feedback['RH_proved'] is False,'feedback scope')
        out.update(status='VERIFIED_SAVED_DENSE_ARTIFACT_BINDING',source_energy_profile_programs=24,saved_upper_admissions=48,saved_dual_admissions=24,saved_validation_admissions=48,selected_candidates=8,fresh_geometry_parents=us,preserved_old_files=566,preserved_stage_files=13,reported_stage_resources_within_envelope=True,selection_draw_and_accounting_reproduced=True)
    except Exception as e:out.update(status='INVALID',reason=str(e))
    out.update(elapsed_seconds=time.monotonic()-start,scope='saved correspondence/provenance; does not replay independent scientific admissions',uniform_source_bound_proved=False,uniform_growth_proved=False,RH_proved=False)
    with receipt.open('x') as f:json.dump(out,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps(out));return out

if __name__=='__main__':main()
