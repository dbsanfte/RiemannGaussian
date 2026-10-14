"""Saved coupled083 bindings plus cheap independent outer re-admissions.
No full-matrix science replay, unknown Mobius signs, or hashes.
"""
import json,random,time
from fractions import Fraction as Q
import run_mobius_coupled_completion_083 as R
import check_mobius_coupled_outer_control_083 as OC

def load(name):return json.loads((R.OUT/name).read_text())
def require(ok,message):
    if not ok:raise ValueError(message)

def correspondence(cert,admission,u):
    require(admission['status']=='VERIFIED_FINITE_COUPLED_UPPER_BOUND' and admission['u']==u,'upper status/parent')
    for key in ('squarefree_count','price','row_prices'):require(cert[key]==admission[key],'upper '+key)
    require(sum(map(Q,cert['row_prices']))==Q(cert['price']),'Boolean rowprice sum')
    require(len(cert['row_prices'])==admission['effective_dimension'],'effective row count')
    require(admission['effective_coordinate_order'][0]=='anchor' and admission['prime_signs_anchored'] is True,'known prime anchoring')
    require(admission['effective_dimension']==cert['squarefree_count']-admission['known_sign_coordinates']+1,'anchor dimension')
    require(admission['known_sign_coordinates']==admission['prime_count']+1,'unit+allprime count')
    require(admission['Boolean_squarefree_diagonals_exact'] is True and admission['complete_target_admitted'] is True,'complete Boolean target')

def main():
    start=time.monotonic();target=R.OUT/'independent_artifact_audit_083.json'
    if target.exists():raise FileExistsError('preserve audit attempt '+str(target))
    result=dict(schema='coupled-artifact-audit-v1',full_matrix_science_replayed=False,unknown_signed_data_queried=False,hashes_used=False);outer_checks=[]
    try:
        report=load('report.json');counts=R.validate_parent();require(sum(counts)==598,'598 older files')
        for name in R.FILES:require((R.ROOT/name).read_bytes()==(R.OUT/'source_snapshot'/name).read_bytes(),'stage snapshot '+name)
        protocol=load('protocol.json');require(all(protocol[k]==v for k,v in R.SPEC.items()),'frozen protocol SPEC')
        require(protocol['families']==R.families() and protocol['energies']==R.energies() and protocol['source_files']==R.FILES,'prospective grammar')
        metadata=load('source_metadata.json');require(metadata==json.loads((R.PRIOR.OUT/'source_metadata.json').read_text()),'inherited source kernels')
        known=load('prior_parent_inventory.json');require(known==R.inventory(),'prior inventory reproduction')
        tasks=[]
        for source in R.SPEC['source_ids']:
            for energy in R.energies():
                for family in R.families():tasks.append(dict(id=source+'_'+energy['id']+'_'+family,source_id=source,energy_id=energy['id'],family_id=family,program=R.make_program(metadata[source]['fixed_kernel'],energy,family)))
        roster=load('frozen_task_roster.json');require(roster['tasks']==tasks and roster['all_rosters_frozen_before_discovery'] is True and len(tasks)==24,'complete24 task binding')
        searches=[]
        for task in tasks:
            row=load('search_'+task['id']+'.json');searches.append(row)
            require(row['status']=='LP_PROPOSAL','retained nonadmitted outcome '+task['id']+' '+row['status'])
            for key in ('id','source_id','energy_id','family_id'):require(row[key]==task[key],'task '+key)
            require(row['u']==1024,'calibration parent');p=row['program'];base=task['program']
            require({k:v for k,v in p.items() if k not in ('coupled_terms','gram_weights')}=={k:v for k,v in base.items() if k not in ('coupled_terms','gram_weights')},'source/energy/anchor binding')
            require(len(p['coupled_terms'])==len(base['coupled_terms']),'complete terms')
            for t,b in zip(p['coupled_terms'],base['coupled_terms']):require(t['cut']==b['cut'] and t['weight']==b['weight'] and -16<=Q(t['theta'])<=16,'term descriptor/bounds')
            require(all(0<=Q(w)<=16 for w in p['gram_weights']),'Gram box')
            correspondence(row['certificate'],row['upper_admission'],row['u']);correspondence(row['same_geometry_zero_parameter_baseline'],row['baseline_admission'],row['u'])
            c,d,a=row['certificate'],row['dual'],row['dual_admission'];E=row['upper_admission']['effective_dimension']
            require(a['status']=='VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND' and a['u']==row['u'] and d['lower_bound']==a['lower_bound'],'dual saved admission')
            require(a['effective_coordinate_order']==row['upper_admission']['effective_coordinate_order'] and a['known_sign_coordinates']==row['upper_admission']['known_sign_coordinates'],'dual anchor geometry')
            require(len(d['nu'])==E*(E-1)//2 and all(abs(Q(v))<=2 for v in d['nu']),'effective Boolean dual feasibility')
            lower=Q(a['base_functional'])-16*sum(abs(Q(v)) for v in a['coupled_template_functionals'])+16*sum(min(Q(0),Q(v)) for v in a['gram_template_functionals'])
            require(lower==Q(d['lower_bound']) and Q(row['exact_gap'])==Q(c['price'])-lower and Q(row['exact_gap'])>=0,'exact dual/gap')
            for key,value in [('price_over_u',Q(c['price'])/1024),('price_over_u2',Q(c['price'])/1024**2),('lower_price_over_u2',lower/1024**2)]:require(Q(row[key])==value,'saved ratio')
            require(row['unknown_composite_signs_used'] is False and row['observed_full_source_values_used'] is False and row['known_prime_signs_anchored'] is True and row['uniform_growth_proved'] is False and row['RH_proved'] is False,'search information/proof scope')
            if task['family_id']=='matched_certified':
                system=OC.equality_constraints(base);require(system['status']=='OUTER_EQUALITY_SYSTEM','independent symbolic family derivation')
                require(row['proof_equalities']=={k:system[k] for k in ('rows','rhs')},'declared theorem-family LP origin')
                check=OC.verify_certificate(p,row['outer_certificate']);require(check['status']=='VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL','independent outer re-admission')
                require(check==row['outer_admission'],'exact saved outer admission reproducibility');outer_checks.append(dict(id=task['id'],admission=check))
            else:require('outer_certificate' not in row and row['proof_equalities'] is None,'unrestricted family scope')
        selected=[]
        for source in R.SPEC['source_ids']:
            for family in R.families():
                best=min((r for r in searches if r['source_id']==source and r['family_id']==family),key=lambda r:(Q(r['certificate']['price']),r['id']))
                selected.append({k:best[k] for k in ('id','source_id','energy_id','family_id','program','u','certificate','dual','outer_certificate','outer_admission') if k in best})
        frozen=load('frozen_candidates.json');require(frozen['candidates']==selected and frozen['selected_before_draw'] is True,'exact8 winner selection')
        rng=random.Random(R.SPEC['seed']);excluded=set(known['parents']);draws=[];us=[]
        for lo,hi in R.SPEC['validation_bands']:
            accepted=0
            while accepted<R.SPEC['fresh_parents_per_band']:
                u=rng.randint(lo,hi);ok=u not in excluded;draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED' if ok else 'REJECTED_PREVIOUS_OR_DUPLICATE'))
                if ok:us.append(u);excluded.add(u);accepted+=1
        us.sort();draw=load('validation_draw.json');require(draw['draws']==draws and draw['parents']==us and draw['seed']==R.SPEC['seed'] and draw['drawn_after_formula_freeze'] is True,'fresh draw reproduction')
        require((R.OUT/'frozen_candidates.json').stat().st_mtime_ns<=(R.OUT/'validation_draw.json').stat().st_mtime_ns,'corroborating freeze chronology')
        validations=[]
        for candidate in selected:
            v=load('validation_'+candidate['id']+'.json');validations.append(v);require(v['id']==candidate['id'] and v['program']==candidate['program'],'frozen validation program')
            require([r['u'] for r in v['rows']]==us,'all6 validation parents')
            for row in v['rows']:
                require(row['status']=='VERIFIED','validation failed');correspondence(row['certificate'],row['admission'],row['u'])
                require(Q(row['price_over_u'])==Q(row['certificate']['price'])/row['u'] and Q(row['price_over_u2'])==Q(row['certificate']['price'])/row['u']**2,'validation exact ratios')
            require(v['known_unit_and_all_prime_signs_used'] is True and v['new_unknown_signed_arithmetic_horizon'] is False and v['uniform_full_growth_proved'] is False and v['RH_proved'] is False,'validation scope')
        for key,value in [('tasks',24),('admitted_proposals',24),('selected_candidates',8),('uniform_whole_outer_certificates',6),('validation_rows',48),('admitted_validation_rows',48),('independent_discovery_upper_checks',48),('independent_dual_checks',24),('prior_frozen_files',598)]:require(report[key]==value,'report '+key)
        require(report['fresh_geometry_parents']==us,'report draw')
        require(report['constructor_operations']==sum(r['ops']+r['baseline_constructor_operations'] for r in searches)+sum(row['ops'] for v in validations for row in v['rows']),'matrix constructor accounting')
        require(report['independent_discovery_operations']==sum(r[k]['ops'] for r in searches for k in ('upper_admission','dual_admission','baseline_admission')),'matrix discovery checker accounting')
        require(report['independent_validation_operations']==sum(row['admission']['ops'] for v in validations for row in v['rows']),'matrix validation checker accounting')
        require(report['elapsed_seconds']<7200 and report['sampled_aggregate_peak_rss_bytes']<16*1024**3 and report['conservative_process_peak_sum_bytes']<16*1024**3,'reported resource envelope')
        for key in ('unknown_composite_signs_used','observed_full_source_values_used','uniform_full_growth_proved','uniform_original_source_bound_proved','RH_proved','hashes_used'):require(report[key] is False,'report false claim '+key)
        require(report['known_unit_and_all_prime_signs_used'] is True,'known-sign disclosure')
        result.update(status='VERIFIED_COUPLED_ARTIFACT_BINDING',programs=24,discovery_upper_checks_bound=48,discovery_dual_checks_bound=24,validation_rows_bound=48,outer_controls_re_admitted=6,outer_admissions=outer_checks,selected_candidates=8,fresh_geometry_parents=us,older_files_preserved=598,stage_files_preserved=len(R.FILES),outer_checker_operations_replayed=sum(r['admission']['ops'] for r in outer_checks),saved_outer_checker_operations=sum(r['outer_admission']['ops'] for r in searches if 'outer_admission' in r),resource_accounting_scope='Saved main matrix-constructor/checker totals; symbolic equality/synthesis work not included in those main totals.',reported_resources_within_envelope=True,uniform_full_growth_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)
    except Exception as e:result.update(status='INVALID',reason=str(e))
    result['elapsed_seconds']=time.monotonic()-start
    with target.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k!='outer_admissions'}))

if __name__=='__main__':main()
