"""Read-only saved-record audit. No source sieve, pair compilation, or science replay.
Imports runner for OUT/FILES and its explicitly authorized byte-preservation helper only.
Standalone Fraction arithmetic independently checks all stored prices and energies.
"""
from fractions import Fraction as F
from pathlib import Path
import json, math, traceback, time, random
import run_mobius_density_packet_081 as R

Q=1<<24
COUNTS={}
def check(condition,message):
    if not condition: raise AssertionError(message)
    COUNTS[message.split(':')[0]]=COUNTS.get(message.split(':')[0],0)+1
def read(name): return json.loads((R.OUT/name).read_text())
def ceil24(x): return F(-(-x.numerator*Q//x.denominator),Q)
def root(n,k):
    lo,hi=0,1<<((n.bit_length()+k-1)//k)
    while lo+1<hi:
        m=(lo+hi)//2
        if m**k<=n:lo=m
        else:hi=m
    return hi if hi**k<=n else lo
def floorpower(u,e):return root(u**e.numerator,e.denominator)
def matrices(p):
    m=p['memory']; H=[[F(int(i==j==0)) for j in range(m)] for i in range(m)]
    for ray in p['rays']:
        a=list(map(F,ray['a']));w=F(ray['weight'])
        for i in range(m):
            for j in range(m): H[i][j]+=w*a[i]*a[j]
    r=F(p['drift_multiplier'])
    T=[[ (H[i][j] if i<m and j<m else 0)-(r*H[i-1][j-1] if i and j else 0) for j in range(m+1)]for i in range(m+1)]
    return H,T
OMEGA={}
def omega(e):
    if e in OMEGA:return OMEGA[e]
    # Complete tiny exceptional-prime roster, independently trial-divided.
    horizon=root(2**e.denominator,e.numerator)
    ps=[p for p in range(2,horizon+1) if p**e.numerator<2**e.denominator and all(p%d for d in range(2,math.isqrt(p)+1))]
    c=F(1)
    for p in ps:
        lower=F(root(p**e.numerator*Q**e.denominator,e.denominator),Q)
        c=ceil24(c*2/lower)
    OMEGA[e]=(c,ps,horizon);return OMEGA[e]
def energy(H,state):return sum(H[i][j]*state[i]*state[j] for i in range(len(H)) for j in range(len(H)))
def row_check(p,u,c):
    H,T=matrices(p);s=list(map(F,c['state']))
    check(len(s)==p['memory']+1,'state_dimension')
    E=energy(H,s[:-1]);half=energy(H,s[1:]);drift=E-F(p['drift_multiplier'])*half
    check(E==F(c['energy']) and half==F(c['half_energy']) and drift==F(c['drift']),'exact_energy_recombination')
    check(drift-F(c['packet'])==F(c['unlinked']),'packet_unlinked_recombination')
    check(c['D']==floorpower(u,F(p['eta'])),'exact_roster_cutoff')
    check(F(c['weighted_density'])==0,'saved_exact_density_balance')
    check(0<=c['weighted_pairs']<=c['nonzero_pairs']<=c['pair_count'],'label_count_scope')
    return s

def audit():
    report=read('report.json');spec=read('spec.json');meta=read('source_metadata.json');manifest=read('frozen_candidates.json');draw=read('validation_draw.json');inventory=read('known_parent_inventory.json')
    prior=R.validate_parent()
    check(sum(prior)==542 and prior==report['prior_frozen_counts'],'prior_direct_byte_preservation')
    for name in R.FILES:check((R.ROOT/name).read_bytes()==(R.OUT/'source_snapshot'/name).read_bytes(),'081_direct_byte_preservation')
    for sid,m in meta.items():
        check(m['source_binding']['status']=='VERIFIED_FIXED_KERNEL' and m['source_binding']['normalized_derived_kernel']==m['fixed_kernel'],'source_guard_binding')
        check(m['source_binding']['kernel_is_before_excluded_prime_folds'] is True,'original_unfolded_source')
    searches=[(f,json.loads(f.read_text())) for f in sorted(R.OUT.glob('search_*.json'))]
    proposals=[];energy_ids={};all_rows=0;admitted_states={};finite_count=0;refutations={};files=[]
    for candidate in manifest['candidates']:
        p=candidate['program'];cid=candidate['id'];dis=read('discovery_checks_'+cid+'.json');val=read('validation_'+cid+'.json');files.extend([dis,val])
        check(read('candidate_'+cid+'.json')==candidate,'candidate_manifest_identity')
        for record in (dis,val):
            check(len(record['rows'])==len(record['checks']),'finite_admission_count')
            for row,adm in zip(record['rows'],record['checks']):
                c=row['certificate'];u=row['u'];row_check(p,u,c);finite_count+=1
                check(adm['status']=='VERIFIED_FINITE_PACKET' and adm['u']==u and all(adm[k]==v for k,v in c.items()),'finite_saved_admission_binding')
                check(all(adm[k] is True for k in ['arithmetic_source_admitted','complete_ratio_bank_admitted','exact_density_balance_verified','source_delay_identity_verified']),'finite_source_admission')
                key=candidate['source_id'],u
                s=list(map(F,c['state']));old=admitted_states.get(key,[])
                check(s[:min(len(s),len(old))]==old[:min(len(s),len(old))],'shared_source_state_consistency')
                if len(s)>len(old):admitted_states[key]=s
                if record is val:
                    holds=F(c['unlinked'])<=F(candidate['discovery_unlinked_kappa'])*u
                    check(row['unlinked_calibrated_bound_holds']==holds,'validation_refutation_arithmetic')
                    check(abs(F(c['packet']))<=F(candidate['certificate']['constant'])*u,'finite_paid_packet_bound')
            if record is val:
                bad=[r for r in record['rows'] if not r['unlinked_calibrated_bound_holds']]
                check(len(bad)==record['finite_unlinked_refutations'] and len(record['rows'])-len(bad)==record['finite_unlinked_certified'],'validation_outcome_count')
                check(record['first_refutation']==min(bad,key=lambda r:r['u']),'first_refutation_binding')
                refutations[cid]=len(bad)
                check(record['uniform_unlinked_bound_proved'] is False and record['RH_proved'] is False,'unpaid_scope')
                check(sorted(r['u'] for r in record['rows'])==draw['parents'],'complete_fresh_validation_domain')
    for f,srch in searches:
        energy_ids.setdefault(srch['source_id'],set()).add(srch['energy']['index'])
        for item in srch['all_programs']:
            p=item['program'];H,T=matrices(p);eps=F(p['epsilon']);eta=F(p['eta']);oc,ps,horizon=omega(eps)
            J=2*sum(abs(x) for row in T for x in row)*sum(abs(F(k['weight'])) for k in p['kernel'])**2
            exponent=F(1,2)+eta*(F(3,2)+2*eps);cert={'omega_price':str(oc),'jump_price':str(J),'constant':str(J*(oc+2)),'exponent':str(exponent)}
            check(item['certificate']==cert and exponent<=F(p['q']),'all_program_exact_price')
            adm=item['bound_admission'];check(adm['status']=='VERIFIED_UNIFORM_SIGNED_PACKET_BOUND' and all(adm[k]==v for k,v in cert.items()),'bound_admission_arithmetic')
            check(adm['H']==[[str(x)for x in row]for row in H] and adm['T']==[[str(x)for x in row]for row in T],'full_drift_matrix_binding')
            check(adm['omega_primes']==ps and adm['omega_prime_horizon']==horizon,'complete_exceptional_prime_roster')
            check(p['kernel']==meta[item['source_id']]['fixed_kernel'],'program_source_binding')
            rows=[(int(u),byD[str(floorpower(int(u),eta))])for u,byD in srch['exact_discovery_rows_by_parent_and_D'].items()]
            vals=[];pos=neg=0;both=False;nonzero=False
            for u,c in rows:
                state=row_check(p,u,c);all_rows+=1
                check(state==admitted_states[item['source_id'],u][:len(state)],'all_energy_source_to_selected_admission')
                vals.append(F(c['unlinked'])/u);pos+=F(c['packet'])>0;neg+=F(c['packet'])<0
                both|=F(c['positive_mass'])>0 and F(c['negative_mass'])>0;nonzero|=F(c['packet'])!=0
            maximum=max(vals)
            check(item['discovery_unlinked_kappa']==str(ceil24(max(0,maximum))) and item['maximum_observed_unlinked_over_u']==str(maximum),'independent_discovery_calibration')
            check(item['positive_packet_rows']==pos and item['negative_packet_rows']==neg and item['both_density_signs_seen']==both and item['nonzero_packet_seen']==nonzero,'discovery_activity_metrics')
            check(item['selection_eligible']==(item['energy_kind']=='memory_cross_term' and both and nonzero),'selection_eligibility')
            check(item['maximum_D']==max(c['D']for u,c in rows),'maximum_roster_binding')
            proposals.append(dict(item,search_file=f.name))
    expected=[]
    for sid in R.SPEC['source_ids']:
        opts=[p for p in proposals if p['source_id']==sid and p['selection_eligible']]
        keys=[lambda x:(-F(x['program']['eta']),F(x['certificate']['constant']),F(x['discovery_unlinked_kappa']),x['energy_index'],x['schedule_index']),lambda x:(F(x['certificate']['constant']),F(x['discovery_unlinked_kappa']),-F(x['program']['eta']),x['energy_index'],x['schedule_index']),lambda x:(F(x['discovery_unlinked_kappa']),-F(x['program']['eta']),F(x['certificate']['constant']),x['energy_index'],x['schedule_index'])]
        winners={}
        for track,key in zip(R.SPEC['selection_tracks'],keys):
            win=min(opts,key=key);label=win['energy_index'],win['schedule_index'];winners.setdefault(label,[win,[]])[1].append(track)
        for i,(win,tracks) in enumerate(winners.values()):
            candidate=next(c for c in manifest['candidates']if c['id']==sid+'_packet_'+str(i))
            check(all(candidate[k]==v for k,v in win.items()) and candidate['selection_tracks']==tracks,'full_rank_selection')
            expected.append(candidate['id'])
    check(len(proposals)==1122==report['generated_programs'] and len(searches)==34 and finite_count==330==report['independently_checked_finite_rows'],'complete_generated_inventory')
    check(len(expected)==6==report['selected_candidates'],'selected_inventory')
    check(manifest['validation_draw_started'] is False and manifest['discovery_independently_checked'] is True and draw['drawn_after_formula_freeze'] is True,'freeze_before_fresh_draw')
    known=set(inventory['parents']);check(len(draw['parents'])==36 and not known.intersection(draw['parents']),'freshness_against_inventory')
    accepted=[d['u']for d in draw['draws']if d['status']=='ACCEPTED'];check(sorted(accepted)==draw['parents'] and len(set(accepted))==len(accepted),'draw_acceptance_inventory')
    olddraw=json.loads((R.PRIOR.OUT/'validation_draw.json').read_text())['parents']
    oldknown=set(inventory['prior_inventory']['parents'])
    expectedknown=oldknown|set(olddraw)|{u//2 for u in olddraw}|{1103,551,275}
    check(known==expectedknown and inventory['newly_registered080_parents']==olddraw,'inventory_all_prior_halves_linkage')
    expecteddisc=sorted(set(olddraw[::8]+[olddraw[-1]]))
    check(spec['discovery_parents']==expecteddisc,'discovery_parent_selection_linkage')
    rng=random.Random(draw['seed']); regenerated=[];maximum=R.SPEC['maximum_parent']
    for level in range(14,maximum.bit_length()):
        low,high=2**level,min(maximum,2**(level+1)-1)
        if low<=high:
            for _ in range(3):regenerated.append(dict(u=rng.randint(low,high),kind='irregular',level=level))
    for eta in sorted({F(c['program']['eta'])for c in manifest['candidates']}):
        b=max(2,floorpower(maximum,eta)//2);n=b**eta.denominator
        boundary=root(n,eta.numerator)
        if boundary**eta.numerator<n:boundary+=1
        for offset in [-1,0,1]:regenerated.append(dict(u=boundary+offset,kind='ratio_entry',eta=str(eta),label=b,boundary=boundary))
    occupied=set(known)
    for d in regenerated:
        u=d['u'];d['status']='OUTSIDE_DOMAIN' if not 1<=u<=maximum else 'PREVIOUSLY_KNOWN_OR_DUPLICATE' if u in occupied else 'ACCEPTED'
        if d['status']=='ACCEPTED':occupied.add(u)
    check(regenerated==draw['draws'],'complete_seeded_draw_and_boundary_regeneration')

    check(all(r['id']in refutations for r in report['results']) and {r['id']:r['finite_unlinked_refutations']for r in report['results']}==refutations,'report_result_binding')
    check(report['constructor_operations']==sum(d['constructor_operations']for f,d in searches)+sum(d.get('constructor_operations',0)for d in files),'constructor_work_total')
    check(report['checker_operations']==sum(d['checker_operations']for f,d in searches)+sum(d['checker_operations']for d in files),'checker_work_total')
    check(report['elapsed_seconds']<7200 and report['conservative_sum_process_peaks_bytes']<16*1024**3,'reported_resource_limits')
    check(all(report[k]is False for k in ['uniform_original_source_bound_proved','uniform_unlinked_bound_proved','RH_proved','hashes_used','new_arithmetic_horizon']),'report_no_promotion')
    return dict(status='PASS',checks=COUNTS,generated_price_records=len(proposals),saved_discovery_recombinations=all_rows,selected_finite_admissions=finite_count,prior_byte_preserved_files=sum(prior),stage_byte_preserved_files=len(R.FILES),selected_refutations=refutations,exceptional_prime_prices_checked=len(OMEGA),uniform_original_source_bound_proved=False,uniform_unlinked_bound_proved=False,RH_proved=False,scope='Saved arithmetic and linkage audit; no new source queries. Analytic packet theorem is auxiliary only. Retained label counts do not measure physical coverage.')

if __name__=='__main__':
    start=time.monotonic();attempts=[dict(attempt=1,status='ENVIRONMENT_FAILURE',detail='Initial read-only runner import under system python3 failed: ModuleNotFoundError numpy. No source or audit checks executed. Corrected to project venv.')]
    try:
        result=audit();attempts.append(dict(attempt=2,status='PASS'))
    except Exception:
        result=dict(status='FAIL',traceback=traceback.format_exc(),checks=COUNTS);attempts.append(dict(attempt=2,status='FAIL',detail=result['traceback']))
    prior_result=Path('mobius_density_packet_independent_audit_081.json')
    if prior_result.exists():
        old_attempts=json.loads(prior_result.read_text())['attempts']
        attempts=old_attempts+[dict(attempt=len(old_attempts)+1,status=result['status'],detail='Expanded inventory/draw linkage audit; previous evidence retained unchanged.')]
    result.update(attempts=attempts,elapsed_seconds=time.monotonic()-start)
    target=Path('mobius_density_packet_independent_audit_081.json')
    if target.exists():target=Path('mobius_density_packet_independent_audit_081_attempt_'+str(time.time_ns())+'.json')
    with target.open('x')as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(str(target),result['status']);print(result.get('traceback',''))
