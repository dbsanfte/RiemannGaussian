"""Independent NEW085 saved-artifact audit; no proposer or old science replay."""
import os
for key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):os.environ[key]='1'
import gc,json,time,random,traceback,math
from pathlib import Path
from fractions import Fraction as Q
from concurrent.futures import ProcessPoolExecutor,wait,FIRST_COMPLETED
import multiprocessing as mp
import run_mobius_annihilator_085 as RUN
import check_mobius_annihilator_085 as CHECK

def read(path):return json.loads(path.read_text())
def expected_grammar(sh,eh):
    result=[]
    for a in range(1,sh):
        for b in range(1,sh-a+1):
            if a+b>sh or math.gcd(a,b)!=1:continue
            for d in range(1,eh+1):
                for c in range(-eh,eh+1):
                    if abs(c)+d>eh or math.gcd(abs(c),d)!=1:continue
                    for comp in (False,True):
                        for balanced in (False,True):
                            descriptor=dict(scale=str(Q(a,b)),u_exponent=str(Q(c,d)),complement=comp,unit_balance=balanced)
                            result.append(dict(descriptor=descriptor,cost=a+b+abs(c)+d+int(comp)+int(balanced)))
    result.sort(key=lambda r:(r['cost'],Q(r['descriptor']['u_exponent']),Q(r['descriptor']['scale']),r['descriptor']['complement'],r['descriptor']['unit_balance']))
    for i,r in enumerate(result):r['id']='a'+str(i).zfill(5)
    return result

def independently_column(model,K,balanced,meter):
    N=model['N'];E=model['effective_dimension'];column=[Q(0)]*E
    f=Q(max(K-1,0),N-1)if balanced and N>=2 else Q(0)
    for g,n in enumerate(model['coordinates']):
        value=Q(K//n-int(n==1))if K else Q(0)
        if f:value-=f*(N//n-int(n==1))
        i=model['projection_indices'][g];column[i]+=model['projection_signs'][g]*value
    meter.charge(max(1,len(model['coordinates']))*64)
    return column,sum((v*v for v in column),Q(0))

def audit_banks(out,candidates,protocol):
    grammar=expected_grammar(protocol['scale_height'],protocol['exponent_height']);parents=protocol['training_parents'];meter=CHECK.C.Meter();models={u:CHECK.C.build_model(candidates[0]['program'],u,meter)for u in parents}
    dmin=min(k['divisor']for k in candidates[0]['program']['kernel']);assert all(min(k['divisor']for k in c['program']['kernel'])==dmin for c in candidates)
    # Identity geometry depends only on N and complete prime projection, not source weights.
    columns={};representatives=[];duplicates=[];seen={};cuts_cache={}
    for item in grammar:
        desc=item['descriptor'];cuts=[]
        for u in parents:
            key=(u,desc['scale'],desc['u_exponent'],desc['complement'])
            if key not in cuts_cache:
                K=CHECK.C.floor_cut(Q(desc['scale']),Q(0),Q(desc['u_exponent']),1,u,models[u]['N'],meter)
                cuts_cache[key]=models[u]['N']-K if desc['complement']else K
            cuts.append(cuts_cache[key])
        key=(tuple(cuts),desc['unit_balance'])
        if key in seen:duplicates.append(dict(id=item['id'],representative=seen[key],reason='same cuts and balancing on training geometries only'))
        else:
            seen[key]=item['id'];representatives.append(dict(**item,cuts=cuts))
    summaries=[]
    for candidate in candidates:
        record=read(out/('bank_'+candidate['id']+'.json'));assert record['id']==candidate['id'];assert record['generated']==grammar;assert record['representatives']==representatives;assert record['training_only_duplicates']==duplicates
        witnesses={}
        for binding,u in zip(record['witness_bindings'],parents):
            assert binding['u']==u;old=read(RUN.PRIOR.OUT/binding['file']);assert old['candidate_id']==candidate['id']and old['u']==u;assert old['certificate']==binding['certificate'];assert old['admission']['status']=='VERIFIED_FINITE_FIXED_OPERATOR_SQUARE_LOWER_BOUND';witnesses[u]=binding['certificate']['signs'];assert witnesses[u][0]==1
        scores=[]
        for rep in representatives:
            vals=[]
            for u,K in zip(parents,rep['cuts']):
                key=(u,K,rep['descriptor']['unit_balance'])
                if key not in columns:columns[key]=independently_column(models[u],K,key[2],meter)
                col,norm=columns[key];assert len(witnesses[u])==len(col)
                dot=sum((v*s for v,s in zip(col,witnesses[u])),Q(0));vals.append(dot*dot/norm if norm else Q(0));meter.charge(len(col)*16+32)
            scores.append(dict(id=rep['id'],normalized_violation_by_parent=list(map(str,vals)),values=vals,nonzero_geometry=any(columns[(u,K,rep['descriptor']['unit_balance'])][1]for u,K in zip(parents,rep['cuts']))))
        rep_by_id={r['id']:r for r in representatives}
        for mode in protocol['modes']:
            choice=record['choices'][mode];assert choice['scores']==[{k:v for k,v in s.items()if k!='values'}for s in scores]
            remaining=[s for s in scores if s['nonzero_geometry']];coverage=[Q(0)]*len(parents);selected=[];steps=[]
            while remaining and len(selected)<protocol['bank_size']:
                def gain(row):return sum((v/(1+c)for v,c in zip(row['values'],coverage)),Q(0))
                best=max(remaining,key=gain)if mode=='adaptive'else remaining[0]
                value=gain(best)
                if mode=='adaptive'and not value:break
                selected.append(best['id']);remaining.remove(best);coverage=[a+b for a,b in zip(coverage,best['values'])];steps.append(dict(selected=best['id'],gain=str(value),coverage=list(map(str,coverage))))
                meter.charge(max(1,len(remaining))*len(parents)*64)
            bank=[rep_by_id[k]['descriptor']for k in selected]
            assert choice['selected_ids']==selected and choice['steps']==steps and choice['bank']==bank
            assert candidate['banks'][mode]==bank and candidate['selected_descriptor_ids'][mode]==selected
        summaries.append(dict(candidate_id=candidate['id'],generated=len(grammar),representatives=len(representatives),aliases=len(duplicates),all_complete_cut_columns_scores_and_selections_verified=True))
    return dict(summaries=summaries,independent_ops=meter.ops,unique_complete_columns=len(columns),scope='NEW085 cut/identity/score reconstruction only; no old084 source values, certificates or solver replay')

def exact_growth(price,u,hypothesis):
    j=hypothesis['j'];C=Q(hypothesis['constant']);p=Q(price)
    if p<=0:return True
    if not C:return False
    ratio=p/C
    assert j>=1 and C>=0 and j*(ratio.numerator.bit_length()+ratio.denominator.bit_length())+(j+1)*u.bit_length()<=100000
    return ratio.numerator**j<=ratio.denominator**j*u**(j+1)

def replay_admission(task):
    started=time.monotonic();c,row=task
    admitted=CHECK.verify_certificate(c['program'],row['u'],c['outer_certificate'],row['bank'],row['certificate'])
    assert admitted['status']=='VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND',admitted
    saved=row['admission']
    for key,value in admitted.items():
        if key not in ('ops','peak_bytes'):assert saved[key]==value,(row['id'],key)
    assert admitted['price']==row['certificate']['price']
    for diagnostic,key in [('cuts','cuts'),('identity_trace','identity_trace'),('factor_trace','factor_trace'),('effective_dimension','effective_dimension'),('rank','factor_rank')]:assert row['diagnostics'][diagnostic]==admitted[key]
    return dict(id=row['id'],candidate_id=c['id'],status='VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND',price=admitted['price'],independent_ops=admitted['ops'],independent_peak_bytes=admitted['peak_bytes'],elapsed_seconds=time.monotonic()-started)

def rss_bytes(pids):
    total=0
    for pid in pids:
        try:
            for row in Path('/proc/'+str(pid)+'/status').read_text().splitlines():
                if row.startswith('VmRSS:'):total+=int(row.split()[1])*1024;break
        except FileNotFoundError:pass
    return total

def audit(result):
    audit_started=time.monotonic();out=RUN.OUT;report=read(out/'report.json');assert report['status']=='COMPLETE_ADAPTIVE_ANNIHILATOR_SEARCH';protocol=read(out/'protocol.json');counts=RUN.validate_parent();assert sum(counts)==protocol['prior_byte_preserved_files']
    for name in RUN.FILES:assert (RUN.ROOT/name).read_bytes()==(out/'source_snapshot'/name).read_bytes()
    result.update(source_byte_preservation=dict(inherited=sum(counts),new_frozen=len(RUN.FILES),hashes_used=False))
    old=read(RUN.PRIOR.OUT/'frozen_candidates.json')['candidates'];roster=read(out/'frozen_operator_roster.json')['candidates'];assert roster==old
    frozen=read(out/'frozen_candidates.json');candidates=frozen['candidates'];assert len(candidates)==8
    for previous,candidate in zip(old,candidates):
        for key,value in previous.items():assert candidate[key]==value
    assert frozen['banks_frozen_before_calibration_and_draw']is True
    result['banks']=audit_banks(out,candidates,protocol);gc.collect()
    draw=read(out/'validation_draw.json');inventory=read(out/'prior_parent_inventory.json');assert inventory==RUN.inventory();excluded=set(inventory['parents']);rng=random.Random(protocol['seed']);expected=[];history=[]
    for lo,hi in protocol['validation_bands']:
        accepted=0
        while accepted<protocol['fresh_parents_per_band']:
            u=rng.randint(lo,hi);ok=u not in excluded;history.append(dict(u=u,band=[lo,hi],status='ACCEPTED'if ok else'REJECTED_PREVIOUS_OR_DUPLICATE'))
            if ok:expected.append(u);excluded.add(u);accepted+=1
    assert draw['parents']==sorted(expected)and draw['draws']==history and draw['prospective_draw_values_seen_in_preflight']is True and draw['no_validation_outcomes_seen_before_freeze']is True
    result['freshness']=dict(parents=sorted(expected),complete_rng_history_verified=True,geometry_seen_in_preflight=True,outcomes_held_out=True,new_S_and_L_each_geometry=True)
    tasks=read(out/'calibration_roster.json')['tasks']+read(out/'validation_roster.json')['tasks'];assert len(tasks)==32
    by_id={c['id']:c for c in candidates};expected_ids={c['id']+'_'+mode+'_'+str(protocol['calibration_parent'])for c in candidates for mode in protocol['modes']}|{c['id']+'_adaptive_'+str(u)for c in candidates for u in expected};assert {t['id']for t in tasks}==expected_ids
    rows=[];replays=[]
    for task in tasks:
        c=by_id[task['candidate']['id']];assert task['candidate']==c;assert task['bank']==c['banks'][task['mode']]
        row=read(out/('bound_'+task['id']+'.json'));assert row['id']==task['id']and row['candidate_id']==c['id']and row['u']==task['u']and row['mode']==task['mode']and row['stage']==task['stage']and row['bank']==task['bank'];rows.append(row)
        if row['status']=='EXACT_ANNIHILATOR_SQUARE_PROPOSAL':
            assert row['admission']['status']=='VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND';assert row['frozen_growth_tests']==[dict(**h,passes=exact_growth(row['certificate']['price'],row['u'],h))for h in c['calibrated_growth_hypotheses']]
            assert row['price_over_u2']==str(Q(row['certificate']['price'])/row['u']**2)
            assert row['price_over_u']==str(Q(row['certificate']['price'])/row['u'])
            if row['stage']=='calibration':
                saved=read(RUN.PRIOR.OUT/('search_'+c['id']+'.json'));assert saved['program']==c['program'] and saved['u']==row['u'];comparison=row['saved084_comparison'];assert comparison['price']==saved['certificate']['price'];assert comparison['exact_reduction']==str(Q(comparison['price'])-Q(row['certificate']['price']));assert comparison['same_operator']is True and comparison['same_geometry']is True
            replays.append((c,row))
    result['retained_outcomes']=[dict(id=r['id'],status=r['status'])for r in rows];result['independent_admissions']=[]
    start=audit_started;peak=0
    with ProcessPoolExecutor(max_workers=3,mp_context=mp.get_context('spawn'))as pool:
        pending={pool.submit(replay_admission,t)for t in replays}
        while pending:
            pids=[os.getpid()]+[p.pid for p in pool._processes.values()];peak=max(peak,rss_bytes(pids));assert peak<=16*1024**3
            assert time.monotonic()-start<=7200
            done,pending=wait(pending,timeout=1,return_when=FIRST_COMPLETED)
            for future in done:result['independent_admissions'].append(future.result());print('admitted',len(result['independent_admissions']),'/',len(replays),flush=True)
    good=[r for r in rows if r['status']=='EXACT_ANNIHILATOR_SQUARE_PROPOSAL'];fresh=[r for r in good if r['stage']=='validation'];cal=[r for r in good if r['stage']=='calibration']
    comparisons=[]
    for c in candidates:
        values={r['mode']:r for r in cal if r['candidate_id']==c['id']}
        if set(values)==set(protocol['modes']):
            adaptive=values['adaptive'];baseline=values['grammar_order'];comparisons.append(dict(candidate_id=c['id'],adaptive_price=adaptive['certificate']['price'],grammar_order_price=baseline['certificate']['price'],saved084_price=adaptive['saved084_comparison']['price'],adaptive_below_grammar_order=Q(adaptive['certificate']['price'])<Q(baseline['certificate']['price']),adaptive_below_saved084=Q(adaptive['certificate']['price'])<Q(adaptive['saved084_comparison']['price'])))
    result['calibration_price_comparisons']=comparisons
    assert report['operators']==8 and report['calibration_rows']==16 and report['new_auxiliary_rows']==16 and report['calibration_admitted']==len(cal)and report['new_auxiliary_admitted']==len(fresh)
    growth=[dict(j=j,passes=sum(t['passes']for r in fresh for t in r['frozen_growth_tests']if t['j']==j),tested=sum(t['j']==j for r in fresh for t in r['frozen_growth_tests']))for j in protocol['diagnostic_exponent_parameters']];assert report['growth_hypotheses_by_j']==growth
    assert len(report['outcomes'])==len(rows)and {r['id']:r['status']for r in report['outcomes']}=={r['id']:r['status']for r in rows}
    assert report['sampled_aggregate_peak_rss_bytes']<=16*1024**3 and report['elapsed_seconds']<=7200
    assert report['independent_operations']==sum(r['admission']['ops']for r in good)
    assert report['constructor_operations']==sum(r.get('ops',0)for r in rows)
    assert report['bank_selection_operations']==sum(r['ops']for r in report['bank_selection'])
    for summary in report['bank_selection']:
        bankrecord=read(out/('bank_'+summary['id']+'.json'));assert summary['ops']==bankrecord['ops'] and summary['generated']==len(bankrecord['generated'])and summary['representatives']==len(bankrecord['representatives'])
    assert all(report[k]is False for k in ('uniform_remaining_bound_proved','uniform_source_bound_proved','RH_proved','unknown_composite_signs_used','observed_full_source_values_used','hashes_used'))
    for name in RUN.FILES:assert (RUN.ROOT/name).read_bytes()==(out/'source_snapshot'/name).read_bytes()
    assert RUN.validate_parent()==counts
    result.update(status='VERIFIED_ANNIHILATOR_ARTIFACT_BINDING',growth_counts=growth,complete_outcome_count=len(rows),independent_exact_certificate_count=len(replays),sampled_audit_aggregate_peak_bytes=peak,uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,scope='All NEW085 identities/scores/certificates independently replayed; original084 scientific certificates/SCS never replayed; saved old comparison metadata only')

if __name__=='__main__':
    if not (RUN.OUT/'report.json').exists():raise SystemExit('085 report not ready; no heavy audit started')
    started=time.monotonic();result=dict(status='RUNNING',old_science_replayed=False,old_tests_run=False,hashes_used=False)
    try:audit(result)
    except Exception:result.update(status='FAIL',traceback=traceback.format_exc())
    result['elapsed_seconds']=time.monotonic()-started
    path=RUN.OUT/'independent_annihilator_artifact_audit_085.json'
    if path.exists():path=RUN.OUT/('independent_annihilator_artifact_audit_085_attempt_'+str(time.time_ns())+'.json')
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(path,result['status']);print(result.get('traceback',''))
