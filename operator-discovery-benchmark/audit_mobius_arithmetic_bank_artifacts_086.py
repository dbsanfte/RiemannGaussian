"""Independent read-only saved086 binding; never solves a numerical problem."""
import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[name]='1'
import json,time,random,copy,traceback,resource
from pathlib import Path
from fractions import Fraction as Q
from math import gcd,lcm
import numpy as np
import check_mobius_arithmetic_bank_086 as C
import run_mobius_arithmetic_bank_retry_086 as LAUNCH
RUN=LAUNCH.RUN

LOW='VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND'
UP='VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND'
GAIN='VERIFIED_FINITE_ARITHMETIC_BANK_INFORMATION_GAIN'
def read(name):return json.loads((RUN.OUT/name).read_text())
def require(condition,message):
    if not condition:raise ValueError(message)
def old_descriptors(sh,eh):
    scales=[Q(a,b)for a in range(1,sh)for b in range(1,sh-a+1)if gcd(a,b)==1]
    exps=[Q(a,b)for b in range(1,eh+1)for a in range(-eh,eh+1)if abs(a)+b<=eh and gcd(abs(a),b)==1]
    out=[]
    for a in scales:
        for e in exps:
            for complement in (False,True):
                for balanced in (False,True):
                    d=dict(scale=str(a),u_exponent=str(e),complement=complement,unit_balance=balanced)
                    out.append(dict(descriptor=d,cost=a.numerator+a.denominator+abs(e.numerator)+e.denominator+int(complement)+int(balanced)))
    return sorted(out,key=lambda r:(r['cost'],Q(r['descriptor']['u_exponent']),Q(r['descriptor']['scale']),r['descriptor']['complement'],r['descriptor']['unit_balance']))
def grammar(memory,spec):
    out=[dict(descriptor=dict(kind='divisor',cut=r['descriptor']),cost=r['cost'])for r in old_descriptors(spec['divisor_scale_height'],spec['exponent_height'])]
    for r in old_descriptors(spec['prime_scale_height'],spec['exponent_height']):
        if r['descriptor']['unit_balance']:continue
        cut={k:v for k,v in r['descriptor'].items()if k!='unit_balance'}
        for domain in ('prime','cofactor'):
            for w in [dict(kind='one')]+[dict(kind='source',i=i)for i in range(memory+1)]:out.append(dict(descriptor=dict(kind='prime_pair',cut_on=domain,cut=cut,weight=w),cost=r['cost']+2+w.get('i',-1)+1))
    out.sort(key=lambda r:r['cost'])
    for i,r in enumerate(out):r['id']='g'+str(i).zfill(5)
    return out

def independent_catalog(program,u,generated):
    m=C.C.Meter();model=C.C.build_model(program,u,m);N=model['N'];E=model['effective_dimension'];G=model['squarefree_count']
    require(E<=512,'audit complete dimension');cuts={};seen={};representatives=[];aliases=[];columns={};forms={}
    base_peak=m.peak_bytes;require(len(generated)*8192<1024**3,'audit grammar prospective budget');m.reserve(base_peak+len(generated)*8192+16*(N+1)*(E+1)*16)
    for item in generated:
        d=item['descriptor'];cut=d['cut'];keycut=(cut['scale'],cut['u_exponent'],cut['complement'])
        if keycut not in cuts:
            K=C.C.floor_cut(Q(cut['scale']),Q(0),Q(cut['u_exponent']),1,u,N,m);cuts[keycut]=N-K if cut['complement']else K
        K=cuts[keycut];form=('divisor',cut['unit_balance'])if d['kind']=='divisor'else('prime_pair',d['cut_on'],d['weight']['kind'],d['weight'].get('i'))
        key=form+(K,)
        if key in seen:aliases.append(dict(id=item['id'],representative=seen[key],scope='same cutoff/form at training geometry only'));continue
        seen[key]=item['id'];representatives.append(dict(**item,cut=K));forms.setdefault(form,set()).add(K)
    prospective=base_peak+len(generated)*8192+len(representatives)*(1024+64*E)+2*(N+1)*(E+1)*16+len(representatives)*8192
    require(prospective<=4*1024**3,'audit catalog and score complete residency');m.reserve(prospective);m.charge(max(1,len(representatives)*E)*64)
    coordinates=model['coordinates'];positions={n:i for i,n in enumerate(coordinates)};primes=C.C.is_prime_table(N,m);roster=[n for n in range(2,N+1)if primes[n]];formcols={}
    for form,needed in forms.items():
        if form[0]=='divisor':
            for K in needed:
                factor=Q(max(K-1,0),N-1)if form[1]and N>=2 else Q(0);raw=[(Q(K//n-int(n==1))if K else Q(0))-factor*Q(N//n-int(n==1))for n in coordinates];v=[Q(0)]*E
                for g,x in enumerate(raw):v[model['projection_indices'][g]]+=model['projection_signs'][g]*x
                den=lcm(*(x.denominator for x in v))if v else 1;column=[int(x*den)for x in v];formcols[form+(K,)]=(column,den,0)
        else:
            domain,kind,index=form[1:];weights=[Q(1)if kind=='one'else row[index]for row in model['features']];den=lcm(*(x.denominator for x in weights))if weights else 1;ints=[int(x*den)for x in weights]
            require(max([abs(x).bit_length()for x in ints]+[0])+2*N.bit_length()<60,'audit prospective integer prefix bits')
            table=np.zeros((N+1,E),dtype=np.int64);counts=np.zeros(N+1,dtype=np.int64)
            for prime in roster:
                for g,n in enumerate(coordinates):
                    if n>N//prime:break
                    if n%prime==0:continue
                    h=positions[prime*n];k=prime if domain=='prime'else n;counts[k]+=1
                    table[k,model['projection_indices'][g]]+=model['projection_signs'][g]*ints[g];table[k,model['projection_indices'][h]]+=model['projection_signs'][h]*ints[g];m.charge(32)
            np.cumsum(table,axis=0,out=table);np.cumsum(counts,out=counts)
            for K in needed:formcols[form+(K,)]=([int(x)for x in table[K]],den,int(counts[K]))
    for item in representatives:
        d=item['descriptor'];form=('divisor',d['cut']['unit_balance'])if d['kind']=='divisor'else('prime_pair',d['cut_on'],d['weight']['kind'],d['weight'].get('i'));columns[item['id']]=formcols[form+(item['cut'],)]
    return dict(representatives=representatives,training_only_duplicates=aliases,columns=columns,ops=m.ops,peak_bytes=m.peak_bytes)

def trigger(value,u,j,constant):
    v=Q(value);c=Q(constant)
    return v>0 and v.numerator**j*c.denominator**j>v.denominator**j*c.numerator**j*u**(j+1)
def score_choice(catalog,signs,union,meter=None):
    meter=meter or C.C.Meter();require(type(signs)is list and all(type(s)is int and s in(-1,1)for s in signs)and(not signs or signs[0]==1),'audit exact anchored score signs');meter.reserve(catalog['peak_bytes']+len(catalog['representatives'])*8192)
    out=[];best=None
    for item in catalog['representatives']:
        if not union and item['descriptor']['kind']!='divisor':continue
        col,den,_=catalog['columns'][item['id']];require(len(col)==len(signs),'complete score shape');bits=max([abs(x).bit_length()for x in col]+[0])+max(1,len(col).bit_length());require(2*bits<=4096,'audit prospective score bits')
        meter.charge(32*len(col)+64);dot=sum(a*s for a,s in zip(col,signs));norm=sum(a*a for a in col);score=Q(dot*dot,norm)if norm else Q(0);row=dict(id=item['id'],score=str(score),violation=str(Q(dot,den)));out.append(row)
        if score and(best is None or score>best[0]):best=(score,item,row)
    return out,best

def audit_operator(candidate):
    started=time.monotonic();counts=dict(lower=0,upper=0,extensions=0,scores=0,exact_attempts=0,failed_attempts=0);cid=candidate['id'];spec=read('protocol.json');u=spec['training_parent'];bankrow=read('bank_'+cid+'.json');cache={};events=[]
    def lower(filename):
        if filename in cache:return cache[filename]
        row=read(filename);require(row['candidate_id']==cid,'lower candidate');require(row['bank']is not None,'lower complete bank')
        require(row.get('highs_threads_requested')==1,'all lower HiGHS threads1')
        if 'native_environment'in row:require(all(v=='1'for v in row['native_environment'].values()),'lower numerical environment1')
        for attempt in row.get('attempts',[]):
            if 'highs_threads_requested'in attempt:require(attempt['highs_threads_requested']==1,'MILP attempt threads1')
            events.append(dict(file=filename,attempt=attempt.get('name'),status=attempt.get('status'),scope='saved lower proposal attempt; not silently discarded',warnings=attempt.get('warnings',[]),reason=attempt.get('reason')))
        if row.get('admission',{}).get('status')==LOW:
            result=C.verify_lower(candidate['program'],row['u'],candidate['outer_certificate'],row['bank'],row['certificate']);require(result['status']==LOW,'lower replay '+filename+str(result));counts['lower']+=1
            if 'excludes_frozen_target'in row:require(row['excludes_frozen_target']==trigger(row['certificate']['lower_bound'],row['u'],spec['trigger_j'],spec['trigger_constant']),'lower exact trigger')
            if 'lower_bound_over_u'in row:require(Q(row['lower_bound_over_u'])==Q(row['certificate']['lower_bound'])/row['u'],'lower normalization')
        else:events.append(dict(file=filename,status=row['status'],scope='retained unadmitted lower outcome'))
        cache[filename]=row;return row
    if bankrow['status']=='COMPLETE_ARITHMETIC_ENRICHMENT':
        generated=grammar(candidate['program']['memory'],spec);saved=read('catalog_'+cid+'.json');require(saved['generated']==generated,'independent complete grammar');catalog=independent_catalog(candidate['program'],u,generated);score_meter=C.C.Meter();require(saved['representatives']==catalog['representatives'],'canonical representatives');require(saved['training_only_duplicates']==catalog['training_only_duplicates'],'complete aliases');shared=lower(bankrow['shared_initial_witness_file']);require(shared['bank']==candidate['initial_bank'],'common initial bank')
        for mode in spec['modes']:
            arm=bankrow['arms'][mode];bank=copy.deepcopy(candidate['initial_bank'])
            for step in arm['steps']:
                row=lower(step['witness_file']);require(step['old_bank']==bank==row['bank'],'cumulative lower bank');require(row['status']=='EXACT_COMPATIBLE_BANK_WITNESS_PROPOSAL'and row['excludes_frozen_target'],'extension admitted exact trigger');scores,best=score_choice(catalog,row['certificate']['signs'],mode=='union',score_meter);counts['scores']+=len(scores);require(step['choice']['scores']==scores,'all exact scores');require(step['choice']['selected']==(best[1]if best else None),'maximum score stable tie');require(step['choice']['selected_score']==(best[2]if best else None),'chosen exact score')
                if step['status']=='EXACT_INFORMATION_GAIN':
                    added=best[1]['descriptor'];r=C.verify_extension(candidate['program'],u,candidate['outer_certificate'],bank,row['certificate'],added);require(r['status']==GAIN,'extension replay');require(Q(r['new_identity_dot'])==Q(step['extension_admission']['new_identity_dot']),'extension exact dot');bank.append(copy.deepcopy(added));require(step['new_bank']==bank,'new bank append');counts['extensions']+=1
                else:events.append(dict(status=step['status'],scope='retained enrichment stop'))
            require(arm['bank']==bank==candidate['banks'][mode],'frozen learned bank');require(arm['added_count']==len(bank)-len(candidate['initial_bank']),'addition count');lower(arm['final_witness_file'])
    else:events.append(dict(file='bank_'+cid+'.json',status=bankrow['status'],scope='retained failed enrichment'))
    for path in sorted(RUN.OUT.glob('witness_'+cid+'*.json')):lower(path.name)
    for path in sorted(RUN.OUT.glob('bound_'+cid+'*.json')):
        row=read(path.name);require(row['candidate_id']==cid,'upper candidate');expected=candidate['initial_bank']if row['mode']=='initial'else candidate['banks'][row['mode']];require(row['bank']==expected,'upper frozen bank')
        if row['status']=='EXACT_MIXED_ZERO_SQUARE_PROPOSAL':
            certificates=[('chosen',row['certificate'])]+[(a['name'],a['certificate'])for a in row.get('attempts',[])if a['status']=='EXACT_CERTIFICATE']
            if 'search_certificate'in row:certificates.append(('saved_search',row['search_certificate']))
            inherited=row.get('inherited_incumbent',{})
            if inherited.get('status')=='EXACT_EMBEDDED_INCUMBENT':
                initial=read(inherited['source_file']);embedded=copy.deepcopy(initial['certificate']);embedded['partner_matrix']=[r+['0']*(len(row['bank'])-len(initial['bank']))for r in embedded['partner_matrix']];require(inherited['certificate']==embedded,'exact incumbent zero-padding');certificates.append(('embedded',embedded));require(Q(row['certificate']['price'])<=Q(initial['certificate']['price']),'incumbent retention')
            seen=set()
            for label,cert in certificates:
                key=json.dumps(cert,sort_keys=True)
                if key in seen:continue
                seen.add(key);r=C.verify_upper(candidate['program'],row['u'],candidate['outer_certificate'],row['bank'],cert);require(r['status']==UP,'upper exact replay '+path.name+' '+label+str(r));counts['exact_attempts']+=1
            counts['upper']+=1;require(Q(row['price_over_u'])==Q(row['certificate']['price'])/row['u'],'upper normalization')
            for h in row['frozen_growth_tests']:require(h['passes']==(not trigger(row['certificate']['price'],row['u'],h['j'],h['constant'])),'frozen exact growth')
            witness_name=row.get('witness_file')
            if row['stage']=='training'and row['mode']in spec['modes']and bankrow['status']=='COMPLETE_ARITHMETIC_ENRICHMENT':witness_name=bankrow['arms'][row['mode']]['final_witness_file']
            if witness_name:
                witness=lower(witness_name);require(witness['bank']==row['bank']and witness['u']==row['u'],'same bank lower/upper');
                if witness['status']=='EXACT_COMPATIBLE_BANK_WITNESS_PROPOSAL':require(Q(witness['certificate']['lower_bound'])<=Q(row['certificate']['price']),'compatible lower<=upper')
        else:
            events.append(dict(file=path.name,status=row['status'],scope='retained failed upper outcome'))
            for a in row.get('attempts',[]):
                if a['status']=='EXACT_CERTIFICATE':
                    r=C.verify_upper(candidate['program'],row['u'],candidate['outer_certificate'],row['bank'],a['certificate']);require(r['status']==UP,'retained attempt admission '+path.name+str(r));counts['exact_attempts']+=1
        if row.get('search_failure'):events.append(dict(file=path.name,status='RETAINED_SEARCH_FAILURE',details=row['search_failure']))
        for a in row.get('attempts',[]):
            if a['status']!='EXACT_CERTIFICATE':counts['failed_attempts']+=1;events.append(dict(file=path.name,attempt=a.get('name'),status=a['status'],reason=a.get('reason'),error_type=a.get('error_type')))
    return dict(id=cid,counts=counts,retained_nonadmissions=events,score_operations=score_meter.ops if bankrow['status']=='COMPLETE_ARITHMETIC_ENRICHMENT'else 0,elapsed_seconds=time.monotonic()-started,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,peak_rss_bytes=1024*resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)

def main():
    started=time.monotonic();target=RUN.OUT/'independent_arithmetic_bank_artifact_audit_086.json';require(not target.exists(),'preserve previous audit attempt');result=dict(status='FAIL',uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,numerical_optimizers_rerun=False)
    try:
        report=read('report.json');spec=read('protocol.json');
        for key,value in RUN.SPEC.items():require(spec.get(key)==value,'frozen code protocol '+key)
        require(spec['source_files']==RUN.FILES,'frozen corrected source list');RUN.POOL.stage_check(started,[os.getpid()]);manifest=RUN.read(LAUNCH.ABORTED_OUT/'abort_manifest.json');require(manifest['status']=='ABORTED_CONFIRMED_IMPORT_ORDER_THREAD_GUARD_FAILURE'and manifest['witness_files']==8 and manifest['upper_files']==0 and not manifest['fresh_draw_reached'],'aborted launch scope');require(not list(LAUNCH.ABORTED_OUT.glob('bound_*.json'))and not(LAUNCH.ABORTED_OUT/'validation_draw.json').exists(),'aborted no bounds or fresh draw');require(spec['arithmetic_and_search_policy_unchanged'],'corrected launcher only');require(report['status']=='COMPLETE_COUNTEREXAMPLE_ARITHMETIC_BANK_SEARCH','science complete');counts=RUN.validate_parent();require(sum(counts)==report['prior_frozen_files']==spec['prior_byte_preserved_files'],'prior direct byte preservation')
        for name in RUN.FILES:
            RUN.POOL.stage_check(started,[os.getpid()]);require((RUN.ROOT/name).read_bytes()==(RUN.OUT/'source_snapshot'/name).read_bytes(),'086 snapshot '+name)
        old=RUN.read(RUN.PRIOR.OUT/'frozen_candidates.json')['candidates'];candidates=read('frozen_candidates.json')['candidates'];require(len(candidates)==len(old)==8,'all eight original operators')
        for c,p in zip(candidates,old):
            for key in ('id','source_id','family_id','program','outer_certificate','calibrated_growth_hypotheses'):require(c[key]==p[key],'fixed operator/source binding '+key)
            require(c['initial_bank']==[dict(kind='divisor',cut=d)for d in p['banks']['adaptive']],'initial085 bank')
        require(read('prior_parent_inventory.json')==RUN.inventory(),'independent prior inventory linkage');draw=read('validation_draw.json');rng=random.Random(spec['validation_seed']);excluded=set(read('prior_parent_inventory.json')['parents']);parents=[];draws=[]
        for lo,hi in spec['validation_bands']:
            count=0
            while count<spec['fresh_parents_per_band']:
                u=rng.randint(lo,hi);ok=u not in excluded;draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED'if ok else'REJECTED_PREVIOUS_OR_DUPLICATE'))
                if ok:parents.append(u);excluded.add(u);count+=1
        require(draw['parents']==sorted(parents)and draw['draws']==draws and draw['seed']==spec['validation_seed'],'fresh deterministic no-redraw draw')
        for name,modes,us,stage in [('initial_upper_roster.json',['initial'],[spec['training_parent']],'training'),('training_upper_roster.json',spec['modes'],[spec['training_parent']],'training'),('validation_roster.json',spec['modes'],sorted(parents),'validation')]:
            expected=[t for u in us for t in RUN.upper_roster(candidates,modes,u,stage)];require(read(name)['tasks']==expected,'complete roster '+name)
        native_counts={}
        for kind,expected in [('learn',8),('upper',40)]:
            receipts=list(RUN.OUT.glob('native_'+kind+'_*.json'));require(len(receipts)==expected,'all native '+kind+' receipts');native_counts[kind]=len(receipts)
            for path in receipts:
                RUN.POOL.stage_check(started,[os.getpid()]);receipt=read(path.name)
                for side in ('before','after'):
                    snap=receipt[side];require(all(v=='1'for v in snap['environment'].values())and snap['pools']and all(p['num_threads']==1 for p in snap['pools']),'native actual pool/environment1 '+path.name)
        RUN.POOL.stage_check(started,[os.getpid()]);results=RUN.POOL.pool_tasks(audit_operator,candidates,started,'independent_saved086_artifact_binding');RUN.POOL.stage_check(started,[os.getpid()])
        totals={key:sum(r['counts'][key]for r in results)for key in results[0]['counts']};bounds=[read(p.name)for p in sorted(RUN.OUT.glob('bound_*.json'))];good=[r for r in bounds if r['status']=='EXACT_MIXED_ZERO_SQUARE_PROPOSAL'];fresh=[r for r in good if r['stage']=='validation'];require(len(bounds)==report['upper_rows']and len(good)==report['upper_admitted']and len(fresh)==report['validation_upper_admitted'],'all outcome counts')
        require({r['id']for r in bounds}=={r['id']for r in report['outcomes']},'outcome inventory')
        for summary in report['growth_hypotheses_by_j']:
            terms=[h for row in fresh for h in row['frozen_growth_tests']if h['j']==summary['j']];require(summary['tested']==len(terms)and summary['passes']==sum(h['passes']for h in terms),'growth aggregate')
        require(report['sampled_aggregate_peak_rss_bytes']<=spec['max_aggregate_bytes'],'sampled resource cap');require(not report['uniform_remaining_bound_proved']and not report['RH_proved'],'scope flags');result.update(status='VERIFIED_ARITHMETIC_BANK_ARTIFACT_BINDING',counts=totals,operators=results,source_bytes_preserved=sum(counts)+len(RUN.FILES),sampled_aggregate_peak_rss_bytes=RUN.POOL._PEAK,conservative_worker_peak_sum_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+3*max(r['worker_peak_rss_kib']for r in results)),native_thread_receipts=native_counts,aborted_attempt_scope=dict(witnesses=8,upper=0,fresh_draw=False,all_source_and_artifact_bytes_preserved=True),validation_parents=sorted(parents),growth=report['growth_hypotheses_by_j'],all_failure_rows_retained=True,complete_prime_cofactor_unit_projection=True)
    except Exception as exc:result.update(error=str(exc),traceback=traceback.format_exc())
    RUN.POOL.stage_check(started,[os.getpid()]);result['elapsed_seconds']=time.monotonic()-started;target.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ('operators','traceback')},indent=2))
    if result['status']=='FAIL':raise SystemExit(1)
if __name__=='__main__':main()
