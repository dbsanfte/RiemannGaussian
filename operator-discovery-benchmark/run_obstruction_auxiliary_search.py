"""Frozen two-generation obstruction/auxiliary/argument experiment."""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction as Q
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

from flint import arb, ctx
import obstruction_auxiliary_search as P
import obstruction_bound_certificates as B

ROOT=Path(__file__).resolve().parent
TRAIN=[1,2,4,8,16,64,256,1024]
VALIDATION=[2048,4096]
FINAL=[8192,16384]
TOTAL=350000000
SECONDS=7200
RESERVE=1000000
TESTS=['test_obstruction_auxiliary_search','test_obstruction_bound_certificates',
       'test_run_obstruction_auxiliary_search']
RECEIPTS=['obstruction_auxiliary_development.json','obstruction_certificate_development.json',
          'obstruction_workflow_development.json']
SOURCES=['obstruction_auxiliary_search.py','check_obstruction_auxiliary.py',
         'obstruction_bound_certificates.py','run_obstruction_auxiliary_search.py',
         'obstruction_auxiliary_protocol.txt','shifted_quotient_candidates.py',
         'check_shifted_quotient_candidates.py','SHIFTED_QUOTIENT_CANDIDATE_10_REVIEW_001.txt',
         'OBSTRUCTION_AUXILIARY_ANALYTIC_REVIEW_001.txt',
         'OBSTRUCTION_AUXILIARY_STRUCTURE_REVIEW_001.txt']+[n+'.py' for n in TESTS]+RECEIPTS
FAILURES=(ValueError,ArithmeticError,OverflowError,TimeoutError,MemoryError)


def read(path):
    raw=Path(path).read_bytes()
    if len(raw)>16*1024**2: raise OverflowError('bounded result artifact')
    return json.loads(raw)


def write(path,data):
    raw=(json.dumps(data,indent=2,sort_keys=True,allow_nan=False)+'\n').encode()
    if len(raw)>16*1024**2: raise OverflowError('bounded result artifact')
    with Path(path).open('xb') as f:f.write(raw)


def checkpoint(path,data):
    with Path(path).open('a') as f:
        f.write(json.dumps(data,sort_keys=True,allow_nan=False)+'\n');f.flush()


def receipts():
    out={}
    for name in RECEIPTS:
        data=read(ROOT/name)
        if not data['runs'] or data['runs'][-1]['returncode']!=0 or data['operations']!=sum(r['operations'] for r in data['runs']):
            raise ValueError('complete passed cumulative development receipt '+name)
        out[name]=data
    return out


def specification():
    return dict(schema='obstruction-auxiliary-pilot-v1',target=P.TARGET,initial_programs=P.catalogue(),
                train=TRAIN,validation=VALIDATION,final=FINAL,
                feedback='all four shift/average x cube/square-root productions on one unresolved joint state per lane',
                ranking=['reviewed padding availability','positive correction power loss','validation failures','complexity','ordinal id'],
                final_adaptation=False,prior_arithmetic_overlap=True,work_limit=TOTAL,seconds=SECONDS,
                memory_bytes=16*1024**3,process_memory_bytes=4*1024**3,hashes=False,
                development=receipts(),uniform_signed_bound_proved=False,RH_proved=False)


def freeze(directory):
    directory=Path(directory).resolve();data=specification()
    files={n:(ROOT/n).read_bytes() for n in SOURCES}
    if directory.exists():raise FileExistsError('new immutable experiment directory')
    directory.mkdir(parents=True);(directory/'source_snapshot').mkdir()
    for n,raw in files.items():(directory/'source_snapshot'/n).write_bytes(raw)
    write(directory/'source_files.json',SOURCES);write(directory/'protocol.json',data)


def verify_source(directory):
    if read(directory/'source_files.json')!=SOURCES:raise ValueError('source manifest')
    for n in SOURCES:
        if (ROOT/n).read_bytes()!=(directory/'source_snapshot'/n).read_bytes():raise ValueError('changed frozen source '+n)
    if read(directory/'protocol.json')!=specification():raise ValueError('changed frozen specification')


def tight(v):return v.is_finite() and v.rad()<=arb(2)**(-65)*(1+abs(v.mid()))


def compare(saved,current):
    if set(saved)!=set(current) or saved['X']!=current['X']:raise ValueError('same complete case fields')
    for k in saved:
        if k=='X':continue
        value=arb(saved[k])
        if not tight(value) or not tight(current[k]) or not value.overlaps(current[k]):
            raise ArithmeticError('independent tight finite disagreement '+k)


def ceiling(value):
    return str(Q(max(0,int((value.upper()*2**32).ceil().unique_fmpz())),2**32))


def argument(program,constant,base_bound,meter):
    scope=P.SCOPE;nodes=[];premises=[];equivalences=[];reviews=[]
    def node(identity,kind,statement,status='open',rule='obligation',deps=None,certificate=None):
        nodes.append(dict(id=identity,kind=kind,statement=statement,status=status,rule=rule,
                          dependencies=[] if deps is None else deps,certificate=certificate,scope=scope))
    def premise(identity,kind,statement,provenance):
        premises.append(dict(id=identity,kind=kind,statement=statement,status='proven',provenance=provenance,scope=scope))
    provenance='OBSTRUCTION_AUXILIARY_ANALYTIC_REVIEW_001.txt; complete shift/average correction and Young argument'
    rho=program.get('rho','1')
    cert=B.recurrence_certificate(rho,constant,1,base_bound,F='F',step_id='step',base_id='base',meter=meter)
    node('step','uniform_bound',cert['premises']['step'])
    premise('base','base_bound',cert['premises']['base'],
            'upward rational bound on complete X=1 Arb evaluation; independently audited with every training block')
    node('growth','uniform_bound','F(X) has the conditional bounded/logarithmic growth specified by its certificate',
         rule='dyadic_recurrence',deps=['step','base'],certificate=cert)
    if program['family']=='transport':
        algebra=B.transport_certificate(program['a0'],program['a1'],meter=meter)
        node('transport','algebra',algebra['conclusion'],status='proven',rule='dyadic_transport',certificate=algebra)
    elif program['family'] in ('pair','feedback_pair'):
        expected_weights=['2','2'] if program['family']=='pair' else ['4','4','2']
        if program['weights']!=expected_weights or len(program['terms'])!=len(expected_weights):
            raise ValueError('exact complete Young majorant weights')
        if not P.linear_identity([('1',P.atom('R'))]+[('-1',t) for t in program['terms']]):
            raise ValueError('argument bound to complete expression identity')
        premise('recombination','algebra','R is the exact signed sum of every supplied state term',
                'exact free-linear AST normalization in obstruction_auxiliary_search.linear_identity')
        algebra=B.young_certificate('1',meter=meter)
        node('young','algebra','Young domination conditional on R=U+D',status='proven',rule='young_split',
             deps=['recombination'],certificate=algebra)
        if program['family']=='feedback_pair':
            node('nested_young','algebra','Young domination for U=U2+D2 with the previous correction retained',
                 status='proven',rule='young_split',deps=['recombination'],
                 certificate=B.young_certificate('1',U='U2',D='D2',R='U',meter=meter))
    node('target','uniform_bound',P.TARGET['formula']+' <= C_epsilon*X^epsilon uniformly')
    if program['family'] in ('pair','feedback_pair'):
        node('joint','uniform_bound','complete energy of first transformed state <= C_epsilon*X^epsilon uniformly')
        if program['padding_polylog_proved']:
            premise('padding','uniform_bound','Every retained correction energy is O((1+log X)^3), with full constants and boundaries',provenance)
            equivalences.append(dict(id='paid_padding_equivalence',left='target',right='joint',provenance=provenance,scope=scope))
    domination=['growth']+[n['id'] for n in nodes if n['kind']=='algebra']
    node('via_drift','uniform_bound','complete E_R(X)<=C_epsilon X^epsilon uniformly',rule='reviewed_implication',
         deps=domination,certificate={'review_id':'target_domination'})
    reviews.append(dict(id='target_domination',premises=domination,conclusion='via_drift',scope=scope,
                        provenance='exact complete F>=E_R; '+provenance))
    equivalences.append(dict(id='same_target',left='target',right='via_drift',scope=scope,
                             provenance='identical complete target expression and full cofinal quantifiers'))
    graph=dict(schema=B.GRAPH_SCHEMA,scope=scope,premises=premises,nodes=nodes,reviewed_rules=reviews,
               equivalences=equivalences,goals=['target','via_drift']+(['joint'] if program['family'] in ('pair','feedback_pair') else []))
    return dict(graph=graph,verification=B.verify_graph(graph,meter),next_obligations=P.next_obligations(program),
                full_uniform_estimate_proved=False,new_target_exponent_proved=None)


def evaluate_discovery(program,state,meter,directory):
    training=[P.measure(program,X,state,meter) for X in TRAIN]
    constant=P.fitted_drift(training,meter);base=ceiling(training[0]['majorant'])
    checkpoint(directory/'discovery_checkpoints.jsonl',dict(stage='fit_before_validation',id=program['id'],
                                                          constant=constant,operations=meter.operations))
    validation=[P.measure(program,X,state,meter) for X in VALIDATION]
    row=dict(program=program,training=[P.encoded(r) for r in training],validation=[P.encoded(r) for r in validation],
             constant=constant,base_bound=base,validation_score=P.score(validation,constant,meter),
             argument=argument(program,constant,base,meter))
    checkpoint(directory/'discovery_checkpoints.jsonl',dict(stage='complete_candidate',record=row,operations=meter.operations))
    return row


def final_selection(records):
    out=[next(r for r in records if r['program']['family']=='baseline')]
    for lane in ('shift_T','shift_V','average_T','average_V'):
        choices=[r for r in records if r['program']['lane']==lane and r['program'].get('exponent')!='0']
        out.append(min(choices,key=P.rank))
    for critical in (False,True):
        choices=[r for r in records if r['program']['family']=='transport' and (Q(r['program']['rho'])==1)==critical]
        out.append(min(choices,key=lambda r:(r['validation_score']['failed'],r['program']['id'])))
    return out


def audit_worker(directory,stage,records,H,cap,deadline):
    import check_obstruction_auxiliary as C
    ctx.prec=192
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))
    meter=P.P.Meter(cap);meter.deadline=deadline
    checked=[];reason=None
    try:
        state=C.source_state(H,meter)
        for record in records:
            p=record['program'];cases=record.get('cases',record.get('training',[])+record.get('validation',[]))
            fresh=[]
            for old in cases:
                current=C.measure(p,old['X'],state,meter);compare(old,current);fresh.append(current)
            if 'argument' in record:B.verify_graph(record['argument']['graph'],meter)
            if 'training' in record:
                # Recompute fitted constants and scores from independently evaluated cases.
                if P.fitted_drift(fresh[:len(TRAIN)],meter)!=record['constant']:raise ArithmeticError('exact upward training fit')
                if not fresh[0]['majorant']<=P.P.real(record['base_bound']):raise ArithmeticError('complete initial bound')
                score=P.score(fresh[len(TRAIN):],record['constant'],meter)
                if score['passed']!=record['validation_score']['passed']:raise ArithmeticError('frozen validation decisions')
            else:
                score=P.score(fresh,record['constant'],meter)
                if score['passed']!=record['score']['passed']:raise ArithmeticError('frozen final decisions')
            row=dict(id=p['id'],cases=len(cases));checked.append(row)
            checkpoint(Path(directory)/('audit_'+stage+'_checkpoints.jsonl'),dict(**row,operations=meter.operations))
        status='verified'
    except FAILURES as error:
        status='incomplete';reason=str(error) or type(error).__name__
    return dict(stage=stage,status=status,reason=reason,checked=checked,counts=meter.counts(),
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def run(directory):
    directory=Path(directory).resolve();verify_source(directory)
    started=time.monotonic();deadline=started+SECONDS
    write(directory/'started.json',dict(attempt=1,monotonic=started))
    development=sum(d['operations'] for d in receipts().values())
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=120)
    matches=re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$',tests.stdout,re.M)
    frozen=sum(int(n) for _,n in matches)
    write(directory/'frozen_tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr,operations=frozen))
    if tests.returncode or sorted(m for m,_ in matches)!=sorted(TESTS):raise RuntimeError('one complete frozen suite')
    spent=development+frozen+RESERVE
    ctx.prec=128;meter=P.P.Meter(min(130000000,TOTAL-spent));meter.deadline=deadline
    initial=P.catalogue()
    possible=initial+[P.feedback(p,1000+i,mode,a) for i,p in enumerate(initial) if p['family']=='pair'
                     for mode in ('shift','average') for a in ('1/3','1/2')]
    H=P.required_horizon(possible,TRAIN+VALIDATION)
    records=[]
    try:
        state=P.source_state(H,meter)
        for p in initial:records.append(evaluate_discovery(p,state,meter,directory))
        parents=P.select_parents(records);children=[]
        for p in parents:
            parent_record=next(r for r in records if r['program']['id']==p['id'])
            review=parent_record['argument']
            if not any('joint' in leaf['members'] for leaf in review['verification']['undischarged_leaves']):
                raise ValueError('feedback requires a checker-retained unresolved joint obligation')
            obligation=next(o for o in review['next_obligations'] if o['id']=='joint_energy_'+str(p['id']))
            for mode in ('shift','average'):
                for a in ('1/3','1/2'):
                    children.append(P.generate_from_obligation(obligation,p,len(initial)+len(children),mode,a))
        write(directory/'feedback_batch.json',dict(parent_ids=[p['id'] for p in parents],
                                                  programs=children,source_obligations=[P.next_obligations(p) for p in parents]))
        for p in children:records.append(evaluate_discovery(p,state,meter,directory))
        del state
        selected=final_selection(records)
        write(directory/'discovery.json',dict(records=records,horizon=H,counts=meter.counts()))
        write(directory/'final_batch.json',dict(records=selected,scales=FINAL))
        print(json.dumps(dict(stage='discovery',programs=len(records),selected=[r['program']['id'] for r in selected],
                              operations=meter.operations)),flush=True)
        final_H=P.required_horizon([r['program'] for r in selected],FINAL)
        state=P.source_state(final_H,meter);final=[]
        for row in selected:
            cases=[P.measure(row['program'],X,state,meter) for X in FINAL]
            result=dict(program=row['program'],constant=row['constant'],cases=[P.encoded(c) for c in cases],
                        score=P.score(cases,row['constant'],meter))
            final.append(result);checkpoint(directory/'final_checkpoints.jsonl',dict(record=result,operations=meter.operations))
        del state
    except FAILURES as error:
        write(directory/'incomplete.json',dict(reason=str(error),operations=spent+meter.operations,
                                               uniform_signed_bound_proved=False,RH_proved=False));return
    spent+=meter.operations
    write(directory/'final.json',dict(records=final,horizon=final_H,counts=meter.counts()))
    available=TOTAL-spent;audits=[]
    with ProcessPoolExecutor(max_workers=2) as pool:
        futures=[pool.submit(audit_worker,str(directory),stage,rows,cutoff,available//2,deadline)
                 for stage,rows,cutoff in (('discovery',records,H),('final',final,final_H))]
        for future in as_completed(futures):
            result=future.result();audits.append(result);spent+=result['counts']['operations']
            write(directory/('audit_'+result['stage']+'.json'),result)
            print(json.dumps(dict(stage='independent_'+result['stage'],status=result['status'],total_operations=spent)),flush=True)
    verify_source(directory)
    checked=sum(r['cases'] for audit in audits for r in audit['checked']);expected=len(records)*(len(TRAIN)+len(VALIDATION))+len(final)*len(FINAL)
    verified=all(a['status']=='verified' for a in audits) and checked==expected and spent<=TOTAL
    write(directory/'report.json',dict(status='FINITE_AUXILIARIES_AND_ARGUMENT_GRAPHS_VERIFIED' if verified else 'INCOMPLETE',
                                      target=P.TARGET,generation_counts=[len(initial),len(children)],
                                      selected=[dict(id=r['program']['id'],family=r['program']['family'],score=r['score'],
                                                     constant=r['constant']) for r in final],
                                      checked_cases=checked,expected_cases=expected,total_operations=spent,
                                      preparation_operations=development+frozen+RESERVE,producer_operations=meter.operations,
                                      audit_operations=sum(a['counts']['operations'] for a in audits),elapsed_seconds=time.monotonic()-started,
                                      generated_from_unresolved_obligations=len(children),new_target_bounds_proved=0,
                                      uniform_signed_bound_proved=False,RH_proved=False,
                                      next_search_target='complete remaining joint covariance; largest-prime three-channel transfer with smooth complement'))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('action',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();globals()[args.action](args.directory)
