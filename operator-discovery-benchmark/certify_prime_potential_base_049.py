"""Discharge the complete finite base of the fixed048 argument, without fitting.

Protocol fixed here before evaluation: all integers M..2M-1 from the selected
argument, unchanged profiles/Gram/A/eta, independent exact source replay,
complete-domain norm certificates at H65536, two workers, 16GiB aggregate.
No training, ranking, prior norm certificate or uniform recurrence is rerun.
Failure refutes this finite base premise; it cannot refute the target alone.
"""
from copy import deepcopy
from fractions import Fraction as Q
import multiprocessing as mp
from pathlib import Path
import resource
import time

import run_floor_residual_prime_promotion_048 as P

ROOT=Path(__file__).resolve().parent
OUT=P.OUT/'base_followup_001'
H=65536
read,write,emit=P.read,P.write,P.emit


def validate_parent():
    counts=P.validate_parent()
    files=list((P.OUT/'source_snapshot').iterdir())
    if len(files)!=len(P.FILES) or any((ROOT/f.name).read_bytes()!=f.read_bytes() for f in files):
        raise ValueError('preserve frozen048 source')
    if not (P.OUT/'report.json').exists():raise ValueError('completed048 argument required')
    return counts+[len(files)]


def main():
    started=time.monotonic()
    if OUT.exists():raise FileExistsError('preserve fixed base audit')
    counts=validate_parent();source=Path(__file__).read_bytes()
    selected=read(P.OUT/'selected_argument.json')['row']
    request=selected['request'];arg=request['argument'];M=arg['base']['minimum']
    recipe,prime=request['source_recipe'],request['prime']
    if M>128:raise ValueError('this finite application budget is at most128 base supports')
    R=P.PRIOR;S=R.S
    certificate=R.ARG.evaluate_argument(request)
    R.independent_algebra(request,certificate)
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    (OUT/'source_snapshot'/Path(__file__).name).write_bytes(source)
    try:
        write(OUT/'protocol.json',dict(schema='fixed-prime-potential-base-v1',
            selected_argument=selected['id'],request=request,full_base_interval=[M,2*M-1],
            H=H,workers=2,memory_limit_bytes=16*1024**3,hashes_used=False,
            prior_norms_rerun=False,uniform_recurrence_tested=False,
            prior_frozen_source_counts=counts,new_source_files=1))
        compiler=S.S.Compiler(prime*(2*M-1),retain_compilation_certificates=False)
        pm=R.PRIME.Meter(cap=2_000_000_000,seconds=7200)
        cm=R.PC.Meter(cap=2_000_000_000)
        sm=S.S.DRIFT_CHECK.Meter(cap=10_000_000_000)
        nm=R.CAP.CHECK.Meter(cap=500_000_000)
        checked,seen,programs,cases=set(),{},[],[]
        def register(program,identifier):
            program=deepcopy(program);program['id']=identifier
            R.CAP.CHECK.verify_program(program,target=False,meter=nm)
            key=S.S.OLD.semantic_key(program)
            if key not in seen:seen[key]=identifier;programs.append(program)
            return seen[key]
        for N in range(M,2*M):
            inputs=S.source_request(compiler,recipe,prime,N)
            for support,values in ((N,inputs['parent_values']),(prime*N,inputs['child_values'])):
                if support not in checked:
                    for n,value in enumerate(values,1):
                        S.S.DRIFT_CHECK.verify_compilation(recipe['base'],n,support,value,meter=sm)
                    checked.add(support)
            construction=R.PRIME.build_prime_construction(inputs,pm)
            verified=R.PC.verify_prime_construction(inputs,construction,cm)
            whole=construction['original_forcing'];aux=construction['matched']['conversion_auxiliary']
            direction=S.direction(whole,aux,selected['d'],'base_direction')
            # Independently assemble the exact direction from the admitted
            # matched and conversion vectors, not the search helper.
            expected=R.PC._plus(R.PC._decode(whole,cm),
                R.PC._scale(R.PC._decode(aux,cm),-Q(selected['d']),cm),cm)
            if R.PC._decode(direction,cm)!=expected:raise ValueError('independent auxiliary direction')
            case=dict(N=N,whole=register(whole,'base_N%d_whole'%N),
                direction=register(direction,'base_N%d_direction'%N),
                source_verification=verified)
            cases.append(case)
            write(OUT/('source_N%d.json'%N),dict(source_recipe=recipe,certificate=construction,
                verification=verified,rounded_source_independently_verified=True))
        write(OUT/'programs.json',dict(programs=programs,cases=cases))
        reserve=R.CAP.memory_preflight(programs)
        emit('complete_base_audit_started',supports=len(cases),programs=len(programs),H=H,
             aggregate_memory_reserve_bytes=reserve)
        rows=[]
        with mp.get_context('fork').Pool(2) as pool:
            for row in pool.imap_unordered(R.CAP.audit_one,[dict(program=p,H=H) for p in programs]):
                write(OUT/('norm_%03d.json'%(len(rows)+1)),row);rows.append(row)
                if len(rows)%8==0 or len(rows)==len(programs):emit('base_norms_verified',completed=len(rows),total=len(programs))
        by_id={r['id']:r for r in rows}
        if len(rows)!=len(by_id) or set(by_id)!={p['id'] for p in programs}:
            raise ValueError('complete base norm coverage')
        results=[];tau=Q(selected['tau'])
        for c in cases:
            whole=R.AUDIT.interval(by_id[c['whole']]);direction=R.AUDIT.interval(by_id[c['direction']])
            energy=(whole[0]+tau*direction[0],whole[1]+tau*direction[1])
            bound=R.AUDIT.log_bound_interval(c['N'],request['target']['A'],request['target']['eta'])
            status=('verified' if energy[1]<=Q(bound['lower']) else
                    'refuted' if energy[0]>Q(bound['upper']) else 'unresolved_interval')
            results.append(dict(N=c['N'],potential=R.AUDIT.serialize_interval(energy),bound=bound,status=status))
        paid=all(r['status']=='verified' for r in results)
        base_status='PAID_FINITE_EXACT' if paid else ('REFUTED' if any(r['status']=='refuted' for r in results) else 'OPEN')
        write(OUT/'assessment.json',dict(rows=results,full_base_interval=[M,2*M-1],base_status=base_status))
        feedback=read(P.OUT/'next_search_input.json')
        feedback=deepcopy(feedback)
        feedback['authoritative_base_evidence']=str((OUT/'assessment.json').relative_to(ROOT))
        feedback['base_obligation']=dict(status=base_status,interval=[M,2*M-1],source_request=request,
            complete_domain_for_every_support=True,certificate_count=len(rows))
        feedback['remaining_obligations']=['uniform signed recurrence for both integer children, including complete tails'] if paid else ['repair the failed/unresolved finite base before claiming this argument','uniform signed recurrence']
        feedback['uniform_bound_proved']=False
        write(OUT/'next_search_input.json',feedback)
        report=dict(status='COMPLETE_FINITE_BASE_PAID_UNIFORM_RECURRENCE_OPEN' if paid else 'FINITE_BASE_NOT_PAID',
            selected_argument=selected['id'],request=request,base_status=base_status,base_supports=len(cases),
            norm_certificates=len(rows),base_status_counts={label:sum(r['status']==label for r in results) for label in
                ('verified','refuted','unresolved_interval')},
            source_operations=sm.operations,prime_operations=pm.operations,prime_checker_operations=cm.operations,
            norm_producer_operations=sum(r['producer_counts']['operations'] for r in rows),
            norm_checker_operations=sum(r['checker_operations'] for r in rows),
            aggregate_memory_reserve_bytes=reserve,parent_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            largest_individual_worker_rss_kib=max(r['worker_peak_rss_kib'] for r in rows),
            elapsed_seconds=time.monotonic()-started,prior_frozen_source_counts=counts,new_frozen_source_count=1,
            uniform_recurrence_proved=False,RH_proved=False,RH_refuted=False)
        validate_parent()
        if Path(__file__).read_bytes()!=source:raise ValueError('frozen base audit source changed')
        write(OUT/'report.json',report)
        emit('completed',status=report['status'],base_status_counts=report['base_status_counts'],elapsed_seconds=report['elapsed_seconds'])
    except Exception as error:
        write(OUT/'failure.json',dict(type=type(error).__name__,message=str(error),elapsed_seconds=time.monotonic()-started))
        raise


if __name__=='__main__':main()
