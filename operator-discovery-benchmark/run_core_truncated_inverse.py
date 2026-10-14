"""Bounded actual-source inverse search, with two independent workers."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction as Q
import gzip
import json
import multiprocessing as mp
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_truncated_inverse as P
import check_core_truncated_inverse as C
from run_core_bound_program_search import verify as verify_parent

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_bound_program_obligation.json'
PARENT = ROOT/'core-bound-program-results/pilot-001'
SOURCE = ROOT/'core-signed-work-results/pilot-001'
TRANSPORT = ROOT/'core-prime-transport-results/pilot-001'
OUT = ROOT/'core-truncated-inverse-results/pilot-001'
H, X = 1023, 256
TESTS = ['test_core_truncated_inverse', 'test_check_core_truncated_inverse']
RECEIPTS = ['core_truncated_inverse_producer_development.json', 'core_truncated_inverse_checker_development.json']
FILES = ['core_truncated_inverse.py','check_core_truncated_inverse.py','run_core_truncated_inverse.py',
         'core_truncated_inverse_protocol.txt','CORE_TRUNCATED_INVERSE_REVIEW_015.txt',
         'core_bound_program_search.py','prime_bank_candidates.py',INPUT]+RECEIPTS+[s+'.py' for s in TESTS]
MAIN_CAP, WORKER_CAP, TOTAL_CAP = 150000000, 600000000, 1400000000


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    with path.open('x') as f:
        json.dump(value,f,indent=2,sort_keys=True)
        f.write('\n')


def tight(value):
    return value.is_finite() and value.rad() <= arb(2)**-96*(1+abs(value.mid()))


def serial(value):
    if isinstance(value, arb):
        if not tight(value):
            raise ArithmeticError('finite absolute-plus-relative interval required')
        return str(value)
    if isinstance(value,dict):
        return {k:serial(v) for k,v in value.items()}
    if isinstance(value,list):
        return [serial(v) for v in value]
    return value


def limits():
    _, hard=resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))


def stats(m,start):
    return dict(operations=m.operations,peak_cells=m.peak_cells,elapsed_seconds=time.monotonic()-start,
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def verify():
    verify_parent()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)


def archived(role,meter):
    wanted={'core','mode:nu0','mode:nu1','mode:nu2','mode:mu'}
    result={}
    with gzip.open(SOURCE/(role+'_vectors.jsonl.gz'),'rt') as f:
        for line in f:
            row=json.loads(line)
            meter.charge(3*len(row['values']))
            if row['name'] in wanted:
                result[row['name']]=[arb(v) for v in row['values'][:H+1]]
                if len(result[row['name']]) != H+1:
                    raise ValueError('complete prior coefficient support')
            if set(result)==wanted:
                break
    if set(result)!=wanted:
        raise ValueError('complete prior four-mode source')
    mu=[]
    for v in result['mode:mu']:
        choices=[k for k in (-1,0,1) if v==arb(k)]
        if len(choices)!=1:
            raise ArithmeticError('exact archived Mobius integer')
        mu.append(choices[0])
    return result,mu


def check_overlap(a,b,meter):
    a,b=arb(a),arb(b)
    meter.charge(20)
    if not tight(a) or not tight(b) or not a.overlaps(b):
        raise ArithmeticError('independent complete coefficient/observable disagreement')


def worker(role,chosen,representative,tids,source_binding):
    limits();ctx.prec=192;start=time.monotonic();meter=Meter(WORKER_CAP,3600)
    old,mu=archived(role,meter)
    Ru=arb(source_binding['residue'])
    scalars={'beta':arb(9)/2,'-beta':-arb(9)/2,'-R_u':-Ru}
    sources={}
    for tid in tids:
        with gzip.open(TRANSPORT/(role+'-transport-'+str(tid)+'.json.gz'),'rt') as f:
            data=json.load(f)
        g=[arb(v) for v in data['vectors']['g'][:H+1]]
        sources[tid]=dict(g=g,error=[x-y for x,y in zip(g,old['core'])])
        meter.charge(8*len(data['vectors']['g']))
    files=[]
    mode_names={'B':'nu0','U':'nu1','V':'mu','power':'nu2'}
    for row in chosen:
        value=P.source_components(mu,row,scalars,H,meter,P.evaluate if role=='producer' else C.evaluate)
        for case in value['cases']:
            source_mode=next(c['mode'] for c in row['cases'] if c['mode']['name']==case['mode'])
            scalar=scalars[source_mode['coefficient']]
            for a,b in zip(case['restored'],old['mode:'+mode_names[case['mode']]]):
                check_overlap(a,scalar*b,meter)
            if role=='checker':
                for a,b in zip(case['inverse']['reconstructed'],case['inverse']['reference']):
                    check_overlap(a,b,meter)
        for a,b in zip(value['restored_source'],old['core']):
            check_overlap(a,b,meter)
        centered=P.centered_residual(mu,value['cases'][0]['U'],value['cases'][0]['inverse']['R'],meter)
        probes=[]
        for tid,state in sources.items():
            blocks=[P.joined_projection(value['components'],state['error'],state['g'],
                    representative['construction'],scale,representative['reduction']['mesh_power'],meter,
                    'prefix' if role=='producer' else 'abel') for scale in (X,2*X)]
            rho=Q(representative['required']['rho'])
            rr=arb(rho.numerator)/rho.denominator
            probes.append(dict(transport_id=tid,blocks=blocks,
                signed_increment=blocks[1]['full_coarse']-rr*blocks[0]['full_coarse'],
                diagonal_increment=blocks[1]['component_diagonal']-rr*blocks[0]['component_diagonal'],
                cross_increment=blocks[1]['complete_signed_cross']-rr*blocks[0]['complete_signed_cross']))
        value.update(centered_residual=centered,probes=probes)
        name=role+'-geometry-'+str(row['id'])+'.json.gz'
        with gzip.open(OUT/name,'xt',compresslevel=1) as f:
            json.dump(serial(value),f)
        files.append(name)
        print(json.dumps(dict(stage=role+'_source_identity_checked',geometry=row['id'],components=len(value['components']),operations=meter.operations)),flush=True)
    result=dict(files=files,resources=stats(meter,start))
    write(OUT/(role+'_resources.json'),result)
    return result


def main():
    limits();ctx.prec=192;start=time.monotonic();verify_parent()
    if (ROOT/INPUT).read_bytes() != (PARENT/'next_search_input.json').read_bytes():
        raise ValueError('current complete parent input')
    prior=read(ROOT/INPUT)
    parents=prior['generated_bound_program_obligations']
    if not parents or prior['whole_signed_bound_proved']:
        raise ValueError('current unresolved signed targets')
    representative=min(parents,key=lambda o:(-o['construction']['degree'],-o['construction']['cancellation_order'],
        -max(Q(c['eta']) for c in o['construction']['channels']),-Q(o['reduction']['mesh_power']),o['id']))
    tids=sorted({int(o['id'].rsplit('_source_',1)[1]) for o in parents})
    source_binding=read(PARENT/'source_binding.json')
    development={s:read(ROOT/s) for s in RECEIPTS}
    for d in development.values():
        if d['runs'][-1]['returncode'] or d['operations']!=sum(r['operations'] for r in d['runs']):
            raise ValueError('passed cumulative owned development')
    if OUT.exists():
        raise FileExistsError('one terminal attempt; no overwrite or unchanged replay')
    OUT.mkdir(parents=True);(OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json',FILES)
    write(OUT/'protocol.json',dict(schema='source-specific-truncated-inverse-search-v1',input=INPUT,
        cutoffs=list(P.CUTOFFS),coefficient_solver='triangular exact denominator inversion in a weighted monomial quotient',
        discarded_support='alpha*a+gamma*b>=1 gives strict support>N; discard only before any centering expansion',
        all_four_actual_source_modes=True,full_units_and_transport_error=True,
        selection='factor budgets4,5,8; balanced shortest cutoffs and shortest unshifted inverse with smallest retained expansion',
        representative_bound=representative,representative_selection='largest polynomial degree/cancellation/weight/mesh, then inherited id; no numerical responses',
        H=H,X=X,shared_horizon='N=4X-1 used for both complete parent and child',
        numerical_source_scope='all source coefficients previously observed; new decomposition and cross observables only',
        new_source_observations=0,source_horizon_already_observed=524287,
        workers=2,methods=['sparse factor convolution and weighted complete prefixes',
                           'independent divisor convolution and Abel means'],
        scalar_tolerance='finite Arb interval radius<=2^-96*(1+abs(midpoint)); comparisons require enclosure overlap',
        source_selection_uses_numerics=False,constant_fit=False,hashes=False,
        main_cap=MAIN_CAP,worker_cap=WORKER_CAP,total_cap=TOTAL_CAP,process_memory_bytes=4*1024**3,aggregate_memory_limit=16*1024**3,
        main_seconds=14400,worker_seconds=3600,whole_signed_bound_proved=False,RH_proved=False))
    meter=Meter(MAIN_CAP,14400);meter.charge(3000000)
    rows=P.catalogue(source_binding['complete_source'],meter)
    certificates=[]
    bounds={}
    for row in rows:
        for case in row['cases']:
            certificates.append(dict(geometry=row['id'],mode=case['mode']['name'],certificate=C.verify_certificate(case['program'],meter)))
        bounds[str(row['id'])]=P.component_bounds(row,meter)
    chosen=P.select(rows)
    write(OUT/'programs.json',rows);write(OUT/'certificates.json',certificates)
    write(OUT/'component_bounds.json',bounds);write(OUT/'selection.json',chosen)
    write(OUT/'primitive_controls.json',{str(r['id']):P.primitive_controls(r) for r in rows})
    test_start=time.monotonic()
    test=subprocess.run([sys.executable,'-B','-m','unittest']+TESTS,cwd=ROOT,capture_output=True,text=True)
    test_ops=sum(map(int,re.findall(r'operations=(\d+)',test.stdout)))
    write(OUT/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr,
        operations=test_ops,elapsed_seconds=time.monotonic()-test_start))
    if test.returncode:
        raise RuntimeError('frozen tests failed')
    print(json.dumps(dict(stage='source_grammar_frozen',geometries=len(rows),inverse_certificates=len(certificates),selected=len(chosen))),flush=True)
    workers=[]
    with ProcessPoolExecutor(max_workers=2,mp_context=mp.get_context('spawn')) as pool:
        futures=[pool.submit(worker,role,chosen,representative,tids,source_binding) for role in ('producer','checker')]
        for future in as_completed(futures):
            workers.append(future.result())
    comparisons=0;diagnostics=[]
    def compare(a,b):
        nonlocal comparisons
        check_overlap(a,b,meter);comparisons+=1
    for row in chosen:
        outputs=[]
        for role in ('producer','checker'):
            with gzip.open(OUT/(role+'-geometry-'+str(row['id'])+'.json.gz'),'rt') as f:
                outputs.append(json.load(f))
        p,c=outputs
        if len(p['cases'])!=4 or len(c['cases'])!=4 or len(p['probes'])!=len(tids) or len(c['probes'])!=len(tids):
            raise ValueError('complete four modes and every transported source')
        for a,b in zip(p['cases'],c['cases']):
            for key in ('mode','program','U','V'):
                if a[key]!=b[key]:raise ArithmeticError('same complete mode')
            for key in ('A','B','R','S','reconstructed'):
                if len(a['inverse'][key])!=H+1 or len(b['inverse'][key])!=H+1:
                    raise ValueError('complete inverse coefficient arrays')
                for x,y in zip(a['inverse'][key],b['inverse'][key]):compare(x,y)
        if len(p['components'])!=row['component_count'] or len(c['components'])!=row['component_count']:
            raise ValueError('every source component retained')
        for a,b in zip(p['components'],c['components']):
            for key in ('mode','a','b'):
                if a[key]!=b[key]:raise ArithmeticError('same component support')
            compare(a['coefficient'],b['coefficient'])
            if len(a['values'])!=H+1 or len(b['values'])!=H+1:
                raise ValueError('complete component coefficient support')
            for x,y in zip(a['values'],b['values']):compare(x,y)
        if len(p['restored_source'])!=H+1 or len(c['restored_source'])!=H+1:
            raise ValueError('complete restored source support')
        for a,b in zip(p['restored_source'],c['restored_source']):compare(a,b)
        for key in ('exact_slope','cutoff','prefix_bound'):
            if p['centered_residual'][key]!=c['centered_residual'][key]:raise ArithmeticError('exact centering mismatch')
        for a,b in zip(p['centered_residual']['values'],c['centered_residual']['values']):compare(a,b)
        for a,b in zip(p['probes'],c['probes']):
            if a['transport_id']!=b['transport_id']:raise ArithmeticError('same full transported source')
            if len(a['blocks'])!=2 or len(b['blocks'])!=2:raise ValueError('both whole dyadic blocks')
            for key in ('signed_increment','diagonal_increment','cross_increment'):compare(a[key],b[key])
            for u,v in zip(a['blocks'],b['blocks']):
                r=Q(u['mesh_power']);length=1<<(r.numerator*(u['X'].bit_length()-1)//r.denominator)
                if len(u['cells'])!=u['X']//length or len(v['cells'])!=u['X']//length:
                    raise ValueError('complete projected cell partition')
                for key in ('X','mesh_power','all_components_including_transport_error'):
                    if u[key]!=v[key]:raise ArithmeticError('same joined kernel')
                for key in ('full_coarse','component_diagonal','complete_signed_cross'):compare(u[key],v[key])
                for x,y in zip(u['cells'],v['cells']):
                    if (x['start'],x['stop'])!=(y['start'],y['stop']):raise ArithmeticError('complete same cells')
                    for key in ('joined','direct'):
                        for l,r in zip(x[key],y[key]):compare(l,r)
            diagnostics.append(dict(geometry=row['id'],alpha=row['alpha'],gamma=row['gamma'],
                transport_id=a['transport_id'],X=X,child_X=2*X,representative_bound=representative['id'],
                parent_coarse=a['blocks'][0]['full_coarse'],child_coarse=a['blocks'][1]['full_coarse'],
                child_component_diagonal=a['blocks'][1]['component_diagonal'],child_signed_cross=a['blocks'][1]['complete_signed_cross'],
                complete_signed_increment=a['signed_increment'],finite_identity_verified=True,uniform_bound_proved=False))
    write(OUT/'verified_component_diagnostics.json',diagnostics)
    obligations=[]
    for row in chosen:
        for parent in parents:
            ob=P.obligation(parent,row)
            ob['source_geometry'].pop('cases')
            ob['source_geometry_ref']=row['id']
            ob['paid_component_reduction']=P.paid_component_reduction(parent,row,bounds[str(row['id'])])
            obligations.append(ob)
    next_input=dict(schema='source-specific-short-inverse-search-input-v1',status='open',parent_obligation=prior,
        source_geometries=chosen,generated_joined_obligations=obligations,
        next_priority='Search a signed bound for the joined short-Mobius/residual kernel after paying the finite short head; use R=E_U-c_U*One only with EVERY drift term and cross retained',
        true_new_controls=['global shifted residual critical-l1 tail decay', 'centered residual full-prefix bound',
                           'finite short-Mobius source component paid at alpha<=1/2'],
        absolute_component_route_has_unpaid_common_inverse_sector=True,
        original_target_and_all_corrections_retained=True,new_source_observations=0,
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'next_search_input.json',next_input)
    total=meter.operations+test_ops+sum(d['operations'] for d in development.values())+sum(w['resources']['operations'] for w in workers)
    if total>TOTAL_CAP:raise OverflowError('inclusive operation cap')
    verify()
    report=dict(status='ACTUAL_SOURCE_INVERSE_IDENTITIES_AND_COMPONENT_CONTROLS_VERIFIED',
        geometries=len(rows),inverse_certificates=len(certificates),selected_geometries=len(chosen),
        complete_scalar_comparisons=comparisons,numerical_joined_probes=len(diagnostics),
        generated_joined_obligations=len(obligations),
        paid_components_per_selected_geometry={str(r['id']):sum(t['cofinally_paid_by_this_rule'] for t in bounds[str(r['id'])]['components']) for r in chosen},
        main=stats(meter,start),workers=workers,inclusive_operations=total,
        H=H,new_source_observations=0,actual_core_bound_disproved=False,
        full_signed_bounds_proved=0,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'report.json',report);print(json.dumps(report),flush=True)


if __name__=='__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'report.json').exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json',dict(status='incomplete',error_type=type(error).__name__,error=str(error),
                full_comparison_complete=False,whole_signed_bound_proved=False,RH_proved=False))
        raise
