"""Finish verification of saved workers by algebraic keys, without rerunning them.

The original comparison stopped on differing term order. Its failure record
and all frozen files remain intact. This audit requires exactly the expected
component set, rejects duplicates, and compares every saved coefficient.
"""
import gzip
import json
from pathlib import Path
import re
import subprocess
import sys
import time
from flint import ctx
from prime_bank_candidates import Meter
import core_truncated_inverse as P
import run_core_truncated_inverse as R

OUT=R.OUT/'comparison-audit-001'
FILES=['audit_core_truncated_inverse.py','test_audit_core_truncated_inverse.py','core_truncated_inverse_audit_development.json']


def keyed_components(components, expected):
    result={}
    for item in components:
        key=(item['mode'],item['a'],item['b'])
        if key in result:
            raise ValueError('duplicate algebraic component')
        result[key]=item
    if set(result)!=set(expected):
        raise ValueError('missing or unexpected algebraic component')
    return result


def main():
    R.limits();ctx.prec=192;start=time.monotonic();R.verify()
    failed=R.read(R.OUT/'terminal_failure.json')
    if failed['error_type']!='ArithmeticError' or failed['error']!='same component support':
        raise ValueError('audit applies only to the recorded ordering failure')
    if OUT.exists():raise FileExistsError('one saved-output audit')
    development=R.read(R.ROOT/FILES[-1])
    if development['runs'][-1]['returncode'] or development['operations']!=sum(r['operations'] for r in development['runs']):
        raise ValueError('passed owned comparison checks')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name in FILES:(OUT/'source_snapshot'/name).write_bytes((R.ROOT/name).read_bytes())
    R.write(OUT/'protocol.json',dict(reason='saved producer/checker component ordering differs; match exact algebraic keys',
        expected_keys='every (mode,a,b) from the frozen selected source programs',
        worker_reruns=0,source_evaluations=0,original_frozen_files_changed=False,
        original_terminal_failure_retained=True,audit_operation_cap=50000000,
        failed_main_work_charge='full declared150million cap, because its actual terminal counter was not emitted'))
    test=subprocess.run([sys.executable,'-B','-m','unittest','test_audit_core_truncated_inverse'],cwd=R.ROOT,capture_output=True,text=True)
    R.write(OUT/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr))
    if test.returncode:raise RuntimeError('frozen comparison tests failed')
    meter=Meter(50000000,600);meter.charge(5000000)
    chosen=R.read(R.OUT/'selection.json');protocol=R.read(R.OUT/'protocol.json')
    representative=protocol['representative_bound']
    prior=R.read(R.ROOT/R.INPUT);parents=prior['generated_bound_program_obligations']
    tids=sorted({int(o['id'].rsplit('_source_',1)[1]) for o in parents})
    count=0;diagnostics=[];reordered=[]
    def compare(a,b):
        nonlocal count
        R.check_overlap(a,b,meter);count+=1
    def array(a,b,size):
        if len(a)!=size or len(b)!=size:raise ValueError('complete coefficient or cell-vector support')
        for x,y in zip(a,b):compare(x,y)
    for row in chosen:
        data=[]
        for role in ('producer','checker'):
            with gzip.open(R.OUT/(role+'-geometry-'+str(row['id'])+'.json.gz'),'rt') as f:data.append(json.load(f))
        p,c=data
        if p['H']!=R.H or c['H']!=R.H or p['geometry']!=row['id'] or c['geometry']!=row['id']:
            raise ValueError('saved common source horizon and geometry')
        expected={(case['mode']['name'],t['a'],t['b']) for case in row['cases'] for t in case['program']['terms']}
        left,right=(keyed_components(d['components'],expected) for d in data)
        if list(left)!=list(right):reordered.append(row['id'])
        for key in sorted(expected):
            compare(left[key]['coefficient'],right[key]['coefficient'])
            array(left[key]['values'],right[key]['values'],R.H+1)
        for value in data:
            if len(value['cases'])!=4:raise ValueError('all four modes')
        by_mode=[{case['mode']:case for case in d['cases']} for d in data]
        if any(set(m)!={r['mode']['name'] for r in row['cases']} for m in by_mode):raise ValueError('same complete source modes')
        for case in row['cases']:
            name=case['mode']['name'];a,b=(m[name] for m in by_mode)
            if a['program']!=case['program'] or b['program']!=case['program'] or (a['U'],a['V'])!=(b['U'],b['V']):
                raise ValueError('exact bound source program and cutoffs')
            for key in ('A','B','R','S','reconstructed'):array(a['inverse'][key],b['inverse'][key],R.H+1)
            array(a['restored'],b['restored'],R.H+1)
            array(b['inverse']['reconstructed'],b['inverse']['reference'],R.H+1)
        array(p['restored_source'],c['restored_source'],R.H+1)
        for key in ('exact_slope','cutoff','prefix_bound'):
            if p['centered_residual'][key]!=c['centered_residual'][key]:raise ValueError('same exact affine centering')
        array(p['centered_residual']['values'],c['centered_residual']['values'],R.H+1)
        probes=[{a['transport_id']:a for a in d['probes']} for d in data]
        if any(len(d['probes'])!=len(tids) or set(v)!=set(tids) for d,v in zip(data,probes)):raise ValueError('all transported inputs')
        for tid in tids:
            a,b=(v[tid] for v in probes)
            for key in ('signed_increment','diagonal_increment','cross_increment'):compare(a[key],b[key])
            if len(a['blocks'])!=2 or len(b['blocks'])!=2:raise ValueError('both complete blocks')
            for scale,u,v in zip((R.X,2*R.X),a['blocks'],b['blocks']):
                if u['X']!=scale or v['X']!=scale or u['mesh_power']!=representative['reduction']['mesh_power'] or v['mesh_power']!=u['mesh_power']:
                    raise ValueError('same complete cell mesh')
                from fractions import Fraction as Q
                r=Q(u['mesh_power']);length=1<<(r.numerator*(scale.bit_length()-1)//r.denominator)
                if len(u['cells'])!=scale//length or len(v['cells'])!=scale//length:
                    raise ValueError('complete projected partition')
                if u['all_components_including_transport_error']!=len(expected)+1 or v['all_components_including_transport_error']!=len(expected)+1:
                    raise ValueError('every source and error component in cross energy')
                for key in ('full_coarse','component_diagonal','complete_signed_cross'):compare(u[key],v[key])
                for x,y,lo in zip(u['cells'],v['cells'],range(scale,2*scale,length)):
                    if (x['start'],x['stop'])!=(lo,lo+length) or (y['start'],y['stop'])!=(lo,lo+length):raise ValueError('exact cell endpoints')
                    for key in ('joined','direct'):array(x[key],y[key],len(representative['construction']['channels']))
            diagnostics.append(dict(geometry=row['id'],alpha=row['alpha'],gamma=row['gamma'],transport_id=tid,
                X=R.X,child_X=2*R.X,representative_bound=representative['id'],
                parent_coarse=a['blocks'][0]['full_coarse'],child_coarse=a['blocks'][1]['full_coarse'],
                child_component_diagonal=a['blocks'][1]['component_diagonal'],child_signed_cross=a['blocks'][1]['complete_signed_cross'],
                complete_signed_increment=a['signed_increment'],finite_identity_verified=True,uniform_bound_proved=False))
    R.write(OUT/'verified_component_diagnostics.json',diagnostics)
    bounds=R.read(R.OUT/'component_bounds.json');obligations=[]
    for row in chosen:
        for parent in parents:
            ob=P.obligation(parent,row);ob['source_geometry'].pop('cases');ob['source_geometry_ref']=row['id']
            ob['paid_component_reduction']=P.paid_component_reduction(parent,row,bounds[str(row['id'])])
            obligations.append(ob)
    next_input=dict(schema='source-specific-short-inverse-search-input-v1',status='open',parent_obligation=prior,
        source_geometries=chosen,generated_joined_obligations=obligations,
        next_priority='Search the joined short-Mobius/residual kernel after the finite head payment; centered residual R=E_U-c_U*One keeps EVERY drift term and cross',
        new_proved_component_controls=['global shifted residual critical-l1 tail decay','centered full-prefix bound','short plain-Mobius head payment'],
        numerical_verification_scope='saved independent worker results, matched by exact algebraic component key',
        source_evaluations_in_audit=0,original_terminal_failure_retained=True,
        original_target_and_all_corrections_retained=True,new_source_observations=0,
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    R.write(OUT/'next_search_input.json',next_input)
    workers=[R.read(R.OUT/(role+'_resources.json')) for role in ('producer','checker')]
    dev=sum(R.read(R.ROOT/name)['operations'] for name in R.RECEIPTS)
    original_tests=R.read(R.OUT/'frozen_tests.json')['operations']
    # Charge a conservative maximum for the interrupted original comparator
    # instead of fabricating its missing terminal operation counter.
    total_upper=R.MAIN_CAP+sum(w['resources']['operations'] for w in workers)+dev+original_tests+meter.operations+10000
    if total_upper>R.TOTAL_CAP:raise OverflowError('inclusive conservative work cap')
    R.verify()
    for name in FILES:
        if (R.ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('changed frozen audit')
    report=dict(status='SAVED_ACTUAL_SOURCE_OUTPUTS_VERIFIED_BY_ALGEBRAIC_COMPONENT_KEYS',
        geometries=25,inverse_certificates=100,selected_geometries=len(chosen),reordered_geometries=reordered,
        complete_scalar_comparisons=count,numerical_joined_probes=len(diagnostics),generated_joined_obligations=len(obligations),
        paid_components_per_selected_geometry={str(r['id']):sum(t['cofinally_paid_by_this_rule'] for t in bounds[str(r['id'])]['components']) for r in chosen},
        original_terminal_failure_retained=True,worker_reruns=0,new_source_observations=0,
        audit=R.stats(meter,start),workers=workers,inclusive_operations_upper_bound=total_upper,
        upper_bound_includes_full_failed_main_cap=R.MAIN_CAP,
        actual_core_bound_disproved=False,full_signed_bounds_proved=0,whole_signed_bound_proved=False,RH_proved=False)
    R.write(OUT/'report.json',report);print(json.dumps(report),flush=True)


if __name__=='__main__':main()
