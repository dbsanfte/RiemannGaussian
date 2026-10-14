#!/usr/bin/env python3
"""Independent new-q recovery audit using the already frozen verifier methods."""
import argparse,json
from pathlib import Path
import flint
from stable_scale_report import BASE,read,sha
from mellin_kernel_report import summary
from check_mellin_kernels import independent_global,check_cost


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);args=p.parse_args();d=args.run_dir.resolve();summary(d)
    data=read(d/'fresh_observer_costs.json');spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json')
    for n,h in data['source_sha256'].items():assert sha(d/n)==h
    for n,h in data['audit_source_sha256'].items():assert sha(BASE/n)==h
    bs={b['id']:b for b in batch['banks']};ps={p['id']:p for p in batch['programs']};cs={c['id']:c for c in arc['archive']}
    constants={c['candidate_id']:c['constants'] for c in read(d/'parameter_calibration.json')['illustrative_free_constants']}
    counts={'all_scale_weak_and_unit_certificates':0,'fully_charged_native_Mellin_observers':0,'observers_outside_convergence_domain':0};opened=[]
    for row in data['records']:
        c=cs[row['candidate_id']];b=bs[c['bank_id']];ids=b['member_ids'];assert c['RH_sufficient_if_uniform']
        gcs=[independent_global(ps[i]['kernel'],ps[i]['parameters'],batch['global_certificates'][i],counts) for i in ids]
        flint.ctx.prec=384
        check_cost([ps[i]['kernel'] for i in ids],b['recovery_certificate'],b['parameters'],c['frontier'],constants[c['id']],data['q'],gcs,row['fresh_parameter_cost'],spec['cost_query'],counts)
        if row['training_observer_status']=='no_tested_q_inside_this_observers_domain' and row['fresh_parameter_cost']['status']=='conditional':opened.append(c['id'])
    assert not data['selection_or_constants_changed'] and data['no_new_fresh_validation_claim'] and data['conditional_global_premises_still_unproved'] and not data['RH_proved']
    output={'status':'independently_checked_conditional_new_q_costs','source_observer_costs_sha256':sha(d/'fresh_observer_costs.json'),
        'checker_sha256':sha(BASE/'check_mellin_kernel_observers.py'),'counts':counts,'previously_unavailable_native_observers_now_available':opened,
        'no_reselection_or_constant_refit':True,'all_passed':True,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}
    destination=d/'fresh_observer_verification.json'
    if destination.exists():raise FileExistsError('Retain verified observer diagnostic')
    destination.write_text(json.dumps(output,indent=2)+'\n')
    print('New-q native costs checked:',counts['fully_charged_native_Mellin_observers'],'previously unavailable observers opened:',len(opened))


if __name__=='__main__':main()
