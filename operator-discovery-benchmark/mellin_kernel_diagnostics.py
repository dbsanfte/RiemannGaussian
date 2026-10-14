"""Strict read-only wrapper for an auxiliary new-q native cost audit."""
from pathlib import Path
from stable_scale_report import BASE,read,sha


def summary(directory):
    from mellin_kernel_report import summary as parent
    directory=Path(directory).resolve();parent(directory)
    p=directory/'fresh_observer_verification.json'
    if not p.exists():return {'status':'not_run'}
    verification=read(p);data=read(directory/'fresh_observer_costs.json')
    for n,h in data['source_sha256'].items():assert sha(directory/n)==h
    for n,h in data['audit_source_sha256'].items():assert sha(BASE/n)==h
    assert verification['source_observer_costs_sha256']==sha(directory/'fresh_observer_costs.json')
    assert verification['checker_sha256']==sha(BASE/'check_mellin_kernel_observers.py') and verification['all_passed']
    assert verification['no_reselection_or_constant_refit'] and not data['selection_or_constants_changed']
    assert data['no_new_fresh_validation_claim'] and data['conditional_global_premises_still_unproved'] and not data['RH_proved']
    assert verification['uniform_RH_sufficient_signed_controls_verified']==[] and not verification['RH_proved']
    return {'status':verification['status'],'run_directory':str(directory),'verification_sha256':sha(p),
        'counts':verification['counts'],'previously_unavailable_observers_now_available':len(verification['previously_unavailable_native_observers_now_available']),
        'q':data['q'],'records':data['records'],'no_reselection_or_constant_refit':True,
        'no_new_fresh_validation_claim':True,'uniform_signed_premises_unproved':True,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'mellin-kernel-results/latest.json'
    return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}
