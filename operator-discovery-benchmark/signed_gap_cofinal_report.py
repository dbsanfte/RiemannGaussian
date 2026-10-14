"""Cofinal analytical dispositions supersede earlier unresolved status only."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');a=read(d/'audit.json');v=read(d/'verification.json');source=Path(spec['source_run'])
    from signed_gap_profile_report import summary as original
    s=original(source)
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h==sha(d/'frozen_source'/n)
    assert v['all_passed'] and all(v['checks'].values()) and v['protocol_sha256']==a['protocol_sha256']==digest(spec) and v['audit_sha256']==sha(d/'audit.json') and v['checker_sha256']==sha(BASE/'check_signed_gap_cofinal.py') and v['source_queue_sha256']==a['source_queue_sha256']==sha(source/'proof_queue.json') and not v['mathematical_audit_imports_production_code']
    rows=a['attempts'];assert len(rows)==s['proof_queue_candidates'] and not a['global_actual_critical_signed_gap_proved'] and not a['RH_proved']
    return {'status':'verified_actual_arithmetic_cofinal_counterexamples_on_unchanged_fitted_candidates','audit_directory':str(d),'source_run':str(source),'candidate_count':len(rows),
        'disproved_uniform_actual_half_gap_candidates':sum(r['persistent_half_gap_witness'] is not None for r in rows),'disproved_complete_dual_PSD_candidates':sum(r['persistent_nullspace_witness'] is not None for r in rows),
        'disproved_fully_charged_global_defect_candidates':sum(r['persistent_fully_charged_witness'] is not None for r in rows),'unresolved_actual_half_gap_candidates':sum(r['persistent_half_gap_witness'] is None for r in rows),
        'refuted_candidate_ids':[r['program_id'] for r in rows if r['persistent_half_gap_witness'] is not None],'bounded_constant_endpoint_candidates':sum(r['bounded_constant_endpoint_available'] for r in rows),
        'original_formulas_fits_and_finite_passes_unchanged':True,'actual_prime_inverse_counterexamples':True,'parameter_start_cannot_remove_witnesses':True,'unbounded_and_existential_families_remain_unresolved':True,'not_RH_counterexamples':True,
        'verified_checks':len(v['checks']),'independent_native_counts':v['counts'],'verification_sha256':sha(d/'verification.json'),'source_queue_sha256':sha(source/'proof_queue.json'),'machine_formalized':False,
        'global_actual_critical_signed_gap_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'signed-gap-profile-results/latest-cofinal-audit.json';return summary(read(p)['audit_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    return '\n'.join(['Cofinal endpoint audit of actual signed arithmetic candidates',
        f"Frozen candidates: {s['candidate_count']}; global half-gap claims disproved: {s['disproved_uniform_actual_half_gap_candidates']}; full dual-PSD comparisons disproved: {s['disproved_complete_dual_PSD_candidates']}; fully charged global defect bounds disproved: {s['disproved_fully_charged_global_defect_candidates']}; half-gap claims still unresolved: {s['unresolved_actual_half_gap_candidates']}.",
        'These are exact actual-Mobius counterexamples to particular fitted inequalities. At one fixed dyadic scale, a bounded constant and the cofinal root plateau produce a failure for EVERY sufficiently large parameter. An unknown starting q0 cannot remove it.',
        'Half-gap, necessary nullspace-PSD and fully charged margins are checked separately. Failure of the stronger half-gap is not silently substituted for failure of a weaker bound.',
        'Original detector formulas, coefficients, selection and 704 available finite passes remain unchanged. No new holdout cases or novel operator discovery are claimed by this analytical extension.',
        'Growing and existential constant families are not certified by the endpoint test. Their all-scale critical arithmetic bounds remain unresolved. These are not counterexamples to RH.',
        f"Independent audit groups: {s['verified_checks']}; counts: {s['independent_native_counts']}.",
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.',''])
