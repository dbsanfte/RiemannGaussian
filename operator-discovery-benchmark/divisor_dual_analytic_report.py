"""Independent review summary kept separate from the frozen detector result."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');attempts=read(d/'attempts.json');v=read(d/'verification.json');source=Path(spec['source_run'])
    from divisor_dual_report import summary as detector
    original=detector(source)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h==sha(d/'frozen_source'/n)
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    assert attempts['protocol_sha256']==v['protocol_sha256']==digest(spec) and v['attempts_sha256']==sha(d/'attempts.json') and v['checker_sha256']==sha(BASE/'check_divisor_dual_analytic.py') and v['source_queue_sha256']==sha(source/'proof_queue.json') and v['all_passed'] and all(v['checks'].values()) and not v['mathematical_audit_imports_production_code']
    assert len(attempts['attempts'])==original['proof_queue_candidates'] and not attempts['all_scale_critical_signed_bound_proved'] and not attempts['RH_proved']
    rows=attempts['attempts'];return {'status':'verified_separate_analytical_dispositions_on_frozen_detector_leads','review_directory':str(d),'source_run':str(source),
        'candidate_count':len(rows),'proved_uniform_critical_candidates':0,'disproved_uniform_matrix_candidates':sum(r['proof_status']=='disproved_uniform_matrix_claim' for r in rows),'unresolved_uniform_matrix_candidates':sum(r['proof_status']=='unresolved_uniform_matrix_claim' for r in rows),
        'proved_arithmetic_subclaims':attempts['proved_subclaims'],'positive_density_uncovered_tail_obstruction_proved':True,'quadratic_Gram_coefficient_obstruction_proved':True,
        'exact_actual_signed_nullspace_gap_explicit':True,'conditional_Schur_buffer_not_arithmetic_proof':True,'source_candidates_and_selection_unchanged':True,
        'polynomial_level_constant_limits_current_grammar':True,'next_run_feedback':attempts['next_run_feedback'],'verified_checks':len(v['checks']),'independent_exact_counts':v['counts'],
        'source_queue_sha256':sha(source/'proof_queue.json'),'verification_sha256':sha(d/'verification.json'),'machine_formalized':False,'global_full_signed_defect_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'divisor-dual-results/latest-analytical-review.json';return summary(read(p)['review_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    return '\n'.join(['Separate analytical proof attempts on frozen detector candidates',
        f"Exact candidates reviewed: {s['candidate_count']}; uniform matrix claims disproved: {s['disproved_uniform_matrix_candidates']}; unresolved: {s['unresolved_uniform_matrix_candidates']}; proved critical candidates: {s['proved_uniform_critical_candidates']}.",
        'A positive-density set of unselected tail rows gives a null Gram witness with cubic child energy. No Gram weight can repair this universal PSD family. For quadratic Gram power, coefficients below 4/3 also fail via a full-tail witness.',
        'The full nonunit Gram leads retain the exact necessary entry D*Q(4X)-Delta(X). A conditional Schur buffer handles the orthogonal comparison only if a signed arithmetic gap is proved. That gap remains unresolved.',
        'Detector formulas, hashes, selection and numerical evidence remain unchanged. Matrix disproofs are not RH counterexamples.',
        'The prescribed polynomial growth of level constants is a grammar limitation: the general RH-sufficient criterion allows arbitrary finite constants for each epsilon. This limitation is feedback for a fresh run.',
        f"Independent audit groups: {s['verified_checks']}; exact counts: {s['independent_exact_counts']}.",
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.',''])
