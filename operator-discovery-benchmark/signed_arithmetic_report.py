"""Strict scope for signed language, component theorems, and unresolved estimates."""
import json
import hashlib
from pathlib import Path
from detector_workflow_guard import require_verified_runtime

BASE=Path(__file__).resolve().parent


def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def summary(directory):
    require_verified_runtime();d=Path(directory).resolve()
    if (d/'failure.json').exists():raise ValueError('failed run cannot be published as successful')
    p=read(d/'protocol.json');s=read(d/'seal.json');v=read(d/'verification.json')
    for n,h in p['code_sha256'].items():
        if sha(BASE/n)!=h or sha(d/'frozen_source'/n)!=h:raise ValueError('frozen signed source changed')
    for key in ['dependency_sha256','input_sha256']:
        for n,h in p[key].items():
            if sha(BASE/n)!=h:raise ValueError('signed dependency changed')
    for n,h in s['files'].items():
        if sha(d/n)!=h:raise ValueError('signed seal changed')
    for n,h in v['artifact_sha256'].items():
        if sha(d/n)!=h:raise ValueError('verified signed artifact changed')
    if not v['all_passed'] or v.get('RH_proved') or v.get('actual_all_scale_signed_bound_proved'):
        raise ValueError('signed verification invalid or overclaims full theorem')
    batch=read(d/'candidate_batch.json');queue=read(d/'proof_queue.json');final=read(d/'final_evaluation.json')
    calibration_pass=sum(r['finite_pass'] for item in final['calibration_results'] for r in item['cases'])
    rows=final['results']
    return {'status':'verified_signed_arithmetic_language_and_component_certificates',
        'run_directory':str(d),'candidate_stencils':len(batch['candidates']),
        'rejected_generation_records':len(batch['rejected']),'proof_queue_candidates':len(queue['queue']),
        'conditional_critical_bridges':sum(c['nonnegative_critical_recurrence_bridge'] for c in queue['queue']),
        'positive_transformed_energy_bridges':sum(r['positive_energy_transform']['conditional_bridge_admitted'] for r in final['results']),
        'higher_moment_queue_candidates':sum(c['annihilated_moment_count']>1 for c in queue['queue']),
        'global_zero_density_component_certificates':len(rows),
        'energy_only_bridge_obstructions':sum(r['energy_bridge_obstruction']['energy_only_critical_bridge_obstructed'] for r in rows),
        'dyadic_stored_bound_failures':sum(case['finite_pass'] is False and case['in_dyadic_claim_domain'] for r in rows for case in r['score']['cases']),
        'ast_programs':len(batch['ast_exploration']['generation']['programs']),
        'ast_queue_candidates':len(queue['ast_queue']),
        'ast_final_available':final['ast_exploration']['available_cases'],
        'ast_training_missing':batch['ast_exploration']['training']['missing_cases'],
        'fresh_signed_bound_passes':sum(r['score']['passes'] for r in rows),
        'fresh_signed_bound_failures':sum(r['score']['failures'] for r in rows),
        'unseen_level_constants_missing':sum(r['score']['missing'] for r in rows),
        'actual_scales':read(d/'final_cases.json')['actual_scales'],
        'coupled_mobius_reconstructions':len(final['coupled_responses']),
        'calibration_candidate_laws':len(queue['calibration_queue']),
        'calibration_fresh_passes':calibration_pass,
        'calibration_global_scope':'filtered Liouville divisor sum; not unsmoothed Mobius control',
        'counterfeit_divisor_violations':len(final['counterfeit_tail']['violations']),
        'verified_checks':v.get('checks_passed'), 'verification_sha256':sha(d/'verification.json'),
        'dense_signed_residual_control_proved':False,'actual_all_scale_signed_bound_proved':False,
        'uniform_RH_sufficient_signed_controls_verified':[],'machine_formalized':False,'RH_proved':False}


def load_latest():
    p=BASE/'signed-arithmetic-results/latest.json'
    return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    return '\n'.join([
      'Signed arithmetic language and coupled cancellation search',
      f"Generated {s['candidate_stencils']} complete signed stencils; retained {s['proof_queue_candidates']} diverse analytical leads, including {s['higher_moment_queue_candidates']} cancelling multiple density moments.",
      'Exact typed coefficient operations include complete divisor inversion, convolution, signed point products, prefix and index transformations, masks and fractional normalizers. Missing computation remains missing.',
      'The learner infers rational annihilation coefficients from anonymous moment responses. Dyadic dilation, polynomial moment tests and a coefficient budget are supplied search assumptions.',
      f"Full-stencil finite inequality tests evaluated after sealing at scales {s['actual_scales']}: {s['fresh_signed_bound_passes']} passes, {s['fresh_signed_bound_failures']} failures, {s['unseen_level_constants_missing']} missing unseen-level constants.",
      f"{s['conditional_critical_bridges']} queue entries satisfy the direct positive-recursion condition; {s['positive_transformed_energy_bridges']} admit the broader nonnegative transformed-energy bridge. Their signed inequality premise remains unproved.",
      f"{s['global_zero_density_component_certificates']} kernels admit actual all-scale coprime-squarefree component bounds by exact zero integral and a rational certificate for weighted variation. Every modulus, primitive cutoff and dense signed residual is retained.",
      'These component bounds use supplied elementary discrepancy and integration-by-parts lemmas. Higher density-moment cancellation alone does not improve the square-root discrepancy exponent.',
      f"{s['coupled_mobius_reconstructions']} post-seal shared-cutoff cross-term reconstructions preserve the complete signed Mobius defect.",
      f"Arithmetic response calibration: {s['calibration_candidate_laws']} retained sparse laws, {s['calibration_fresh_passes']} post-seal passes. Its all-integer identity is the filtered Liouville divisor sum; no unfiltered RH estimate follows.",
      f"Finite positive-tail counterfeit: {s['counterfeit_divisor_violations']} violations of complete divisor inversion.",
      f"Exploratory recursive ASTs: {s['ast_programs']} sampled, {s['ast_queue_candidates']} structural leads, {s['ast_final_available']} available post-seal observations; {s['ast_training_missing']} missing training computations retained. No ordinary-energy bridge is presumed for these operators.",
      f"Energy-only bridge obstructions: {s['energy_only_bridge_obstructions']}. Exact dyadic-domain stored-bound failures: {s['dyadic_stored_bound_failures']}; non-dyadic failures are separate diagnostic probes.",
      'Actual coefficient prefixes overlap previous development. Evaluation is generated after the candidate seal; standard stencil responses can overlap historical evidence. No previously unseen prime-coefficient claim is made. File-access guards are dataflow checks, not an adversarial OS sandbox.',
      'Full actual Mobius/prime signed upper control over all scales remains unproved. Verified RH-sufficient controls: 0. Research goal remains active.',''])
