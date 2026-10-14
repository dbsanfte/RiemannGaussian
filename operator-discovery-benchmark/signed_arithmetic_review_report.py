"""Strict scope for post-seal parallel reviews and explicit component charges."""
import hashlib
import json
from pathlib import Path
from detector_workflow_guard import require_verified_runtime

BASE=Path(__file__).resolve().parent

def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def summary(directory):
    require_verified_runtime();d=Path(directory).resolve();v=read(d/'verification.json')
    for n,h in v['source_sha256'].items():
        if sha(BASE/n)!=h or sha(d/'frozen_source'/n)!=h:raise ValueError('review source changed')
    for n,h in v['dependency_sha256'].items():
        if sha(BASE/n)!=h:raise ValueError('review dependency changed')
    from signed_arithmetic_report import summary as source_summary
    source=source_summary(v['source_directory'])
    if source['verification_sha256']!=v['source_verification_sha256']:raise ValueError('source verification changed')
    collection=Path(v['collection_directory'])
    if sha(collection/'collection.json')!=v['collection_sha256']:raise ValueError('review collection changed')
    for n,h in v['collection_input_sha256'].items():
        if sha(collection/n)!=h:raise ValueError('review input changed')
    if not v['all_passed'] or v['RH_proved'] or v['actual_all_scale_full_signed_bound_proved']:raise ValueError('review evidence invalid or overstates goal')
    return {'status':'verified_parallel_reviews_and_explicit_component_reduction','review_directory':str(d),
        'reviewed_candidates':v['reviewed_candidates'],'component_coefficient':'U(w)*(11+16*q^2/9)',
        'component_bound_domain':'q>=1, X>=1, shared B=floor(X^(1/3)); complete dense residual excluded and retained',
        'exact_stored_constant_refutations':v['exact_stored_refutations'],
        'all_original_existential_full_signed_claims_remain_unresolved':True,
        'runtime_model_independently_verified':False,'other_reviewer_prose_mathematically_promoted':False,
        'verification_sha256':sha(d/'verification.json'),'uniform_RH_sufficient_signed_controls_verified':[],
        'RH_proved':False}

def load_latest():
    pointer=BASE/'signed-arithmetic-results/review-latest.json'
    return summary(read(pointer)['review_directory']) if pointer.exists() else {'status':'not_run'}

def text_report(s):
    return (f"Parallel analytical reviews: {s['reviewed_candidates']} frozen full-signed candidates. "
            f"Exact dyadic stored-constant refutations: {len(s['exact_stored_constant_refutations'])}. "
            'The original existential full estimates remain unresolved.\n'
            'Verified component charge: |diagonal+short primitive projection| <= U(w)*(11+16*q^2/9)*X^2*ceil(X^(1/q)), q>=1, shared B=floor(X^(1/3)). '
            'It reduces the full estimate to its complete dense signed remainder by an explicit constant shift. '
            'No upper bound on that remainder or RH proof is established. Reviewer prose outside these named certificates is not promoted.\n')
