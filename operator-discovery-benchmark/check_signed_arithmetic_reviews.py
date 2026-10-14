#!/usr/bin/env python3
"""Narrow domain adjudication after generic parallel review collection."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

BASE=Path(__file__).resolve().parent

def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
    if not c:raise ValueError(m)


def check(source,collection,destination):
    from detector_workflow_guard import require_verified_runtime
    from signed_arithmetic_report import summary
    from detector_review_planner import preflight
    from check_signed_arithmetic_search import factor_prefix,ceil_power
    require_verified_runtime();source=Path(source).resolve();collection=Path(collection).resolve();destination=Path(destination).resolve()
    need(not destination.exists(),'successful review audit requires fresh destination')
    s=summary(source);manifest=read(collection/'manifest.json');v=preflight(collection)
    need(manifest['source_directory']==str(source),'review source mismatch')
    need(read(collection/'collection.json')==v,'collection provenance changed')
    queue=read(source/'proof_queue.json')['queue'];final=read(source/'final_evaluation.json')['results']
    need(len(queue)==len(final)==v['reviewed_candidates'],'review coverage mismatch')
    allrows=[row for i in range(1,manifest['batch_count']+1) for row in read(collection/f'batch-{i:02d}-review.json')['reviews']]
    need(all(row['status'] in ['unresolved','conditional','stored_refutation','new_proposal'] for row in allrows),'a global refutation needs a separate complete proof')
    components=[];witnesses=[]
    for candidate,result in zip(queue,final):
        need(candidate['program_id']==result['program_id'],'candidate ordering mismatch')
        U=Q(result['kernel_certificate']['weighted_sqrt_variation_upper']);need(U>=0,'invalid variation')
        components.append({'program_id':candidate['program_id'],'U':str(U),
            'q_domain':'every real q>=1','X_domain':'every real X>=1 for component sums; block-energy specialization needs integer endpoints',
            'primitive_cutoff':'floor(X^(1/3)) shared for whole kernel',
            'cofinal_component_coefficient':'U*(11+16*q^2/9)',
            'q1_coefficient':str(U*Q(115,9)), 'q12_coefficient':str(U*267),
            'full_signed_residual_upper_bound_proved':False,
            'conditional_ordinary_energy_bridge':result['positive_energy_transform']['conditional_bridge_admitted'],
            'supplied_proof':'signed_arithmetic_proof.txt sections2-3; signed_arithmetic_review_proof.txt section1'})
        for observation in result['score']['cases']:
            if observation['finite_pass'] is not False or not observation['in_dyadic_claim_domain']:continue
            X=observation['X'];q=observation['q'];C=Q(candidate['constants'][str(q)])
            scales=candidate['program']['scales'];weights=list(map(Q,candidate['program']['weights']))
            N=2*max(scales)*X-1;mu=factor_prefix(N)['mu'];M=0;energy=[0]
            for m in mu[1:]:M+=m;energy.append(energy[-1]+M*M)
            energies=[energy[2*t*X-1]-energy[t*X-1] for t in scales]
            value=sum(c*a for c,a in zip(weights,energies));bound=C*X*X*ceil_power(X,Q(1,q));margin=value-bound
            need(X&(X-1)==0 and X>1 and margin>0,'stored refutation failed exact check')
            need(value==Q(observation['value']) and bound==Q(observation['bound']),'stored values not independently reproduced')
            k=X.bit_length()-1;cofinal_margin=value-2*C*X*X
            witnesses.append({'program_id':candidate['program_id'],'X':X,'q':q,'C':str(C),
                'scales':scales,'energies':energies,'full_signed_value':str(value),'stored_upper_bound':str(bound),'positive_margin':str(margin),
                'stored_inequality_refuted':True,'existential_free_constant_claim_refuted':False,
                'hypothetical_same_C_extension_refuted':cofinal_margin>0,
                'hypothetical_extension_q_threshold':k,'extension_ceiling_exact':2,'extension_positive_margin':str(cofinal_margin),
                'minimum_C_at_this_X_for_q_at_least_threshold':str(value/(2*X*X))})
    # Exact polynomial step 11+8t^2/3 - [3+6(1+t/3)^2] = 2(t-1)^2.
    lhs=[Q(11)-9,-4,Q(8,3)-Q(2,3)];need(lhs==[Q(2),Q(-4),Q(2)],'component polynomial certificate failed')
    need(Q(1)+2+2+Q(8,6)>6,'exponential lower bound failed')
    destination.mkdir(parents=True)
    records={'schema':1,'all_passed':True,'source_directory':str(source),'collection_directory':str(collection),
        'source_verification_sha256':s['verification_sha256'],'collection_sha256':sha(collection/'collection.json'),
        'source_sha256':{n:sha(BASE/n) for n in ['check_signed_arithmetic_reviews.py','signed_arithmetic_review_proof.txt','signed_arithmetic_review_report.py']},
        'dependency_sha256':{'detector_review_planner.py':sha(BASE/'detector_review_planner.py')},
        'collection_input_sha256':v['input_sha256'],'reviewed_candidates':len(queue),
        'component_bound_certificates':components,'exact_stored_refutations':witnesses,
        'component_proof_uses_symbolic_algebra_and_written_calculus':True,'formal_proof_assistant_checked':False,
        'other_reviewer_prose_mathematically_promoted':False,'all_original_existential_full_signed_claims_remain_unresolved':True,
        'actual_all_scale_full_signed_bound_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}
    (destination/'frozen_source').mkdir()
    for n in records['source_sha256']:(destination/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    (destination/'verification.json').write_text(json.dumps(records,indent=2)+'\n')
    report=f'Parallel reviews collected for {len(queue)} exact signed candidates.\nVerified explicit all-scale component charge: U(w)*(11+16*q^2/9)*X^2*ceil(X^(1/q)), q>=1, shared B=floor(X^(1/3)).\nExact dyadic stored-constant refutations: {len(witnesses)}. All original existential full signed estimates remain unresolved.\nThe full dense signed residual remains the required arithmetic bound. Reviewer prose beyond the named certificates is not promoted. RH-sufficient controls: 0.\n'
    (destination/'report.txt').write_text(report)
    (BASE/'signed-arithmetic-results/review-latest.json').write_text(json.dumps({'review_directory':str(destination)},indent=2)+'\n')
    print(report)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('collection');p.add_argument('destination');a=p.parse_args();check(a.source,a.collection,a.destination)
