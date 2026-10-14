"""Postselection domain checker for a reviewed arithmetic growth obstruction.

Uses the general uniform even-prime/core theorem proved in the adjacent text.
It checks exact theorem membership, not the prose proof in a formal system.
It never modifies the frozen numerical search, formulas, constants or reviews.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

BASE=Path(__file__).resolve().parent
PROOF='factor_region_even_prime_core_posthoc_proof.txt'
REVIEW='factor_region_even_prime_core_posthoc_review.txt'
FILES=[PROOF,REVIEW,'factor_region_asymptotic_backend.py','test_factor_region_asymptotic_backend.py']


def digest(x):
    return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def require(ok,message):
    if not ok:raise ValueError(message)


def rational(x):
    require(type(x) in (int,str) or isinstance(x,Q),'exact rational required')
    return Q(x)


def filter_terms(target):
    require(isinstance(target,dict) and set(target)=={'r','l','filter'},'actual target schema')
    require(all(type(target[k]) is int and target[k]>=0 for k in ('r','l')),'actual integer arities')
    require(target['r']+target['l']>=1,'nonzero total arity')
    require(isinstance(target['filter'],list),'fixed finite filter required')
    merged={}
    for t in target['filter']:
        require(isinstance(t,dict) and set(t)=={'divisor','weight'},'fixed filter term schema')
        d=t['divisor'];require(type(d) is int and d>=1,'fixed positive integer divisor')
        merged[d]=merged.get(d,Q(0))+rational(t['weight'])
    return [(d,w) for d,w in sorted(merged.items()) if w]


def nonzero_half_multiplier(terms):
    """Exact rational test, restricted to the existing c pole budget <=2 terms."""
    require(1<=len(terms)<=2,'one/two-term multiplier domain')
    if len(terms)==1:
        return dict(nonzero=True,reason='single nonzero coefficient',exact_difference=None)
    (d,w),(e,v)=terms
    difference=w*w*e-v*v*d
    return dict(nonzero=bool(w*v>0 or difference),
                reason='same signs' if w*v>0 else 'opposite signs compared by exact squared magnitudes',
                exact_difference=str(difference))


def certificate(program):
    base=dict(program_id=digest(program),actual_all_scale_signed_bound_proved=False,
              RH_proved=False,direct_target_energy_claim_refuted=False,
              formal_machine_checked_proof=False,finite_data_used=False)
    try:
        require(isinstance(program,dict) and set(program)=={'target','terms','constants'},'potential program schema')
        target=program['target'];terms=filter_terms(target)
        require(isinstance(program['terms'],list) and isinstance(program['constants'],dict),'potential terms/constants schema')
        matching=[]
        for term in program['terms']:
            require(isinstance(term,dict) and set(term)=={'feature','weight'},'potential term schema')
            w=rational(term['weight']);require(w>=0,'all potential coefficients must be nonnegative')
            f=term['feature'];require(isinstance(f,dict) and set(f)=={'scheme','scheme_id','vector','eta','feature_id'},'complete square feature schema')
            require(digest({k:v for k,v in f.items() if k!='feature_id'})==f['feature_id'],'feature digest mismatch')
            s=f['scheme'];require(isinstance(s,dict) and set(s)=={'prime_power','core_power'},'fixed rational cutoff scheme')
            require(digest(s)==f['scheme_id'],'scheme digest mismatch')
            theta,phi=(rational(s[k]) for k in ('prime_power','core_power'))
            require(theta>0 and phi>0,'positive fixed cutoff exponents')
            require(isinstance(f['vector'],list) and len(f['vector'])==9,'complete region vector')
            vector=list(map(rational,f['vector']));eta=rational(f['eta']);require(eta>=0,'nonnegative normalizer exponent')
            if (w>0 and theta>=Q(1,3) and phi==Q(1,2) and eta<Q(1,2) and vector[2]
                    and all(not x for i,x in enumerate(vector) if i!=2)):
                matching.append(dict(feature_id=f['feature_id'],weight=str(w),vector_multiplier=str(vector[2]),
                                     prime_power=str(theta),core_power=str(phi),eta=str(eta),
                                     growth_power=str(Q(1,2)-eta),log_denominator_power=4,
                                     energy_asymptotic_prefactor=str(6144*w*vector[2]**2)))
        if target['r']!=1 or target['l']!=1 or not 1<=len(terms)<=2:
            return dict(base,status='unsupported',global_potential_innovation_claim_refuted=False,
                        reason='theorem gate requires actual c=mu*lambda and one/two nonzero fixed filter terms')
        multiplier=nonzero_half_multiplier(terms)
        if not multiplier['nonzero'] or not matching:
            return dict(base,status='unsupported',global_potential_innovation_claim_refuted=False,
                        multiplier=multiplier,reason='leading multiplier vanishes or no covered positive singleton')
        return dict(base,status='global_refutation',global_potential_innovation_claim_refuted=True,
                    witnesses=matching,multiplier=multiplier,
                    multiplier_expression=[dict(divisor=d,weight=str(w)) for d,w in terms],
                    energy_asymptotic='prefactor * P(1/2)^2 * X^growth_power/(log X)^4',
                    theorem_scope='complete actual component2; fixed parent cutoffs; every sufficiently large dyadic X',
                    threshold_explicit=False,
                    contradiction='W>=positive term; all-cofinal innovation telescopes to W=O_q(X^(1/q)); choose 1/q<growth_power',
                    imported_theorem='unconditional Prime Number Theorem pi(t)~t/log(t)',
                    imported_theorem_url='https://dlmf.nist.gov/27.2.E3')
    except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:
        return dict(base,status='invalid',global_potential_innovation_claim_refuted=False,reason=str(e))


def audit(directory,destination):
    require(not sys.flags.optimize and os.environ.get('PYTHONOPTIMIZE','') in ('','0'),
            'verified theorem-domain runtime requires assertions enabled')
    d=Path(directory).resolve();dest=Path(destination).resolve()
    require(not dest.exists(),'new postselection audit destination required')
    verification_sha=sha(d/'verification.json')
    verified=read(d/'verification.json');require(verified['all_passed'] is True,'verified finite arithmetic required')
    start={name:sha(d/name) for name in verified['input_sha256']}
    require(start==verified['input_sha256'],'numerical inputs changed')
    for name,expected in verified['code_sha256'].items():
        require(sha(d/'frozen_source'/name)==expected,'frozen numerical source changed')
    collection=d/'review-collection-001';collection_sha=sha(collection/'collection.json');reviews=read(collection/'collection.json')
    require(reviews['all_passed'] is True and reviews['reviewed_candidates']==verified['selected_count'],'complete analytical queue coverage required')
    for name,expected in reviews['input_sha256'].items():
        require(sha(collection/name)==expected,'collected review changed')
    # The independent prose review binds the exact complete analytical argument.
    proof_sha=sha(BASE/PROOF)
    require(proof_sha in (BASE/REVIEW).read_text(),'independent review does not bind proof hash')
    analytical_hashes={name:sha(BASE/name) for name in FILES}
    tests=subprocess.run([sys.executable,'-B','-m','unittest','test_factor_region_asymptotic_backend'],
                         cwd=BASE,capture_output=True,text=True)
    require(tests.returncode==0,'postselection theorem-domain tests failed')
    test_output=tests.stdout+tests.stderr
    batches=read(d/'candidate_batch.json')['factories'];queue=read(d/'proof_queue.json')['queue']
    proposals={}
    for factory in batches:
        for c in factory['candidates']:
            pid=c['program_id']
            require(pid==digest(c['program']) and pid not in proposals,'archive identity/uniqueness mismatch')
            proposals[pid]=c['program']
    require(len(proposals)==verified['candidate_count'],'verified archive coverage mismatch')
    certificates={pid:certificate(p) for pid,p in proposals.items()}
    require(all(c['status']!='invalid' for c in certificates.values()),'malformed candidate theorem input')
    rejected={pid:c for pid,c in certificates.items() if c['global_potential_innovation_claim_refuted']}
    selected_ids={c['program_id'] for c in queue}
    selected=[]
    final_scores={r['program_id']:r['score'] for r in read(d/'final_evaluation.json')['results']}
    for q in queue:
        pid=q['program_id'];require(digest(q['exact_program'])==pid and q['exact_program']==proposals[pid],
                                    'selected formula digest/archive mismatch')
        selected.append(dict(program_id=pid,exact_program_sha256=pid,precise_claim_sha256=q['precise_claim_sha256'],
                             original_formula_changed=False,
                             original_global_claim_disposition='refuted' if pid in rejected else 'unresolved',
                             certificate=certificates[pid],final_score=final_scores[pid]))
    require({name:sha(d/name) for name in start}==start,'numerical inputs changed during adjudication')
    require(sha(d/'verification.json')==verification_sha and sha(collection/'collection.json')==collection_sha,
            'verification/review collection changed during adjudication')
    for name,expected in reviews['input_sha256'].items():
        require(sha(collection/name)==expected,'review changed during adjudication')
    for name,expected in verified['code_sha256'].items():
        require(sha(d/'frozen_source'/name)==expected,'frozen source changed during adjudication')
    require({name:sha(BASE/name) for name in FILES}==analytical_hashes,'analytical source changed during adjudication')
    dest.mkdir(parents=True,exist_ok=False);(dest/'frozen_source').mkdir()
    for name,expected in analytical_hashes.items():
        raw=(BASE/name).read_bytes();require(hashlib.sha256(raw).hexdigest()==expected,'proof source changed before copy')
        with (dest/'frozen_source'/name).open('xb') as f:f.write(raw)
    with (dest/'contract_tests.txt').open('x') as f:f.write(test_output)
    result=dict(schema=1,all_domain_checks_passed=True,source_directory=str(d),
                source_verification_sha256=verification_sha,source_input_sha256=start,
                source_review_collection_sha256=collection_sha,
                analytical_source_sha256=analytical_hashes,
                contract_tests_sha256=sha(dest/'contract_tests.txt'),
                candidate_count=len(proposals),covered_global_refutations=rejected,
                selected=selected,selected_refuted_ids=sorted(selected_ids&set(rejected)),
                remaining_selected_global_claims=len(selected_ids-set(rejected)),
                numerical_selection_changed=False,analytical_proof_independently_reviewed=True,
                formal_machine_checked_proof=False,actual_all_scale_signed_bound_proved=False,RH_proved=False)
    with (dest/'adjudication.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory');parser.add_argument('destination')
    args=parser.parse_args();r=audit(args.directory,args.destination)
    print(json.dumps(dict(archive_refutations=len(r['covered_global_refutations']),selected_refuted_ids=r['selected_refuted_ids'],remaining_selected_global_claims=r['remaining_selected_global_claims'])))
