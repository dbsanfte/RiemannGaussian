"""Preserve079 outcomes and export checked obstructions as next search inputs."""
import json
from fractions import Fraction as Q

import run_mobius_scale_flux_079 as RUN
import mobius_flux_mass_gate_079 as GATE
import check_mobius_flux_mass_gate_079 as CHECK
from run_fractional_prime_kernel_051 import write as write_new

POST_FILES = ['mobius_flux_mass_gate_079.py', 'test_mobius_flux_mass_gate_079.py',
    'mobius_flux_mass_gate_search_079_development.json', 'check_mobius_flux_mass_gate_079.py',
    'test_check_mobius_flux_mass_gate_079.py', 'mobius_flux_mass_gate_checker_079_development.json',
    'MOBIUS_FLUX_MASS_GATE_CHECK_SCOPE_079.txt', 'MOBIUS_SCALE_FLUX_POSTREVIEW_079.txt',
    'publish_mobius_scale_flux_079.py', 'publish_mobius_scale_flux_079_failed_attempt_001.py']


def write(path, value):
    """Resume a failed export only when an existing artifact matches exactly."""
    if path.exists():
        if path.read_text() != json.dumps(value, indent=2, sort_keys=True)+'\n':
            raise ValueError('preserve differing publication artifact '+str(path))
    else:
        write_new(path, value)


def main():
    root, out = RUN.ROOT, RUN.OUT
    counts = RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes() != (out/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve079 '+name)
    post = {name: (root/name).read_bytes() for name in POST_FILES}
    for name, content in post.items():
        if name.endswith('_development.json') and json.loads(content)['status'] != 'PASS':
            raise ValueError('postrun development must pass')
    (out/'postrun_snapshot').mkdir(exist_ok=True)
    for name, content in post.items():
        target = out/'postrun_snapshot'/name
        if target.exists():
            if target.read_bytes() != content:
                raise ValueError('preserve differing frozen postrun source '+name)
        else:
            with target.open('xb') as f:
                f.write(content)
    report = json.loads((out/'report.json').read_text())
    metadata = json.loads((out/'source_metadata.json').read_text())
    records, jobs, checker_ops = [], [], 0
    for result in report['results']:
        candidate = json.loads((out/('candidate_'+result['id']+'.json')).read_text())
        meta = metadata[candidate['source_id']]
        # These fixed hypotheses are linked to every actual source/half row
        # by the frozen079 runner, independently of postrun asymptotics.
        if (meta['source_binding']['status'] != 'VERIFIED_FIXED_KERNEL'
                or meta['norm_admission']['status'] != 'VERIFIED_UNIFORM_COEFFICIENT_NORM'
                or meta['norm_admission']['folded_kernel'] != meta['norm']['folded_kernel']
                or meta['norm_admission']['excluded_primes'] != meta['primes']):
            raise ValueError('postrun fixed source/norm/fold binding')
        leaves, admissions = [], []
        for index, leaf in enumerate(candidate['leaves']):
            proposal = GATE.propose_gate(meta['fixed_kernel'], meta['primes'], candidate['gamma'], candidate['q'], leaf['a'])
            admission = dict(status='UNPAID_OTHER_SIGNED_LEAF', uniform_correlation_proved=False)
            if proposal['status'] == 'FLUX_MASS_OBSTRUCTION_PROPOSAL':
                admission = RUN.require(CHECK.verify_flux_mass_gate(meta['fixed_kernel'], meta['primes'], candidate['gamma'], candidate['q'], leaf['a'], proposal['certificate']), 'VERIFIED_FLUX_MASS_OBSTRUCTION')
                checker_ops += admission['ops']
            leaves.append(dict(index=index, ray=leaf['a'], proposal=proposal, admission=admission))
            admissions.append(admission)
        obstructed = any(x['status'] == 'VERIFIED_FLUX_MASS_OBSTRUCTION' for x in admissions)
        records.append(dict(id=candidate['id'], source_id=candidate['source_id'], leaves=leaves,
            uniform_local_bound_method_obstructed=obstructed, arithmetic_residual_refuted=False))
        jobs.append(GATE.feedback(candidate, result, admissions))
    obstructed = sum(x['uniform_local_bound_method_obstructed'] for x in records)
    gate_count = sum(leaf['admission']['status'] == 'VERIFIED_FLUX_MASS_OBSTRUCTION' for record in records for leaf in record['leaves'])
    write(out/'postrun_flux_mass_gates.json', dict(records=records, verified_obstructions=gate_count,
        uniform_cover_methods_obstructed=obstructed, checker_operations=checker_ops,
        scientific_arithmetic_queries=0, effective_finite_threshold_supplied=False,
        imported_theorem=GATE.OLD.PNT_REFERENCE, arithmetic_residuals_refuted=0,
        uniform_residual_bound_proved=False, RH_proved=False))
    write(out/'postrun_next_search_input.json', dict(schema='flux-covariance-obstruction-to-construction-search-v1',
        jobs=jobs, next_scientific_search_run=False,
        priority='generate arithmetic constructions that control the exposed remainder, subject to proved growing-mode exclusions',
        exact_symbolic_mode_constraints_are_necessary_not_sufficient=True,
        complete_small_scale_R_base_paid=True, uniform_correlation_proved=False, RH_proved=False))
    coverage = [dict(u=80*k-79, horizon=(80*k-79)//4,
        least_prime_cutoff=RUN.SEARCH.P.T.rational_cutoff((80*k-79)//4, '5/24')) for k in RUN.SPEC['discovery_k']]
    write(out/'postrun_coverage_diagnostic.json', dict(source_id='q1_p16', gamma='5/8', bin=7,
        fixed_excluded_primes=[2, 3, 5, 7], first_allowed_prime=11,
        discovery_anchor_smallest_phase_parent_cutoffs=coverage,
        first_recorded_noncircularity_parent=327601, first_validation_refutation_parent=491441,
        conclusion='this signed channel only begins testing prime11 at the final discovery anchor',
        scope='finite coverage diagnostic, not an impossibility theorem',
        new_obligation='control all prime entry and exit events at moving cutoff boundaries',
        new_arithmetic_queries=0, RH_proved=False))
    receipts = {name: json.loads((root/name).read_text()) for name in RUN.FILES+POST_FILES if name.endswith('_development.json')}
    pre_receipts = [receipts[name] for name in RUN.FILES if name.endswith('_development.json')]
    post_receipts = [receipts[name] for name in POST_FILES if name.endswith('_development.json')]
    distinct = lambda rs: sum(r['distinct_tests'] for r in rs)
    executions = lambda rs: sum(a['tests_run'] for r in rs for a in r['attempts'] if a.get('status', a.get('outcome')) == 'PASS')
    total = sum(counts)+len(RUN.FILES)+len(POST_FILES)
    handoff = f'''SIGNED SCALE-FLUX COVARIANCE SEARCH079 AND GROWING-MODE FEEDBACK

Latest continuation:079 completed an ACTUAL detector search for local signed
bounds and an argument assembling them.102 cover proposals,17 fractional
cutoffs,6 frozen selected constructions; ALL6 failed validation. New generic
prime/semiprime asymptotic rules independently rule out all6 selected local
bound methods for every fixed constant, not just their fitted prices.
The all-scale signed arithmetic/RH objective remains ACTIVE and OPEN.

Location and process
Import run_mobius_scale_flux_079; OUT is078'srough_energy_followup_001/
scale_flux_followup_001. Read report.json, source_metadata.json,
candidate_*.json, validation_checks_*.json, postrun_flux_mass_gates.json,
postrun_next_search_input.json and postrun_coverage_diagnostic.json.
Scientific session59944 finished normally; no process needs resuming.
All historical arithmetic, failures and archived handoffs remain intact.

Original target and preserved source operators
071's necessary slice is N15k,y16k,p3,q5,r1,j1,D20k,
Z(k)=M(10k)-M(8k)-M(20k)+M(16k), J1=Z(k)-2k H_mu(u)H_mu(v).
The exact lift is G(u)=M(u//8)-M(u//10)-M(u//4)+M(u//5), Z(t)=G(floor80t).
The separable price, original correlation, full parameter family and entire
head/core/RH transfer remain unpaid.076's51 programs/43 finite survivors,
eight refutations and077's48 absolute-price method obstructions are unchanged.
078's27 failed auxiliary energies/six prime-mass exclusions also remain.

079 uses fixed sources q1_p16=G and q1_p04=G+(3547/8192)G(u//3), with
P2357 folding. The variable prime predictor q1_p00 and other surviving
operators are preserved outside this fixed-kernel pilot, not disproved.

What the detector constructed and checked
For h=floor(u/2), D=V(u)-V(h), refine both coefficient functions on the
SAME physical integer n. Every occupied cell carries parent/half category,
both coefficient/token polynomials, squarefree count and signed mu count.
Include outer support, gaps, moving categories and literal inherited tokens.
Independently bind every source/half function to the fixed folded kernel,
reconstruct all cells and diagonal Gram B_ij=sum mu^2 delta_i delta_j, and
recombine each endpoint residual. Existing078 feature vectors agree wherever
previously available. No cancellation is assumed from zero-looking samples.

V uses terminal factor layers0..6 and least-prime bins7..9, with cutoffs
ceil(H^(gamma/3)),ceil(H^(2gamma/3)),ceil(H^gamma). Pilot gamma are17 reduced
rationals in[1/7,2/3],denominator<=9; the underlying API accepts other roots
within degree/bit/work gates. All new rows use KNOWN076/078 arithmetic;
there is no extended mu horizon or fresh historical holdout.

Search proper rays of support1or2, axes and slopes±1,±2,±1/2. Each selected
ray has a two-cell nonzero determinant proving it is not a scalar copy of
the full flux. Seek S_a^2<=kappa*u^(q-1)*Q_a, S_a=a.D,Q_a=a^T B a,
q1,129/128,33/32. Floating vectorized ratios/LP propose; exact calibration
rounds kappa upward2^-40, rational elimination reconstructs d=sum t*a,
and independent checks certify discovery. Conditional price radicals use
upward2^-24 enclosures. Formulas freeze BEFORE validation cell queries.

Unconditional proof backend progress
The fixed prefix kernel c_v(n)=sum b_d 1_(n<=v//d) has
 ||c_v||_2^2<=I*v+E<=K*v for v>=base6300,
using exact rational band-square integration and floor error. This yields
 Q_a<=3K max|a|^2 u when h>=base. K=152/525 forq1_p16 and
103079398159/422785843200 forq1_p04. Unit0 vanishes abovebase; terminalr
vanishes ifr*gamma>=1, by exact certificates that define the cover target.

The COMPLETE residual-energy base is paid: A=sum|b_d|/d gives
R(v)^2/v^q<=2base*A^2 for EVERY integer1<=v<2base and real1<=q<2.
Given ALL uniform local covariance leaves, the exact cover implies
 (d.D)^2<=J u^q, J=(sum|t|sqrt_upper(3K*kappa*max|a|^2))^2.
Young gives F(u)<=3/4 F(h)+3J or F(u)<=F(h)+2J forF=R^2/u^q.
The first would imply F<=max(Bbase,12J), conditionally. The uniform
covariance leaves are still unproved; the conditional algebra is not an
all-scale signed theorem. A single fixedq>1 also does not prove RH.

Actual finite outcomes and all-scale negative feedback
85 discovery parents usek256,512,1024,2048,4096;170 validation parents
usek192,384,768,1536,3072,6144,8192,16384,32768,65536;phases0,5,...75,79.
3570 shared cell rows were independently reconstructed. All6 covers fail:
790 local inequalities refuted,2270 certified,zero interval ambiguities.

q1_p16 selects gamma5/8 for allq and
 d=e7+(e1+e8)/2+(e1+e9)/2+(e8+e9)/2;
its validation refutations are187,170,168. q1_p04 selects gamma2/3 and
 d=(e1+e9)+(e7+e8), with91,89,85 refutations. All six containe1+e9.
At q1_p04,q1,u245681 this leaf hasS905431/8192,
Q1030232073959/67108864,kappa746858239043/1099511627776; the exact
positive violation is131948142638925745276299/73786976294838206464.

For fixed kernel massm,foldedmassmP=m*product(1-1/p), ordinary PNT gives
 D1~-mP*u/(2logu). For1/2<gamma<3/4,alpha2gamma/3, the last bin has only
primes/distinctsemiprimes and D9~mP*log((1-alpha)/alpha)*u/(2logu).
A ray in{{1,9}} with nonzero L=mP*(-a1+a9*log((1-alpha)/alpha))/2
has square≫u²/log²u, whereasQ_a=O(u). Therefore ANY constant-kappa leaf
atq<2 fails eventually. Exact rational log series/tail bounds verifyL!=0;
gamma5/8 useslog(7/5),gamma2/3 useslog(5/4). All6 selected methods are
thus ruled out independently of kappa. No finite threshold, Rlowerbound,
residual refutation or positive signed estimate is asserted.
See postreview and independent gate scope for proof/imported PNT source.

Next scientific construction target
The machine-readable feedback exports each actual failed leaf/cover,
uniform obstruction and exact supported-coordinate mode constraint.
Do NOT merely increase kappa or rerun the same two-coordinate grammar.
Generate joint constructions with more arithmetic channels, parameterized
prime/composite pairings and exact coefficient functions where their
proved relationships demand them. Apply growing-mode exclusions first.
Enforce prime entry/exit obligations at moving cutoff boundaries: p16'se7
was empty until its cutoff reached prime11 at the final discoveryanchor;
most discovery rows could not test its later behavior.

Exact a1=a9*log((1-alpha)/alpha) cancels ONLY the first asymptotic mode.
Lowerlogarithmic remainders may still exceed square-root scale. A candidate
must expose that new remainder and a mechanism/lemma/recurrence controlling
it; invented logarithm tokens or more channels alone do not pay the bound.
The next grammar/search after this feedback HAS NOT RUN yet. Uniform
arithmetic correlation leaves and original source/head/core/RH transfer
are the actual unresolved task, not the now-paid coefficient/base bounds.

Validation, resources and preservation
Science3workers,native librarythreads1,{report['elapsed_seconds']}seconds;
sampled parallelRSS{report['sampled_parallel_rss_peak_bytes']}bytes,
conservative processpeak sum{report['conservative_sum_process_peaks_bytes']}bytes,
below16GiB. Authorized stage runtime7200s. Constructor work
{report['constructor_operations']},checker work{report['checker_operations']}
are implementation estimates/counters, not CPUcycles. Postrun has no
arithmetic source queries. No old science/test suite replay, no hashes.
{distinct(pre_receipts)} distinct pre-run tests/{executions(pre_receipts)} successful executions;
{distinct(post_receipts)} distinct postrun tests/{executions(post_receipts)} executions. AllPASS,
all attempts retained. ExistingSol6.1 agents did substantial independent
checker/pre-run proof/workflow review; root handled postrun outcome review.
One export attempt failed because a receipt usedoutcome instead ofstatus;
its source and failure record are preserved. Scientific results unchanged.
Preserve499 older+10 pre-run079+10 postrun079={total} frozen files, with
direct byte comparisons and archived snapshots. Root handoff pointers move;
historical handoffs stay unchanged. The RH goal remains ACTIVE, unfinished.
'''
    with (out/'HANDOFF.txt').open('x') as f:
        f.write(handoff)
    with (root/'MOBIUS_SCALE_FLUX_HANDOFF.txt').open('x') as f:
        f.write(handoff)
    previous = json.loads((RUN.PRIOR.OUT/'publication_integrity.json').read_text())
    pointers = previous['continuation_pointers_updated']+['MOBIUS_ROUGH_ENERGY_HANDOFF.txt']
    for name in pointers:
        (root/name).write_text('Latest continuation: MOBIUS_SCALE_FLUX_HANDOFF.txt\n\n079 completed local signed-covariance discovery and exact conditional covers.\nAll six selected covers failed; checked prime/semiprime modes rule out their local bounds for every constant.\nUniform coefficient norm and complete residual base are paid; signed arithmetic/RH remains open.\nPreserve historical artifacts and use the new construction feedback.\n')
    for name, content in post.items():
        if (root/name).read_bytes() != content or (out/'postrun_snapshot'/name).read_bytes() != content:
            raise ValueError('postrun source changed '+name)
    RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes() != (out/'source_snapshot'/name).read_bytes():
            raise ValueError('079 frozen source changed '+name)
    publication = dict(status='PUBLISHED_LOCAL_COVARIANCE_FAILURES_AND_GROWING_MODE_FEEDBACK',
        prior_frozen_counts=counts, prior_frozen_total=sum(counts), prerun_files=RUN.FILES,
        postrun_files=POST_FILES, total_frozen_files=total,
        prerun_distinct_tests=distinct(pre_receipts), prerun_successful_test_executions=executions(pre_receipts),
        postrun_distinct_tests=distinct(post_receipts), postrun_successful_test_executions=executions(post_receipts),
        final_development_receipts='PASS', scientific_session=59944,
        scientific_elapsed_seconds=report['elapsed_seconds'], scientific_completed_normally=True,
        frozen_candidates=report['frozen_candidates'], all_frozen_covers_failed_local_validation=True,
        verified_uniform_leaf_obstructions=gate_count, uniform_cover_methods_obstructed=obstructed,
        postrun_arithmetic_source_queries=0, continuation_pointers_updated=pointers,
        preserved_failed_export_attempts=1, failed_export_source='publish_mobius_scale_flux_079_failed_attempt_001.py',
        hashes_used=False, old_science_replayed=False, complete_R_energy_base_proved=True,
        uniform_coefficient_norm_proved=True, uniform_correlation_proved=False,
        uniform_residual_bound_proved=False, uniform_source_bound_proved=False,
        uniform_head_bound_proved=False, uniform_core_bound_proved=False, RH_proved=False)
    write(out/'publication_integrity.json', publication)
    print(json.dumps({k: publication[k] for k in ('status', 'total_frozen_files', 'verified_uniform_leaf_obstructions',
        'uniform_cover_methods_obstructed', 'prerun_distinct_tests', 'postrun_distinct_tests')}))


if __name__ == '__main__': main()
