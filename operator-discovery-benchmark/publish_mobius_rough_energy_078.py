"""Archive078 outcomes and execute the generic postrun proof-rule feedback.

No arithmetic source is queried and no prior scientific experiment is rerun.
"""
import json
from fractions import Fraction as Q

import run_mobius_rough_energy_078 as RUN
import mobius_prime_mass_gate_078 as GATE
import check_mobius_prime_mass_gate_078 as CHECK
from run_fractional_prime_kernel_051 import write

POST_FILES=['mobius_prime_mass_gate_078.py','test_mobius_prime_mass_gate_078.py',
    'mobius_prime_mass_gate_search_078_development.json','check_mobius_prime_mass_gate_078.py',
    'test_check_mobius_prime_mass_gate_078.py','mobius_prime_mass_gate_checker_078_development.json',
    'MOBIUS_PRIME_MASS_GATE_CHECK_SCOPE_078.txt','MOBIUS_ROUGH_ENERGY_POSTREVIEW_078.txt',
    'publish_mobius_rough_energy_078.py']


def main():
    out=RUN.OUT;root=RUN.ROOT
    counts=RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():raise ValueError('preserve078 '+name)
    post={name:(root/name).read_bytes() for name in POST_FILES}
    for name,content in post.items():
        if name.endswith('_development.json') and json.loads(content)['status']!='PASS':raise ValueError('postrun development must pass')
    (out/'postrun_snapshot').mkdir()
    for name,content in post.items():
        with (out/'postrun_snapshot'/name).open('xb') as f:f.write(content)
    report=json.loads((out/'report.json').read_text())
    records=[];jobs=[];checker_ops=0
    for result in report['results']:
        candidate=json.loads((out/('candidate_'+result['id']+'.json')).read_text())
        old=json.loads((RUN.PRIOR.OUT/('construction_'+candidate['source_id']+'.json')).read_text())
        base=old['kernel_binding']['kernel']
        if base!=GATE.F.KERNEL:raise ValueError('source kernel binding differs from077')
        fixed=GATE.fixed_kernel(base,old['program']);admissions=[]
        row=dict(id=candidate['id'],source_id=candidate['source_id'],kernel_proposal=fixed,ray_records=[])
        if fixed['status']=='FIXED_KERNEL_PROPOSAL':
            binding=CHECK.verify_kernel(base,old['program'],fixed['kernel'])
            if binding['status']!='VERIFIED_FIXED_KERNEL':raise ValueError('fixed source binding '+str(binding))
            checker_ops+=binding['ops'];row['kernel_admission']=binding
            for index in range(len(candidate['program']['rays'])):
                proposal=GATE.propose_gate(fixed['kernel'],sorted(old['search']['prime_schedule']),candidate['gamma'],candidate['program'],index)
                item=dict(ray_index=index,proposal=proposal)
                if proposal['status']=='PNT_PRIME_MASS_OBSTRUCTION_PROPOSAL':
                    admission=CHECK.verify_prime_mass_gate(fixed['kernel'],sorted(old['search']['prime_schedule']),candidate['gamma'],candidate['program'],proposal['certificate'])
                    if admission['status']!='VERIFIED_PRIME_MASS_OBSTRUCTION':raise ValueError('PNT gate admission '+str(admission))
                    checker_ops+=admission['ops'];item['admission']=admission;admissions.append(admission)
                row['ray_records'].append(item)
        row['uniform_energy_method_obstructed']=bool(admissions)
        row['arithmetic_residual_refuted']=False
        records.append(row)
        jobs.append(GATE.next_search_feedback(candidate,result,admissions))
    write(out/'postrun_prime_mass_gates.json',dict(records=records,checker_operations=checker_ops,
        scientific_arithmetic_queries=0,imported_theorem=GATE.PNT_REFERENCE,
        uniform_energy_methods_obstructed=sum(r['uniform_energy_method_obstructed'] for r in records),
        arithmetic_residuals_refuted=0,uniform_residual_bound_proved=False,RH_proved=False))
    write(out/'postrun_next_search_input.json',dict(schema='rough-energy-obstruction-to-flux-search-v1',jobs=jobs,
        formal_flux_inequality='For h=floor(u/2),s=(h/u)^q,tau>s: F(u)-tau F(h) <= tau/(tau-s)*(V(u)-V(h))^T M_u (V(u)-V(h))/u^q',
        matrix='M_u=dd^T+sum lambda*u^(-2eta)*a*a^T; d=allones',
        proof_rule='nonnegative eta gives M_u<=M_h; Young inequality or a full block PSD certificate controls cross terms',
        arithmetic_flux_bound_still_required=True,flux_scientific_search_run=False,
        uniform_drift_proved=False,RH_proved=False))
    obstructed=sum(r['uniform_energy_method_obstructed'] for r in records)
    handoff='''SIGNED ROUGH AUXILIARY-ENERGY SEARCH078 AND PRIME-MASS FEEDBACK

The detector now actually searches auxiliary constructions and signed bounds,
not only operators or numerical residual constants. It ran459 LP proposals
over17 fractional rough cutoffs and952 weighted square atoms for three fixed
076 residuals. All27 frozen recurrence formulas FAILED independent validation.
The goal of all-scale signed arithmetic control and an RH proof remains OPEN.

Latest run: import run_mobius_rough_energy_078; OUT is077's
residual_fold_followup_001/rough_energy_followup_001. Read report.json,
candidate_*.json, discovery_checks_*.json, validation_checks_*.json,
postrun_prime_mass_gates.json and postrun_next_search_input.json.
Scientific session97929 completed normally in79.844502959seconds. No process
needs resuming. All historical artifacts, failures and source archives remain.

Original source and unpaid target

071's necessary slice is N=15k,y=16k,p3,q5,r1,j1,D20k,
Z(k)=M(10k)-M(8k)-M(20k)+M(16k), J1=Z(k)-2k H_mu(u)H_mu(v).
The exact lift is G(u)=M(u//8)-M(u//10)-M(u//4)+M(u//5), Z(t)=G(floor80t).
The separable price, full parameter family, source/head/core and RH transfer
are still unpaid. 076's51 programs/43 finite survivors/eight refutations and
077's48 fixed-prime absolute-coefficient method obstructions stay unchanged.

078 selects the existing surviving residuals q1_p16 (G), q1_p04
(G+(3547/8192)G(u//3)) and q1_p00 (prime-block predictor). Fixed folded prime
setP2357 preserves each full signed residual and its parent count tokens.
The remaining old formulas are preserved, not declared disproved or exhausted.

Actual new search language and data

For each folded coefficient kernelc, H=maxsupport, y=ceil(H^gamma), V has
seven SIGNED rough factor layers0..6 plus three SIGNED least-prime bins with
cutoffsceil(H^(gamma/3)),ceil(H^(2gamma/3)),y. Each child bin equals MINUS
its corresponding complete rough-child aggregate. Units, strict factors,
squares, cut boundaries and shared parent count tokens are literal. SumV=R
exactly. The degree condition y^7>=H is a resource/domain gate, not an
arithmetic counterexample. The API admits arbitrary rational exponents;
the finite pilot generates reduced gamma in[1/7,2/3] with denominator<=9.

The new energy is E(u)=R(u)^2+sum lambda*u^(-2eta)*(a.V(u))^2.
136 coordinate/pair/channel contrasts and7eta in[0,1] with denominator<=4
give952 auxiliary atoms. Lambda is positive, and projection-only rays are
excluded. E>=R^2 is an unconditional algebraic certificate. No growth bound
follows from that certificate alone. A synthetic recovery test made the LP
discover a nonzero auxiliary yielding constant normalized energy, validated
its continuation and rejected a deliberately broken continuation.

For fixedq=1,129/128,33/32 andtau=1/2,3/4,1 the LP searches
 E(u)/u^q <= tau E(floor(u/2))/floor(u/2)^q+C.
It charges observed base values as well as C/(1-tau); tau1 usesbase+C only
as a numerical score and would imply LOGARITHMIC normalized growth if its
uniform drift and complete base were proved. Coefficients are rounded down,
their exact weighted budget repaired, and C recalibrated upwards before
freezing. All signed cross terms are retained before interval evaluation.

102 discovery parent rows and170 validation parent rows use phase0,5,...75,79.
Discoveryk128,256,512,1024,2048,4096; sparse observedbasek64. Validationk192,
384,768,1536,3072,6144,8192,16384,32768,65536. EVERY literal half is admitted.
426 unique parents supply10848 new signed feature rows; two independent
factor constructions agree exactly. These are NEW rough decompositions of
KNOWN076 arithmetic, not a fresh historical holdout or extended mu prefix.
The sparse observed base is NOT a complete residual-energy induction base.

Results and exact obstruction feedback

All27 selected formulas had improved exact discovery scores (ratios about
0.62713..0.91125 to matching zero-auxiliary scores). All27 then failed:
1813 validation recurrences refuted,2777 certified,zero interval ambiguities.
Matching baselines also all failed,928 rows. No uniform candidate survives.
The actual arithmetic operators/residuals are NOT refuted by these failures.

The strongest discovery score was q1_p04 q1 tau3/4 gamma3/5, ratio
31990120424/51010077999. Its first validation witnessu122801,h61400 has
drift lower about0.04523473, exceeding frozenC about0.029094845;68 of its
170 validation rows fail. Larger fitted constants would define new formulas.

A new independently checked prime-mass rule rejects auxiliary energies
that must grow too quickly, even if their drift constant is increased.
For a fixed rational prefix kernel c(n)=sum a_d 1_(n<=u//d), m=sum a_d/d,
and fixed foldedP, the terminal prime coordinate is asymptotic to
 -m*product((p-1)/p)*u/logu for0<gamma<1, by the classical prime number
theorem. A positive PURE-PRIME auxiliary square with2-2eta>q andm!=0
forces E/u^q to outgrow every constant timeslogu. This contradicts either
uniformtau<1 or uniformtau1 constant drift with finite base. This is an
eventual negative ENERGY-METHOD theorem, not a finite threshold, a lower
bound onR, a positive arithmetic estimate or an RH refutation.

The generic rule binds each fixed direct source kernel independently,
checks mass, finite fold factor and exponent exactly, and imports PNT
explicitly with a primary reference. Variable prime-count kernels,
coupled rays, zero mass and critical/supercritical eta are outside its
conclusion; none is declared safe. See MOBIUS_ROUGH_ENERGY_POSTREVIEW_078.txt
and MOBIUS_PRIME_MASS_GATE_CHECK_SCOPE_078.txt for proof and scope.
'''
    handoff+=f'It verifies all-scale energy obstructions for{obstructed} of the27 formulas.\n'
    handoff+='''
Next concrete bound target

postrun_next_search_input.json exports all27 exact failed formulas, physical
witnesses, applicable proved prime-mass exclusions and new signed scale-change
targets. Define h=floor(u/2),D=V(u)-V(h),F=E/u^q and
M_u=dd^T+sum lambda*u^(-2eta)*aa^T. Then M_u<=M_h. For s=(h/u)^q<tau,
 F(u)-tau F(h) <= [tau/(tau-s)] D^T M_u D/u^q.
Thus a separately proved bound for the signed scale-change energy would
pay the recurrence. Atq1,tau1/2 andevenu, s=tau and this generic price is
infinite; tau3/4 givesprice3 andtau1 givesprice2. More selective block PSD
or correlation constructions may retain useful negative cross terms.

The next SCIENTIFIC SEARCH SHOULD TARGET THIS SIGNED SCALE-CHANGE BOUND,
including every new outer-shell integer, moving prime/factor category
boundary and count-token change at both parents. Do not rerun only the
same finite energy fitting with largerC. A flux equal to the unpaid drift
is circular. Actual signed arithmetic control, complete energy base,
uniform parameter closure and original whole head/core transfer remain.
The flux proof rule is derived in postreview and exported, but its own
scientific construction/bound search HAS NOT RUN yet.

Validation and resources

Two existing user-authorized Sol6.1 agents handled substantial independent
checker and mathematical review work.15 distinct pre-run tests pass over26
successful executions. Postrun counts and all attempts are recorded in
publication_integrity.json and the new development receipts. No unchanged
historical scientific run or old test suite was replayed. No hashes.

Science3workers,nativethreads1,79.844502959s. Constructor work22180126758,
checker work2949636014 are implementation counters including source factor
initialization, not CPU cycles. Sampled parallelRSS2005319680 bytes;
conservative sum of process peaks2746163200 bytes (about2.56GiB), below
the authorized16GiB. Authorized runtime7200s/stage remains. Preserve480
older frozen files plus10 pre-run078 files and9postrun files=499 total.
Root handoff pointers advance; historical handoffs remain archived unchanged.
The RH goal is still ACTIVE and unfinished.
'''
    with (out/'HANDOFF.txt').open('x') as f:f.write(handoff)
    pointer=(root/'MOBIUS_ROUGH_ENERGY_HANDOFF.txt')
    with pointer.open('x') as f:f.write(handoff)
    previous=json.loads((RUN.PRIOR.OUT/'publication_integrity.json').read_text())
    names=previous['continuation_pointers_updated']+['MOBIUS_RESIDUAL_FOLD_HANDOFF.txt']
    for name in names:
        (root/name).write_text('Latest continuation: MOBIUS_ROUGH_ENERGY_HANDOFF.txt\n\n078 completed signed auxiliary-energy discovery; all27 frozen drift formulas failed validation.\nNew checked prime-mass obstructions and signed scale-change feedback are archived.\nThe original all-scale signed arithmetic/RH objective is still open. Preserve historical archives.\n')
    for name,content in post.items():
        if (root/name).read_bytes()!=content or (out/'postrun_snapshot'/name).read_bytes()!=content:raise ValueError('postrun source changed '+name)
    RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():raise ValueError('frozen078 source changed '+name)
    receipts={name:json.loads((root/name).read_text()) for name in RUN.FILES+POST_FILES if name.endswith('_development.json')}
    post_receipts=[receipts[name] for name in POST_FILES if name.endswith('_development.json')]
    publication=dict(status='PUBLISHED_SIGNED_ENERGY_SEARCH_FAILURES_AND_PRIME_MASS_FEEDBACK',
        prior_frozen_counts=counts,prior_frozen_total=sum(counts),prerun_files=RUN.FILES,postrun_files=POST_FILES,
        total_frozen_files=sum(counts)+len(RUN.FILES)+len(POST_FILES),
        prerun_distinct_tests=15,prerun_test_executions=26,
        postrun_distinct_tests=sum(r.get('distinct_tests',r['attempts'][-1]['tests_run']) for r in post_receipts),
        postrun_test_executions=sum(a['tests_run'] for r in post_receipts for a in r['attempts']),
        final_development_receipts='PASS',scientific_session=97929,scientific_elapsed_seconds=report['elapsed_seconds'],
        scientific_completed_normally=True,all_frozen_recurrences_refuted=True,
        verified_uniform_energy_obstructions=obstructed,postrun_arithmetic_source_queries=0,
        continuation_pointers_updated=names,hashes_used=False,old_science_replayed=False,
        uniform_drift_proved=False,uniform_residual_bound_proved=False,uniform_source_bound_proved=False,
        uniform_head_bound_proved=False,uniform_core_bound_proved=False,RH_proved=False)
    write(out/'publication_integrity.json',publication)
    print(json.dumps({k:publication[k] for k in ('status','total_frozen_files','verified_uniform_energy_obstructions','postrun_distinct_tests','postrun_test_executions')}))


if __name__=='__main__':main()
