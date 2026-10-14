"""Freeze, discover and independently assess coupled scale-bound programs."""
import json
from pathlib import Path
import resource
import time

import coupled_scale_bounds as P

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'prime-cofactor-bound-results/pilot-001'
PREVIOUS=ROOT/'fractional-cofactor-bound-results/pilot-001'
OUT=ROOT/'coupled-scale-bound-results/pilot-001'
ARCHIVE=ROOT/'multiscale-bound-results/pilot-001/source_snapshot/core_vectors.jsonl.gz'
FILES=['coupled_scale_bounds.py','check_coupled_scale_bounds.py','coupled_scale_evidence.py',
       'run_coupled_scale_bounds.py','test_coupled_scale_bounds.py',
       'test_check_coupled_scale_bounds.py','test_coupled_scale_evidence.py',
       'coupled_scale_bounds_development.json','check_coupled_scale_bounds_development.json',
       'coupled_scale_evidence_development.json','coupled_scale_bounds_protocol.txt',
       'COUPLED_SCALE_RULE_REVIEW_037.txt','COUPLED_SCALE_CHECK_SCOPE_037.txt']


def read(path):
    return json.loads(path.read_text())


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as stream:
        json.dump(value,stream,indent=2,sort_keys=True)
        stream.write('\n')


def emit(event,**data):
    print(json.dumps(dict(event=event,**data)),flush=True)


def main():
    import check_coupled_scale_bounds as C
    import coupled_scale_evidence as E
    started=time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,resource.getrlimit(resource.RLIMIT_AS)[1]))
    if read(BASE/'report.json')['status']!='PRIME_STATES_AND_AUXILIARY_BOUNDS_VERIFIED_JOINED_BOUND_OPEN':
        raise ValueError('admitted035 source states required')
    if not read(BASE/'verification.json')['verified']:
        raise ValueError('independent base-source admission')
    # Trusted earlier premises are bound by bytes, not a second old search.
    for name in ('check_prime_cofactor_discovery.py','prime_cofactor_observations.py'):
        if (ROOT/name).read_bytes()!=(BASE/'source_snapshot'/name).read_bytes():
            raise ValueError('unchanged source premise required: '+name)
    if (ROOT/'adaptive_rational_exponents.py').read_bytes()!=(PREVIOUS/'source_snapshot/adaptive_rational_exponents.py').read_bytes():
        raise ValueError('unchanged adaptive rational scheduler')
    OUT.mkdir(parents=True,exist_ok=False)
    try:
        for name in FILES:
            path=OUT/'source_snapshot'/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes((ROOT/name).read_bytes())
        for destination,source in [('base035_certificate.json',BASE/'search.json'),
                                   ('previous_next_search_input.json',PREVIOUS/'next_search_input.json')]:
            (OUT/'source_snapshot'/destination).write_bytes(source.read_bytes())
        plan=P.exponent_plan()
        write(OUT/'exponent_plan.json',plan)
        emit('protocol_frozen',offsets=plan['candidates'],memory_gib=16,archive_reused=True)
        base=read(BASE/'search.json')['certificate']
        meter=C.BASE.Meter()
        context=C.prepare(base,meter=meter)
        evidence,handle=E.build_evidence(ARCHIVE,base,scales=P.SCALES,divisors=P.DIVISORS)
        write(OUT/'evidence.json',evidence)
        emit('complete_source_grams_ready',source_checks=evidence['audit'],resource=evidence['metadata'])
        proposal=P.search(base,evidence,plan)
        write(OUT/'search.json',proposal)
        proofs=[C.verify_candidate(context,candidate) for candidate in proposal['candidates']]
        write(OUT/'conditional_verification.json',dict(verified=True,candidates=proofs,
            operations=meter.operations,recurrence_proved=False,whole_signed_bound_proved=False,RH_proved=False))
        emit('candidate_programs_frozen',coverage=proposal['coverage'],candidates=proposal['candidates'])
        intervals=E.interval_audit(handle,proposal['candidates'])
        write(OUT/'interval_audit.json',intervals)
        tables={row['id']:row for row in intervals['candidates']}
        assessments=[]
        for candidate,proof in zip(proposal['candidates'],proofs):
            rows=tables[candidate['id']]['recurrences']
            failures=[r['X'] for r in rows if r['status']=='fail']
            unresolved=[r['X'] for r in rows if r['status']=='unresolved']
            by_partition={name:{status:sum(rows[k]['status']==status for k in ks)
                                for status in ('pass','fail','unresolved')}
                          for name,ks in P.PARTITIONS.items()}
            assessments.append(dict(id=candidate['id'],program=candidate['program'],
                recurrence_C=candidate['recurrence_C'],
                arithmetic_status='REFUTED_ON_OBSERVED_SCALE' if failures else
                    'FINITE_AUDIT_UNRESOLVED' if unresolved else 'FINITE_SURVIVOR_UNPROVED',
                failure_scales=failures,unresolved_scales=unresolved,partitions=by_partition,
                conditional_bound=proof['conditional_energy_bound'],
                generic_proof_attempt=proof['proof_attempt']['status'],
                uniform_recurrence_proved=False))
        survivors=[a for a in assessments if a['arithmetic_status']=='FINITE_SURVIVOR_UNPROVED']
        next_input=read(PREVIOUS/'next_search_input.json')
        next_input['coupled_scale_search']=dict(
            report=str(OUT.relative_to(ROOT)/'report.json'),
            definition=proposal['definition'],helper_definition=proposal['helper_definition'],
            source_binding=base['source'],state_programs=base['states'],
            target_remains_complete_original_core=True,
            inherited_accepted033_obligation_replaced=False,
            finite_assessments=assessments,
            open_lemmas=[proof['open_recurrence'] for proof in proofs if
                         any(a['id']==proof['candidate_id'] for a in survivors)],
            proof_frontier=[dict(candidate_id=proof['candidate_id'],
                paid_helper=proof['paid_helper'],paid_head=proof['paid_head'],
                forcing=proof['forcing_provider'],dependencies=proof['dependency_graph'],
                rejected_generic_rule=proof['proof_attempt']) for proof in proofs],
            next_search_target='prove or replace the complete signed scale-defect inequality using actual source identities',
            permitted_next_constructions=['complete arithmetic divisor identities',
                'signed prime/composite correlation bounds','paid boundary telescoping',
                'new multiscale auxiliaries with independent recovery'],
            feedback='coefficient-size and paid-helper envelopes alone fail; finite arithmetic survivors need additional signed arithmetic constraints',
            finite_evidence_is_not_a_paid_premise=True,recurrence_proved=False)
        write(OUT/'next_search_input.json',next_input)
        report=dict(status='COUPLED_SCALE_PROGRAMS_AUDITED_UNIFORM_BOUND_OPEN',
            complete_original_source=True,current_Z033_isolated=False,
            coverage=proposal['coverage'],candidate_assessments=assessments,
            audited_nonempty_candidates=sum(bool(c['program']) for c in proposal['candidates']),
            finite_survivors=len(survivors),nonempty_finite_survivors=sum(bool(c['program']) for c in survivors),
            conditional_implications_checked=len(proofs),
            arithmetic_recurrences_proved=0,generic_envelope_countermodels=len(proofs),
            recovered_uniform_growth_improvements_proved=0,
            exponent_offsets=plan['candidates'],no_semantic_denominator_ceiling=True,
            reused_data=True,new_data_holdout=False,
            source_exposure=evidence['exposure'],source_audit=evidence['audit'],
            evidence_resource=intervals['metadata'],search_resource=proposal['resource'],
            checker_operations=meter.operations,exponent_operations=plan['operations'],
            development_receipts={name:read(ROOT/name) for name in FILES if name.endswith('_development.json')},
            elapsed_seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            previous_accepted_obligation_unchanged=True,whole_signed_bound_proved=False,RH_proved=False)
        for name in FILES:
            if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():
                raise ValueError('frozen037 source changed: '+name)
        if time.monotonic()-started>1200:
            raise TimeoutError('total037 runtime budget1200s')
        write(OUT/'report.json',report)
        emit('completed',status=report['status'],finite_survivors=report['finite_survivors'],
             nonempty_finite_survivors=report['nonempty_finite_survivors'],
             elapsed_seconds=report['elapsed_seconds'],peak_rss_kib=report['peak_rss_kib'],
             whole_signed_bound_proved=False,RH_proved=False)
    except Exception as error:
        write(OUT/'terminal_failure.json',dict(error=type(error).__name__,message=str(error),
            elapsed_seconds=time.monotonic()-started,evidence_counts=getattr(error,'evidence_counts',None),
            whole_signed_bound_proved=False,RH_proved=False))
        raise


if __name__=='__main__':main()
