"""Freeze, run and independently audit a bounded structural candidate search."""
import argparse
import ast
from fractions import Fraction as Q
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import semantic_potential_discovery as D
import potential_candidate_language as L

ROOT = Path(__file__).resolve().parent
TESTS = ['test_potential_candidate_language', 'test_check_potential_candidate_discovery',
         'test_potential_candidate_semantics', 'test_check_potential_candidate_semantics',
         'test_semantic_potential_discovery_workflow']
ALLOCATIONS = dict(preparation=40000000, generation=15000000, discovery=145000000,
                   final=100000000, independent=150000000)
DEVELOPMENT_OPERATIONS = 2326670  # 10845 producer + 7987 checker + 2307838 workflow.
ROOT_RESERVE = 1000000
CAP = 8388608
RESIDENT_CELLS = 1000000


class ResidentMeter:
    """Shared stage counter plus bounded root metadata and external source reserve."""
    def __init__(self, meter):
        self.base = meter
    def __getattr__(self, name):
        return getattr(self.base, name)
    def live(self, cells):
        return self.base.live(cells + RESIDENT_CELLS)


def bound_metadata(meter, *values):
    cells = 0
    def count(value):
        nonlocal cells
        meter.charge()
        cells += 1
        if type(value) is dict:
            cells += 2*len(value)
            for key,item in value.items(): count(key); count(item)
        elif type(value) in (list,tuple):
            cells += len(value)
            for item in value: count(item)
        elif type(value) is str:
            cells += len(value)//8+1
        if cells > RESIDENT_CELLS-100000:
            raise OverflowError('bounded retained root metadata reserve')
    for value in values: count(value)
    return cells


def write(path, value):
    data = (D.canonical(value) + '\n').encode()
    if len(data) > CAP:
        raise OverflowError('8MiB individual artifact cap')
    with Path(path).open('xb') as handle:
        handle.write(data)


def read(path):
    with Path(path).open('rb') as handle:
        data = handle.read(CAP + 1)
    if len(data) > CAP:
        raise OverflowError('8MiB individual input cap')
    return json.loads(data)


def protocol():
    return dict(schema='semantic-structural-potential-discovery-v2', target='actual_mobius',
        allocations=ALLOCATIONS, total_work=450000000, stages_have_shared_meters=True,
        training=list(D.TRAIN), validation=list(D.VALIDATION), final=list(D.FINAL), levels=list(D.LEVELS),
        families=list(D.FAMILIES), initial_family_quota=8, max_initial=40, max_mutations=24, selected_structures=8,
        diagnostic_cap=D.DISCOVERY_MAX, diagnostic_max_cases=2,
        diagnostics_used_for_ranking=False, independent_semantic_reconstruction=True,
        selection='calibration/coupled_sum/coupled_bank/nonlinear/exploration slots; masked mixed cores keep core class; mechanism-family diversity; calibration max2, ordinary mechanism max3 before noncalibration overflow; finite rank uses shared validation failures, anchored costs q12/6/3/2, W1, complexity, ordinal id',
        baseline='always evaluated; excluded only from structural parent/lead slots',
        constants='exact training maximum; frozen before validation; never refitted on final',
        final_controls=['one', 'partial_prime_2'], source_overlap_with_previous_research=True,
        numerical_optimizer=False, hashes=False, research_attempts=1, independent_audits=1,
        memory_bytes=6*1024**3, max_cells=6000000, max_bits=4096, stage_seconds=3600,
        root_resident_cells=RESIDENT_CELLS,
        tests=TESTS, development_operations=DEVELOPMENT_OPERATIONS, root_reserve=ROOT_RESERVE, **D.FLAGS)


def sources():
    pending = ['run_semantic_potential_discovery', 'semantic_potential_discovery',
               'potential_candidate_semantics', 'check_potential_candidate_semantics',
               'potential_candidate_language', 'check_potential_candidate_discovery', *TESTS]
    found = set()
    while pending:
        name = pending.pop(); path = ROOT/(name+'.py')
        if name in found or not path.is_file():
            continue
        found.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in found) + ['semantic_potential_discovery_contract.txt',
                                           'semantic_potential_discovery_soundness.txt']


def freeze(directory):
    d = Path(directory).resolve()
    if d.exists():
        raise FileExistsError('fresh structural-discovery directory required')
    names = sources()
    if sum((ROOT/n).stat().st_size for n in names) > CAP:
        raise OverflowError('bounded source snapshot')
    d.mkdir(); (d/'source_snapshot').mkdir()
    for name in names:
        (d/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(d/'protocol.json', protocol()); write(d/'source_snapshot.json', names)


def synthetic_receipt(stdout):
    found = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', stdout, re.M)
    if len(found) != len(TESTS) or sorted(k for k, v in found) != sorted(TESTS):
        raise ValueError('all cumulative arithmetic and semantic test receipts required')
    frozen = {k: int(v) for k, v in found}
    total = DEVELOPMENT_OPERATIONS + ROOT_RESERVE + sum(frozen.values())
    if total > 25000000:
        raise OverflowError('cumulative development/frozen synthetic25m cap')
    return dict(development=DEVELOPMENT_OPERATIONS, root_reserve=ROOT_RESERVE,
                frozen_modules=frozen, total=total)


def frozen_source(directory):
    names=read(directory/'source_snapshot.json')
    if names != sources():
        raise ValueError('complete frozen source list')
    for name in names:
        current=(ROOT/name).read_bytes()
        if current != (directory/'source_snapshot'/name).read_bytes():
            raise ValueError('source changed after freeze: '+name)


def evaluate_one(record, values, scales, meter, *, include_initial=False):
    result = dict(id=record['id'], status='available', cases=[])
    try:
        L.validate_candidate(record['program'], meter)
        evaluator = L.Evaluator(values, meter)
        if include_initial:
            result['initial'] = evaluator.measure(record['program'], 1)
        for X in scales:
            result['cases'].append(evaluator.case(record['program'], X))
    except (OverflowError, TimeoutError, MemoryError) as error:
        result.update(status='missing', reason=str(error) or type(error).__name__)
    except (ValueError, TypeError, KeyError, ZeroDivisionError) as error:
        result.update(status='invalid', reason=str(error) or type(error).__name__)
    return result


def discovery_round(d, label, records, values, work, generation):
    training = []
    for record in records:
        result = evaluate_one(record, values, D.TRAIN, work, include_initial=True)
        result['constants'] = D.fit_constants(result['cases'], generation) if result['status'] == 'available' else None
        training.append(result)
    # This file exists before any validation computation of this generation.
    write(d/(label+'_training.json'), training)
    evidence = []
    for record, trained in zip(records, training):
        result = dict(trained)
        result['training_cases'] = result.pop('cases')
        result['validation_cases'] = []; result['validation_scores'] = []
        result['diagnostics'] = dict(status='not_attempted', cases=[], scores=[])
        if trained['status'] == 'available':
            checked = evaluate_one(record, values, D.VALIDATION, work)
            result['validation_cases'] = checked['cases']
            if checked['status'] == 'available':
                result['validation_scores'] = D.assess(checked['cases'], trained['constants'], generation)
            else:
                result.update(status=checked['status'], reason=checked['reason'])
            diagnostic = evaluate_one(record, values, record['exposure']['diagnostic_scales'], work)
            diagnostic['scores'] = D.assess(diagnostic['cases'], trained['constants'], generation) if diagnostic['status']=='available' else []
            result['diagnostics'] = diagnostic
        evidence.append(result)
    write(d/(label+'_evidence.json'), evidence)
    return evidence


def run(directory):
    d = Path(directory).resolve()
    if read(d/'protocol.json') != protocol():
        raise ValueError('fixed protocol required')
    frozen_source(d)
    write(d/'run_started.json', dict(one_structural_search=True))
    memory = 6*1024**3
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (memory, hard))
    start, cpu = time.monotonic(), time.process_time()
    meters = {}; receipt = dict(status='UNKNOWN', **D.FLAGS)
    try:
        tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS],
                               cwd=ROOT, text=True, capture_output=True, timeout=300)
        test_record = dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr)
        if tests.returncode == 0:
            test_record['work'] = synthetic_receipt(tests.stdout)
        write(d/'tests.json', test_record)
        if tests.returncode:
            raise ValueError('frozen tests failed; no research computation started')
        generation = ResidentMeter(L.Meter(ALLOCATIONS['generation'], deadline=time.monotonic()+3600))
        work = ResidentMeter(L.Meter(ALLOCATIONS['discovery'], deadline=time.monotonic()+3600))
        meters.update(generation=generation, discovery=work)
        batch = D.generate_initial(generation); write(d/'generation0_batch.json', batch)
        bound_metadata(generation,batch)
        values = L.mobius(4*D.DISCOVERY_MAX-1, work)
        initial_evidence = discovery_round(d, 'generation0', batch['records'], values, work, generation)
        bound_metadata(generation,batch,initial_evidence)
        parents = D.choose(batch['records'], initial_evidence, generation)
        write(d/'adaptive_parents.json', parents)
        mutations = D.generate_mutations(parents, batch['records'], generation)
        bound_metadata(generation,batch,initial_evidence,mutations,parents)
        write(d/'generation1_batch.json', mutations)
        later = discovery_round(d, 'generation1', mutations['records'], values, work, generation)
        records = batch['records'] + mutations['records']; evidence = initial_evidence + later
        bound_metadata(generation,batch,mutations,evidence,records,parents)
        selected = D.choose(records, evidence, generation)
        selected = [batch['records'][0]] + selected
        by_id = {e['id']: e for e in evidence}
        final_batch = [dict(record=r, constants=by_id[r['id']]['constants']) for r in selected]
        write(d/'final_batch.json', final_batch)
        write(d/'proof_queue.json', [D.obligation(r) for r in selected if r['id']])
        final = ResidentMeter(L.Meter(ALLOCATIONS['final'], deadline=time.monotonic()+3600)); meters['final'] = final
        actual = L.mobius(4*max(D.FINAL)-1, final); responses = []
        for source in ('mu', 'one', 'partial_prime_2'):
            values = L.control_source(source, actual, final)
            for item in final_batch:
                result = evaluate_one(item['record'], values, D.FINAL, final, include_initial=True)
                result.update(source=source, constants=item['constants'])
                result['scores'] = D.assess(result['cases'], item['constants'], generation) if result['status'] == 'available' else []
                responses.append(result)
                bound_metadata(generation,batch,mutations,evidence,records,parents,final_batch,responses)
        write(d/'final_responses.json', responses)
        receipt.update(status='CANDIDATE_LEADS', generated=len(records)-1,
                       selected_ids=[r['id'] for r in selected if r['id']],
                       final_available=sum(r['status']=='available' for r in responses),
                       final_missing=sum(r['status']=='missing' for r in responses),
                       final_invalid=sum(r['status']=='invalid' for r in responses))
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError, subprocess.TimeoutExpired) as error:
        receipt.update(status='UNKNOWN', reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        receipt.update(stage_counts={name:m.counts() for name,m in meters.items()},
            cost=dict(elapsed_seconds=time.monotonic()-start, cpu_seconds=time.process_time()-cpu,
                      peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      enforced_memory_bytes=memory))
        write(d/'receipt.json', receipt)
        resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return receipt


def _independent_constants(cases, meter):
    out = {}
    for q in D.LEVELS:
        maximum = Q(0)
        for case in cases:
            k = 1
            while k**q < case['X']:
                meter.charge(q+1); k += 1
            meter.charge(4); maximum = max(maximum, Q(case['innovation'])/k)
        out[str(q)] = str(maximum)
    return out


def _independent_scores(cases, constants, meter):
    out = []
    for case in cases:
        for q in D.LEVELS:
            k = 1
            while k**q < case['X']:
                meter.charge(q+1); k += 1
            meter.charge(4); bound = Q(constants[str(q)])*k
            out.append(dict(X=case['X'], q=q, bound=str(bound), passed=Q(case['innovation'])<=bound,
                            in_dyadic_claim_domain=case['X'] & (case['X']-1) == 0))
    return out


def _independent_choose(records, evidence, meter):
    candidates = []
    by_id = {r['id']:r for r in records}
    for e in evidence:
        if e['status'] != 'available' or e['id'] == 0:
            continue
        r = by_id[e['id']]; costs = []
        for q in reversed(D.LEVELS):
            value = Q(e['initial']['W']); X = 1
            while X < max(D.VALIDATION):
                k = 1
                while k**q < X:
                    meter.charge(q+1); k += 1
                meter.charge(3); value += Q(e['constants'][str(q)])*k; X *= 2
            costs.append(value)
        key = (sum(not s['passed'] for s in e['validation_scores']), tuple(costs),
               Q(e['initial']['W']), r['complexity'], r['id'])
        candidates.append((key, r))
    candidates.sort(key=lambda pair:pair[0]); chosen = []
    def mechanism(r):
        semantic=r['semantics']; name=semantic['mechanism']
        if name=='mask' and len(semantic['states'])==1:
            core=semantic['states'][0]['core_mechanism']
            if core in ('coupled_sum','coupled_bank','nonlinear'): name=core
        return name
    def group(r):
        name=mechanism(r)
        if name in ('lag','mask','bounded_root','target_copy'): return 'calibration'
        if name in ('unknown','multi_state'): return 'exploration'
        return name
    def absent(r): return all(r['id']!=c['id'] for c in chosen)
    for slot in ('calibration','coupled_sum','coupled_bank','nonlinear','exploration'):
        item=next((r for _,r in candidates if group(r)==slot),None)
        if item is not None: chosen.append(item)
    for require_diversity in (True,False):
        for _,r in candidates:
            if len(chosen)==8: break
            g=group(r); n=sum(group(c)==g for c in chosen)
            if not absent(r) or n>=(2 if g=='calibration' else 3): continue
            if require_diversity and any((mechanism(c),c['family'])==
                                        (mechanism(r),r['family']) for c in chosen): continue
            chosen.append(r)
    for _,r in candidates:
        if len(chosen)==8: break
        if absent(r) and group(r)!='calibration': chosen.append(r)
    return chosen


def audit(directory):
    import check_potential_candidate_discovery as C
    import check_potential_candidate_semantics as CS
    d = Path(directory).resolve(); write(d/'independent_started.json', dict(one_audit=True))
    start = time.monotonic(); soft,hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (6*1024**3,hard))
    meter = ResidentMeter(C.Meter(ALLOCATIONS['independent'], deadline=start+3600))
    result = dict(status='UNKNOWN', workflow_verified=False, finite_arithmetic_verified=False, **D.FLAGS)
    checked = 0
    def require(condition, message):
        if not condition:
            raise ValueError(message)
    def input_file(name):
        value = read(d/name); meter.charge(len(D.canonical(value))//32+1); return value
    try:
        frozen_source(d)
        require(input_file('protocol.json') == protocol(), 'fixed complete protocol')
        receipt = input_file('receipt.json'); tests = input_file('tests.json')
        require(tests['returncode'] == 0 and tests['work'] == synthetic_receipt(tests['stdout'])
                and tests['stderr'].rstrip().endswith('OK'), 'one successful frozen suite and cumulative development')
        for stage, count in receipt['stage_counts'].items():
            require(stage in ('generation','discovery','final') and type(count['operations']) is int
                    and 0 <= count['operations'] <= ALLOCATIONS[stage], 'whole shared stage limits')
        require(all(receipt[k] is False for k in D.FLAGS), 'finite evidence has no theorem flags')
        if receipt['status'] != 'CANDIDATE_LEADS':
            result.update(workflow_verified=True, reason=receipt.get('reason','incomplete search'))
        else:
            require(set(receipt['stage_counts'])=={'generation','discovery','final'}, 'complete run retains every shared stage receipt')
            records = []; evidence = []; parents = []
            for generation in (0,1):
                batch = input_file('generation%d_batch.json'%generation)
                expected = D.generate_initial(meter) if generation == 0 else D.generate_mutations(parents,records,meter)
                require(batch == expected, 'replay of declared structural generation by full payload equality')
                training = input_file('generation%d_training.json'%generation)
                current = input_file('generation%d_evidence.json'%generation)
                require(len(training)==len(current)==len(batch['records']), 'all generated candidates retained')
                for r,trained,e in zip(batch['records'],training,current):
                    require(trained['id']==e['id']==r['id'], 'ordinal evidence binding')
                    CS.verify(r['program'],r['semantics'],meter)
                    checker = C.Checker(4*D.DISCOVERY_MAX-1,meter)
                    C.validate_candidate(r['program'],meter)
                    if 'initial' in trained:
                        checker.verify_measure(r['program'],trained['initial']); checked += 1
                    require([c['X'] for c in trained['cases']] == list(D.TRAIN)[:len(trained['cases'])], 'ordered complete training prefix')
                    for case in trained['cases']:
                        checker.verify_case(r['program'],case); checked += 1
                    if trained['status']=='available':
                        require(len(trained['cases'])==len(D.TRAIN) and 'initial' in trained
                            and trained['constants']==_independent_constants(trained['cases'],meter), 'complete exact training fit')
                    else:
                        require(trained['status'] in ('missing','invalid') and trained.get('reason') and trained['constants'] is None,
                                'explicit failed training and no manufactured constant')
                    require(e['training_cases']==trained['cases'] and e['constants']==trained['constants']
                            and e.get('initial')==trained.get('initial'), 'validation does not alter frozen training')
                    require([c['X'] for c in e['validation_cases']] == list(D.VALIDATION)[:len(e['validation_cases'])], 'ordered validation prefix')
                    for case in e['validation_cases']:
                        checker.verify_case(r['program'],case); checked += 1
                    if e['status']=='available':
                        require(trained['status']=='available' and len(e['validation_cases'])==len(D.VALIDATION)
                            and e['validation_scores']==_independent_scores(e['validation_cases'],e['constants'],meter), 'fixed constants on complete validation')
                    else:
                        require(e['status'] in ('missing','invalid') and e.get('reason') and not e['validation_scores'], 'explicit incomplete evidence')
                    diagnostic=e['diagnostics']; planned=r['exposure']['diagnostic_scales']
                    require([c['X'] for c in diagnostic['cases']]==planned[:len(diagnostic['cases'])], 'prospective ordered selector diagnostics')
                    for case in diagnostic['cases']:
                        checker.verify_case(r['program'],case); checked+=1
                    if diagnostic['status']=='available':
                        require(trained['status']=='available' and len(diagnostic['cases'])==len(planned)
                                and diagnostic['scores']==_independent_scores(diagnostic['cases'],e['constants'],meter),
                                'complete separately scored selector diagnostics')
                    elif diagnostic['status']=='not_attempted':
                        require(trained['status']!='available' and not diagnostic['cases'] and not diagnostic['scores'], 'diagnostics unavailable after failed training')
                    else:
                        require(diagnostic['status'] in ('missing','invalid') and diagnostic.get('reason') and not diagnostic['scores'], 'explicit incomplete diagnostics')
                    del checker
                records += batch['records']; evidence += current
                bound_metadata(meter,batch,training,current,records,evidence,parents)
                if generation == 0:
                    parents = _independent_choose(records,evidence,meter)
                    require(input_file('adaptive_parents.json')==parents, 'structural parents selected by declared evidence rule')
            selected = [records[0]] + _independent_choose(records,evidence,meter)
            by_id = {e['id']:e for e in evidence}
            expected = [dict(record=r,constants=by_id[r['id']]['constants']) for r in selected]
            require(input_file('final_batch.json')==expected, 'final programs/constants fixed from discovery evidence')
            require(input_file('proof_queue.json')==[D.obligation(r) for r in selected if r['id']], 'complete unproved obligations, no final cherry-picking')
            final = input_file('final_responses.json'); require(len(final)==3*len(selected), 'all selected actual/control outcomes retained')
            for source_index,source in enumerate(('mu','one','partial_prime_2')):
                for offset,item in enumerate(expected):
                    row = final[source_index*len(selected)+offset]; record=item['record']
                    require(row['id']==record['id'] and row['source']==source and row['constants']==item['constants'], 'final arithmetic source/program/frozen constants')
                    checker=C.Checker(4*max(D.FINAL)-1,meter,source=source)
                    if 'initial' in row:
                        checker.verify_measure(record['program'],row['initial']); checked+=1
                    require([c['X'] for c in row['cases']] == list(D.FINAL)[:len(row['cases'])], 'ordered final complete prefix')
                    for case in row['cases']:
                        checker.verify_case(record['program'],case); checked+=1
                    if row['status']=='available':
                        require(len(row['cases'])==len(D.FINAL) and 'initial' in row
                            and row['scores']==_independent_scores(row['cases'],row['constants'],meter), 'complete finite final arithmetic')
                    else:
                        require(row['status'] in ('missing','invalid') and row.get('reason') and not row['scores'], 'explicit incomplete final result')
                    del checker
            bound_metadata(meter,records,evidence,parents,expected,final)
            result.update(status='FINITE_EVALUATION_VERIFIED', workflow_verified=True, finite_arithmetic_verified=True,
                semantic_annotations_verified=True,
                generated=len(records)-1, selected_ids=[r['id'] for r in selected if r['id']],
                scope='independent complete finite arithmetic and scoped semantic annotations; generation/exposure replay share implementation; no global estimate or proof')
    except (ValueError,TypeError,KeyError,OverflowError,TimeoutError,MemoryError) as error:
        result.update(reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        result.update(cases_verified=checked,counts=meter.counts(),elapsed_seconds=time.monotonic()-start)
        write(d/'independent_verification.json',result)
        resource.setrlimit(resource.RLIMIT_AS,(soft,hard))
    return result


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['freeze','run','audit']); parser.add_argument('directory')
    args=parser.parse_args(); result=globals()[args.command](args.directory)
    if result is not None:
        print(D.canonical(result))
