"""Independent audit of singleton-column affine elimination and full recovery.

No producer or native solver is imported. Remaining-system proportional row
compression is replayed by the existing independent compression checker.
"""
from fractions import Fraction as F
import hashlib
import json
import check_joint_gram_compressed_replay as C

FLAGS = dict(global_bound_proved=False, RH_proved=False)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def _rational(value, bits, denominator=None, *, output=False):
    if type(value) not in ((int, str, F) if output else (int, F)):
        raise ValueError('exact rational input required')
    if type(value) is str and (len(value) > 4*bits+4 or any(c not in '0123456789+-/' for c in value)):
        raise ValueError('bounded rational output text')
    q = F(value)
    if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > bits:
        raise OverflowError('leaf coefficient bits')
    if denominator is not None and q.denominator > denominator:
        raise OverflowError('leaf denominator limit')
    return q


def _limits(max_rows, max_columns, max_cells, max_work, max_coefficient_bits,
            max_denominator, max_preprocessing_operations, max_preprocessing_cells):
    if any(type(v) is not int or v < 1 for v in (max_rows, max_columns, max_cells, max_work,
            max_coefficient_bits, max_denominator, max_preprocessing_operations, max_preprocessing_cells)):
        raise ValueError('positive strict leaf limits')
    if max_work > 450000000:
        raise ValueError('authorized 450 million total work ceiling')


def _system_hash(labels, support, rows, rhs):
    return digest(dict(row_labels=labels, support=support,
                       rows=[dict(coefficients=[[v, str(row[v])] for v in sorted(row)], rhs=str(b))
                             for row, b in zip(rows, rhs)]))


def rebuild_leaf_system(columns, lhs, support, *, max_rows=20000, max_columns=2000,
                        max_cells=2000000, max_work=450000000, max_coefficient_bits=4096,
                        max_denominator=2**4096, max_preprocessing_operations=200000000,
                        max_preprocessing_cells=4000000, max_receipt_bytes=8388608):
    """Independently find the minimum original variable ID leaf at every step.

    Entire rows are removed and kept as affine equations. No row operation or
    coefficient substitution occurs during elimination. RHS-only rows remain.
    """
    _limits(max_rows, max_columns, max_cells, max_work, max_coefficient_bits,
            max_denominator, max_preprocessing_operations, max_preprocessing_cells)
    if type(max_receipt_bytes) is not int or max_receipt_bytes < 1:
        raise ValueError('positive receipt byte limit')
    if type(columns) is not list or type(lhs) is not dict or type(support) is not list or any(type(i) is not int or not 0 <= i < len(columns) for i in support) or len(set(support)) != len(support):
        raise ValueError('complete unique selected support schema')
    if len(support) > max_columns:
        raise OverflowError('leaf selected column cap')
    labels = set(lhs)
    selected = []
    for i in support:
        if type(columns[i]) is not dict:
            raise ValueError('sparse exact selected column')
        p = {}
        for label, value in columns[i].items():
            q = _rational(value, max_coefficient_bits); labels.add(label)
            if q: p[label] = q
        selected.append(p)
    target = {label: _rational(q, max_coefficient_bits) for label, q in lhs.items()}
    try:
        labels = sorted(labels)
    except TypeError:
        raise ValueError('comparable original row labels')
    if len(labels) > max_rows:
        raise OverflowError('leaf original row cap')
    positions = {v: j for j, v in enumerate(support)}
    row_lookup = {label: r for r, label in enumerate(labels)}
    rows = [{} for _ in labels]
    for variable, column in zip(support, selected):
        for label, coefficient in column.items(): rows[row_lookup[label]][variable] = coefficient
    rhs = [target.get(label, F(0)) for label in labels]
    active_rows = set(range(len(labels))); active_variables = set(support)
    occurrences = {v: {r for r, row in enumerate(rows) if v in row} for v in support}
    pushes = sum(len(occurrences[v]) == 1 for v in support)
    pivots = []
    while True:
        leaves = [v for v in active_variables if len(occurrences[v]) == 1]
        if not leaves: break
        variable = min(leaves); row_index = next(iter(occurrences[variable])); row = rows[row_index]
        equation = [[v, str(row[v])] for v in sorted(row)]
        equation_hash = digest(dict(row_label=labels[row_index], equation=equation, rhs=str(rhs[row_index])))
        pivots.append(dict(variable=variable, support_position=positions[variable], row=row_index,
                           row_label=labels[row_index], coefficient=str(row[variable]), rhs=str(rhs[row_index]),
                           equation=equation, equation_hash=equation_hash))
        active_variables.remove(variable); active_rows.remove(row_index)
        for v in row:
            occurrences[v].remove(row_index)
            if v in active_variables and len(occurrences[v]) == 1: pushes += 1
    retained_positions = [j for j, v in enumerate(support) if v in active_variables]
    retained_variables = [support[j] for j in retained_positions]
    retained_rows = sorted(active_rows); retained_labels = [labels[r] for r in retained_rows]
    remaining_rows = [rows[r] for r in retained_rows]; remaining_rhs = [rhs[r] for r in retained_rows]
    reduced_columns = [{labels[r]: rows[r][v] for r in retained_rows if v in rows[r]} for v in retained_variables]
    # Explicit zero values preserve zero rows as well as nonzero RHS-only rows.
    reduced_target = {labels[r]: rhs[r] for r in retained_rows}
    original_hash = _system_hash(labels, support, rows, rhs)
    remaining_hash = _system_hash(retained_labels, retained_variables, remaining_rows, remaining_rhs)
    m, n, t = len(labels), len(support), len(lhs)
    nnz = sum(map(len, selected)); remaining_nnz = sum(map(len, reduced_columns))
    rm, rn, lp = len(retained_rows), len(retained_variables), len(pivots)
    pivot_entries = sum(len(p['equation']) for p in pivots)
    entries = len(lhs)+sum(len(columns[v]) for v in support)
    ledger = dict(preprocessing=0, input=entries+nnz+t, row_order=m*m,
                  incidence=m+n+3*nnz, binding=2*nnz+2*m+n+2*remaining_nnz+2*rm+rn,
                  queue_scan=n, queue=n*(2*pushes), pivot_scan=pushes,
                  pivot_archive=2*pivot_entries+lp, pivot_update=2*lp+pivot_entries,
                  reduced=2*remaining_nnz+rn+rm+n+m, receipt=0)
    # A zero-length producer phase is absent unless charge() was called.
    if not n: ledger.pop('queue_scan')
    if not pushes:
        ledger.pop('queue'); ledger.pop('pivot_scan')
    if not lp:
        ledger.pop('pivot_archive'); ledger.pop('pivot_update')
    pre = sum(ledger.values())
    cells = 3*nnz+t+m+n+2*pivot_entries+lp+remaining_nnz+rm
    back = 8*pivot_entries+4*lp+2*n+1
    verification = 6*nnz+3*t+3*m+4*n+1
    post_cells = 3*nnz+6*n+m+1
    if pre+back+verification >= max_work or pre+back+verification >= max_preprocessing_operations:
        raise OverflowError('leaf preprocessing plus postprocessing work reserve')
    if cells+post_cells >= max_preprocessing_cells:
        raise OverflowError('leaf preprocessing plus postprocessing cell reserve')
    return dict(original_row_labels=labels, original_system_hash=original_hash,
                remaining_system_hash=remaining_hash, pivots=pivots,
                retained_support_positions=retained_positions, retained_variable_indices=retained_variables,
                retained_rows=retained_rows, reduced_columns=reduced_columns, reduced_target=reduced_target,
                selected_columns=selected, original_rhs=target, original_rows=rows, rhs=rhs,
                original_support=list(support), inconsistent_rhs_rows=[r for r in retained_rows if not rows[r] and rhs[r]],
                schema='fixed-support-singleton-column-elimination-v1',
                ordering='minimum (original variable index, original row index)', native_call_interruptible=False,
                original_variables=n, remaining_variables=rn, remaining_rows=rm,
                input_entry_count=entries, selected_nonzero_count=nnz, remaining_nonzero_count=remaining_nnz,
                heap_pushes=pushes, heap_pops=pushes, pivot_entry_count=pivot_entries,
                original_work_proxy=m*max(1,n)**2, preprocessing_work=pre, preprocessing_cells=cells,
                backsubstitution_work_reserve=back, full_verification_work_reserve=verification,
                postprocessing_cells_reserve=post_cells, leaf_work_reserve=pre+back+verification,
                work_ledger=ledger)


def verify_leaf_preprocessing(columns, lhs, support, receipt, **limits):
    expected = rebuild_leaf_system(columns, lhs, support, **limits)
    if type(receipt) is not dict:
        raise ValueError('leaf elimination receipt required')
    for key in ('schema', 'ordering', 'native_call_interruptible', 'original_support',
                'original_row_labels', 'original_system_hash', 'remaining_system_hash', 'pivots',
                'retained_support_positions', 'retained_variable_indices', 'retained_rows',
                'original_variables', 'remaining_variables', 'remaining_rows', 'input_entry_count',
                'selected_nonzero_count', 'remaining_nonzero_count', 'heap_pushes', 'heap_pops',
                'pivot_entry_count', 'original_work_proxy', 'preprocessing_work', 'preprocessing_cells',
                'backsubstitution_work_reserve', 'full_verification_work_reserve',
                'postprocessing_cells_reserve', 'leaf_work_reserve'):
        if key not in receipt or digest(receipt[key]) != digest(expected[key]):
            raise ValueError('independent deterministic leaf replay '+key)
    if type(receipt.get('original_rows')) is not int or receipt['original_rows'] != len(expected['original_rows']):
        raise ValueError('complete original equation row count')
    allowed_phases = set(expected['work_ledger']) | {'remaining_compression_python', 'backsubstitution', 'full_verification'}
    if type(receipt.get('work_ledger')) is not dict or set(receipt['work_ledger'])-allowed_phases:
        raise ValueError('complete typed leaf resource phases')
    if any(type(value) is not int or value < 0 for value in receipt['work_ledger'].values()):
        raise ValueError('nonnegative exact integer traversal charges')
    for phase, value in expected['work_ledger'].items():
        if receipt['work_ledger'].get(phase) != value:
            raise ValueError('independent leaf traversal ledger '+phase)
    byte_limit = limits.get('max_receipt_bytes', 8388608)
    if len(json.dumps(receipt, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()) > byte_limit:
        raise OverflowError('leaf receipt byte cap')
    return dict(verified=True, complete_original_rows_verified=True,
                deterministic_minimum_variable_pivots_verified=True,
                rhs_only_rows_retained=True, original_rows=len(expected['original_rows']),
                remaining_rows=expected['remaining_rows'], remaining_variables=expected['remaining_variables'],
                reduced_system_sha256=expected['remaining_system_hash'], **FLAGS)


def _verify_rows(rows, rhs, values, bits):
    for row, target in zip(rows, rhs):
        total = F(0)
        # Insertion order follows the original selected support order, which
        # is the producer's accumulation order for bounded intermediates.
        for variable, coefficient in row.items():
            product = _rational(coefficient*values[variable], bits)
            total = _rational(total+product, bits)
        if total != target:
            raise ValueError('all original and retained affine equations')
    return dict(verified=True, all_original_equations_verified=True, rows=len(rows), **FLAGS)


def verify_leaf_solution(columns, lhs, support, answer, receipt, compression_receipt=None,
                         *, require_nonnegative=False, **limits):
    if type(require_nonnegative) is not bool:
        raise ValueError('explicit nonnegative support option')
    preprocessing = verify_leaf_preprocessing(columns, lhs, support, receipt, **limits)
    expected = rebuild_leaf_system(columns, lhs, support, **limits)
    if type(answer) is not list or len(answer) != len(support):
        raise ValueError('complete full returned support weights')
    bits = limits.get('max_coefficient_bits', 4096); denominator = limits.get('max_denominator', 2**4096)
    weights = [_rational(q, bits, denominator, output=True) for q in answer]
    if receipt.get('status') != 'full_original_equality_verified':
        raise ValueError('returned leaf solution requires terminal original equality status')
    if receipt.get('exact_support_weights') != list(map(str, weights)):
        raise ValueError('complete returned leaf support vector binding')
    if require_nonnegative and any(q < 0 for q in weights):
        raise ValueError('nonnegative reconstructed full support weights')
    values = {v: weights[j] for j, v in enumerate(support)}
    for pivot in reversed(expected['pivots']):
        variable = pivot['variable']; residual = _rational(pivot['rhs'], bits, output=True)
        for v, coefficient in pivot['equation']:
            if v != variable:
                product = _rational(F(coefficient)*values[v], bits)
                residual = _rational(residual-product, bits)
        recovered = _rational(residual/F(pivot['coefficient']), bits, denominator)
        if recovered != values[variable]:
            raise ValueError('exact reverse affine leaf back-substitution')
    reduced_weights = [weights[j] for j in expected['retained_support_positions']]
    if receipt.get('reduced_solution') != list(map(str, reduced_weights)):
        raise ValueError('remaining native solution binding')
    recovered = [dict(variable=p['variable'], value=str(values[p['variable']])) for p in reversed(expected['pivots'])]
    if receipt.get('backsubstitution_values') != recovered:
        raise ValueError('all reverse affine recovered values binding')
    reduced_solution = _verify_rows([expected['original_rows'][r] for r in expected['retained_rows']],
                                   [expected['rhs'][r] for r in expected['retained_rows']], values, bits)
    full_solution = _verify_rows(expected['original_rows'], expected['rhs'], values, bits)
    nested = receipt.get('remaining_compression')
    if type(nested) is not dict or (compression_receipt is not None and compression_receipt != nested):
        raise ValueError('remaining-system complete compression receipt binding')
    compression_receipt = nested
    remaining_budget = limits.get('max_work', 450000000)-expected['leaf_work_reserve']
    compression = C.verify_producer_compression(expected['reduced_columns'], expected['reduced_target'],
                     list(range(len(reduced_weights))), compression_receipt, max_work=remaining_budget)
    # Check the Python normalization intermediates covered by the old helper's
    # bit ceiling; the native C routine's internal bits are not bounded here.
    _, augmented = C.augmented_rows(expected['reduced_columns'], expected['reduced_target'], list(range(len(reduced_weights))))
    for row in augmented:
        pivot = next((q for q in row if q), None)
        if pivot is not None:
            for q in row:
                if q: _rational(q/pivot, bits)
    for mapping in compression_receipt['mapping']:
        ratio = _rational(mapping['ratio'], bits, output=True)
        representative = mapping['representative']
        if representative is not None:
            for q in augmented[representative]:
                if q: _rational(ratio*q, bits)
    rm, rn = expected['remaining_rows'], expected['remaining_variables']
    native_cells = compression_receipt['reduced_rows']*(rn+1)
    if native_cells > limits.get('max_cells', 2000000):
        raise OverflowError('remaining native augmented cell cap')
    native_total = compression_receipt['total_work_proxy']
    leaf_total = expected['leaf_work_reserve']+native_total
    if receipt.get('remaining_native_total_work_proxy') != native_total or receipt.get('leaf_total_work_proxy') != leaf_total:
        raise ValueError('complete leaf plus native work accounting')
    wrapper_work = sum(receipt.get(key, 0) for key in ('compilation_work_reserve', 'dual_build_work_proxy', 'dual_verification_work_reserve'))
    for key in ('compilation_work_reserve', 'dual_build_work_proxy', 'dual_verification_work_reserve'):
        if key in receipt and (type(receipt[key]) is not int or receipt[key] < 0):
            raise ValueError('nonnegative integer outer resource reserve')
    if receipt.get('total_work_proxy') != leaf_total+wrapper_work or leaf_total > limits.get('max_work', 450000000) or leaf_total+wrapper_work > 450000000:
        raise ValueError('authorized leaf total work gate')
    pivot_entries, lp = expected['pivot_entry_count'], len(expected['pivots'])
    n, nnz, t, m = len(support), expected['selected_nonzero_count'], len(lhs), len(expected['original_rows'])
    back_work = 4*pivot_entries+lp+2*rn
    full_work = n+4*nnz+t+m+1
    compression_python = compression_receipt.get('preprocessing_actual_work', compression_receipt['preprocessing_work'])
    actual_work = expected['preprocessing_work']+compression_python+back_work+full_work
    actual_cells = expected['preprocessing_cells']+compression_receipt['preprocessing_cells']+rn+pivot_entries+nnz
    ledger = dict(expected['work_ledger'], remaining_compression_python=compression_python,
                  backsubstitution=back_work, full_verification=full_work)
    if not back_work: ledger.pop('backsubstitution')
    if receipt.get('work_ledger') != ledger or type(receipt.get('preprocessing_actual_work')) is not int or type(receipt.get('preprocessing_actual_cells')) is not int or receipt['preprocessing_actual_work'] != actual_work or receipt['preprocessing_actual_cells'] != actual_cells:
        raise ValueError('independent complete preprocessing/backsubstitution/verification ledger')
    if actual_work > limits.get('max_preprocessing_operations', 200000000) or actual_cells > limits.get('max_preprocessing_cells', 4000000):
        raise OverflowError('complete leaf preprocessing/postprocessing caps')
    if compression_python > limits.get('max_preprocessing_operations', 200000000)-expected['leaf_work_reserve']:
        raise OverflowError('remaining helper preprocessing allocation cap')
    if compression_receipt['preprocessing_cells'] > limits.get('max_preprocessing_cells', 4000000)-expected['preprocessing_cells']-expected['postprocessing_cells_reserve']:
        raise OverflowError('remaining helper preprocessing cell allocation cap')
    if back_work > expected['backsubstitution_work_reserve'] or full_work > expected['full_verification_work_reserve']:
        raise ValueError('leaf postprocessing work reserve domination')
    return dict(verified=True, preprocessing=preprocessing, reduced_solution=reduced_solution,
                full_original_solution=full_solution, reverse_back_substitution_verified=True,
                all_support_weights_verified=True, nonnegative_support_verified=require_nonnegative,
                compression=compression, leaf_total_work_proxy=leaf_total,
                preprocessing_actual_work=actual_work, preprocessing_actual_cells=actual_cells,
                native_cells=native_cells, resource_limits_verified=True, **FLAGS)
