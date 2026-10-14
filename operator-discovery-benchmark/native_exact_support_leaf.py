"""Exact singleton-COLUMN elimination on a fixed declared support.

An eliminated variable occurs in precisely one remaining equation. Removing
that equation therefore creates no Schur update and assumes no sign. Reverse
affine substitution restores every selected variable; full original equality
and, in the dual wrapper, nonnegativity are mandatory. The unchanged compressed
native helper solves the remaining system. Native RREF remains uninterruptible,
so external worker time and memory enforcement are required.

Work limits are deterministic traversal/arithmetic/native proxies, not bounds
on the bit complexity of FLINT's internals. Exact rational intermediates in
the Python preprocessing and back-substitution obey the declared bit ceiling.
"""
from fractions import Fraction as F
import copy
import hashlib
import heapq
import json
import math
import time
import native_exact_support_compressed as N

FLAGS = dict(global_bound_proved=False, RH_proved=False)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def _system(labels, support, rows, target):
    return dict(row_labels=labels, support=support,
                rows=[dict(coefficients=[[support[j], str(q)] for j, q in sorted(row.items(), key=lambda item: support[item[0]])],
                           rhs=str(target[r])) for r, row in enumerate(rows)])


def exact_support_solution(columns, lhs, support, *, deadline=None,
                           max_rows=20000, max_columns=2000, max_cells=2000000,
                           max_work=450000000, max_denominator=2**4096,
                           max_coefficient_bits=4096,
                           max_preprocessing_operations=200000000,
                           max_preprocessing_cells=4000000,
                           max_receipt_bytes=8388608, diagnostics=None,
                           on_checkpoint=None):
    """Return exact signed weights in the ORIGINAL support order, or None.

    None records an inconsistent remaining equality solve; it is returned as
    unknown by the dual wrapper and carries no exclusion of the broader cone.
    ``diagnostics['leaf_elimination']`` binds the complete elimination receipt.
    """
    bounds = (max_rows, max_columns, max_cells, max_work, max_denominator,
              max_coefficient_bits, max_preprocessing_operations,
              max_preprocessing_cells, max_receipt_bytes)
    if any(type(v) is not int or v < 1 for v in bounds):
        raise ValueError('positive strict resource bounds')
    if max_work > 450000000:
        raise ValueError('authorized total charged work ceiling')
    if deadline is not None and (type(deadline) not in (int, float) or not math.isfinite(deadline)):
        raise ValueError('absolute deadline')
    if diagnostics is None:
        diagnostics = {}
    if type(diagnostics) is not dict:
        raise ValueError('diagnostics dictionary')
    if on_checkpoint is not None and not callable(on_checkpoint):
        raise ValueError('optional synchronous checkpoint callback')
    used = cells = 0
    ledger = {}
    info = dict(schema='fixed-support-singleton-column-elimination-v1',
                status='preprocessing', original_support=list(support) if type(support) is list else None,
                pivots=[], ordering='minimum (original variable index, original row index)',
                work_ledger=ledger, native_call_interruptible=False)
    diagnostics['leaf_elimination'] = info

    def charge(work=1, new_cells=0, phase='preprocessing'):
        nonlocal used, cells
        used += work; cells += new_cells
        ledger[phase] = ledger.get(phase, 0) + work
        info['preprocessing_actual_work'] = used
        info['preprocessing_actual_cells'] = cells
        if used > max_preprocessing_operations or used > max_work:
            raise OverflowError('leaf preprocessing/back-substitution work cap')
        if cells > max_preprocessing_cells:
            raise OverflowError('leaf preprocessing/back-substitution cell cap')
        if deadline is not None and time.monotonic() > deadline:
            raise TimeoutError('leaf reconstruction deadline; native call is not interruptible')

    def exact(q, phase='input'):
        charge(phase=phase)
        if type(q) not in (int, F):
            raise ValueError('exact rational input only')
        q = F(q)
        if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > max_coefficient_bits:
            raise OverflowError('leaf rational coefficient bits')
        return q

    def bounded():
        charge(0, phase='receipt')
        try:
            size = len(json.dumps(info, sort_keys=True, separators=(',', ':'), allow_nan=False).encode())
        except (TypeError, ValueError) as e:
            raise ValueError('JSON-serializable exact row labels required') from e
        if size > max_receipt_bytes:
            raise OverflowError('leaf elimination receipt byte cap')

    def emit():
        bounded()
        if on_checkpoint is not None:
            try:
                on_checkpoint(copy.deepcopy(info))
            except (OverflowError, TimeoutError, MemoryError):
                raise
            except Exception as e:
                raise RuntimeError('leaf checkpoint callback failed: '+str(e)) from e

    charge(0)
    if type(columns) is not list or type(lhs) is not dict or type(support) is not list or any(type(i) is not int or not 0 <= i < len(columns) for i in support) or len(set(support)) != len(support):
        raise ValueError('sparse fixed support schema')
    n = len(support)
    if n > max_columns:
        raise OverflowError('original selected support column cap')
    selected = []; keys = set(lhs); input_entries = len(lhs)
    for i in support:
        if type(columns[i]) is not dict:
            raise ValueError('sparse exact column dictionary')
        p = {}; input_entries += len(columns[i])
        for key, q in columns[i].items():
            q = exact(q); keys.add(key)
            if q:
                p[key] = q; charge(1, 1, 'input')
        selected.append(p)
    target = {key: exact(q) for key, q in lhs.items()}
    charge(len(target), len(target), 'input')
    m = len(keys)
    if m > max_rows:
        raise OverflowError('original selected equation row cap')
    # Comparison work reserve covers deterministic sorting independently of
    # Python's particular sorting strategy.
    charge(m*m, phase='row_order')
    try:
        labels = sorted(keys)
    except TypeError as e:
        raise ValueError('comparable exact row labels required') from e
    lookup = {key: r for r, key in enumerate(labels)}
    rows = [{} for _ in labels]; rhs = [target.get(key, F(0)) for key in labels]
    incidence = [set() for _ in support]
    charge(m+n, m+n, 'incidence')
    nnz = sum(map(len, selected))
    for j, p in enumerate(selected):
        for key, q in p.items():
            r = lookup[key]; rows[r][j] = q; incidence[j].add(r)
            charge(3, 2, 'incidence')
    charge(2*nnz+2*m+n, phase='binding')
    info.update(original_row_labels=labels, original_rows=m, original_variables=n,
                input_entry_count=input_entries, selected_nonzero_count=nnz,
                original_system_hash=digest(_system(labels, support, rows, rhs)),
                original_work_proxy=m*max(1,n)**2)
    active_vars = set(range(n)); active_rows = set(range(m)); queue = []
    pushes = pops = pivot_entries = 0
    for j in range(n):
        charge(phase='queue_scan')
        if len(incidence[j]) == 1:
            r = next(iter(incidence[j])); heapq.heappush(queue, (support[j], r, j)); pushes += 1
            charge(n, phase='queue')
    while queue:
        variable, r, j = heapq.heappop(queue); pops += 1
        charge(n, phase='queue')
        charge(phase='pivot_scan')
        if j not in active_vars or incidence[j] != {r} or r not in active_rows:
            continue
        equation = [[support[k], str(q)] for k, q in sorted(rows[r].items(), key=lambda item: support[item[0]])]
        charge(2*len(rows[r])+1, 2*len(rows[r])+1, 'pivot_archive')
        row_hash = digest(dict(row_label=labels[r], equation=equation, rhs=str(rhs[r])))
        info['pivots'].append(dict(variable=variable, support_position=j, row=r,
                                   row_label=labels[r], coefficient=str(rows[r][j]),
                                   rhs=str(rhs[r]), equation=equation, equation_hash=row_hash))
        pivot_entries += len(rows[r])
        active_vars.remove(j); active_rows.remove(r)
        charge(2, phase='pivot_update')
        for k in rows[r]:
            incidence[k].discard(r); charge(phase='pivot_update')
            if k in active_vars and len(incidence[k]) == 1:
                sole = next(iter(incidence[k])); heapq.heappush(queue, (support[k], sole, k)); pushes += 1
                charge(n, phase='queue')
    retained_positions = [j for j in range(n) if j in active_vars]
    retained_rows = [r for r in range(m) if r in active_rows]
    retained_ids = [support[j] for j in retained_positions]
    reduced_columns = []
    for j in retained_positions:
        p = {labels[r]: rows[r][j] for r in incidence[j]}
        reduced_columns.append(p); charge(2*len(p)+1, len(p), 'reduced')
    # Explicit zero RHS keys keep zero and contradiction rows in the domain.
    reduced_target = {labels[r]: rhs[r] for r in retained_rows}
    charge(len(reduced_target)+n+m, len(reduced_target), 'reduced')
    local = {j: k for k, j in enumerate(retained_positions)}
    reduced_rows = [{local[j]: q for j, q in rows[r].items()} for r in retained_rows]
    remaining_nnz = sum(map(len, reduced_columns))
    charge(2*remaining_nnz+2*len(retained_rows)+len(retained_positions), phase='binding')
    info.update(retained_support_positions=retained_positions,
                retained_variable_indices=retained_ids, retained_rows=retained_rows,
                remaining_rows=len(retained_rows), remaining_variables=len(retained_positions),
                remaining_nonzero_count=remaining_nnz,
                remaining_system_hash=digest(_system([labels[r] for r in retained_rows], retained_ids,
                                                     reduced_rows, [rhs[r] for r in retained_rows])),
                heap_pushes=pushes, heap_pops=pops, pivot_entry_count=pivot_entries,
                preprocessing_work=used, preprocessing_cells=cells)
    back_reserve = 8*pivot_entries+4*len(info['pivots'])+2*n+1
    verify_reserve = 6*nnz+3*len(lhs)+3*m+4*n+1
    post_cells = 3*nnz+6*n+m+1
    post_work = back_reserve+verify_reserve
    info.update(backsubstitution_work_reserve=back_reserve,
                full_verification_work_reserve=verify_reserve,
                postprocessing_cells_reserve=post_cells,
                leaf_work_reserve=used+post_work,
                status='prepared_remaining_system')
    emit()
    if used+post_work >= max_work or used+post_work >= max_preprocessing_operations:
        raise OverflowError('leaf preprocessing plus back-substitution/verification reserves')
    if cells+post_cells >= max_preprocessing_cells:
        raise OverflowError('leaf preprocessing plus postprocessing cell reserve')
    native_diagnostics = {}
    pre_work, pre_cells = used, cells
    try:
        remaining = N.exact_support_solution(
            reduced_columns, reduced_target, list(range(len(retained_positions))),
            deadline=deadline, max_rows=max_rows, max_columns=max_columns,
            max_cells=max_cells, max_work=max_work-pre_work-post_work,
            max_denominator=max_denominator, max_coefficient_bits=max_coefficient_bits,
            max_preprocessing_operations=max_preprocessing_operations-pre_work-post_work,
            max_preprocessing_cells=max_preprocessing_cells-pre_cells-post_cells,
            diagnostics=native_diagnostics)
    finally:
        compression = native_diagnostics.get('row_compression')
        if compression is not None:
            info['remaining_compression'] = compression
            info['remaining_native_total_work_proxy'] = compression['total_work_proxy']
            info['leaf_total_work_proxy'] = pre_work+post_work+compression['total_work_proxy']
            info['total_work_proxy'] = info['leaf_total_work_proxy']
        info['status'] = 'remaining_native_completed' if 'row_compression' in native_diagnostics else 'remaining_native_failure'
    emit()
    if remaining is None:
        info['status'] = 'remaining_system_inconsistent'; emit(); return None
    if type(remaining) is not list or len(remaining) != len(retained_positions):
        raise ValueError('remaining native support coverage')
    # Account for the compressed helper's Python work/cells before the final
    # leaf checks; its native proxy is separately included in total_work_proxy.
    comp = info['remaining_compression']
    charge(comp.get('preprocessing_actual_work', comp['preprocessing_work']),
           comp['preprocessing_cells'], 'remaining_compression_python')
    answer = [F(0)]*n; id_to_position = {variable: j for j, variable in enumerate(support)}
    for j, q in zip(retained_positions, remaining):
        answer[j] = exact(q, 'backsubstitution'); charge(1, 1, 'backsubstitution')
    recovered = []
    for pivot in reversed(info['pivots']):
        charge(phase='backsubstitution')
        j = pivot['support_position']; total = exact(F(pivot['rhs']), 'backsubstitution')
        for variable, text in pivot['equation']:
            if variable == pivot['variable']:
                continue
            charge(2, 1, 'backsubstitution')
            product = exact(F(text)*answer[id_to_position[variable]], 'backsubstitution')
            total = exact(total-product, 'backsubstitution')
        answer[j] = exact(total/F(pivot['coefficient']), 'backsubstitution')
        charge(2, 1, 'backsubstitution')
        recovered.append(dict(variable=pivot['variable'], value=str(answer[j])))
    rebuilt = {}
    for p, w in zip(selected, answer):
        w = exact(w, 'full_verification')
        if w.denominator > max_denominator:
            raise OverflowError('restored selected weight denominator')
        for key, q in p.items():
            charge(2, 1, 'full_verification')
            value = exact(rebuilt.get(key, F(0))+exact(w*q, 'full_verification'), 'full_verification')
            if value:
                rebuilt[key] = value
            else:
                rebuilt.pop(key, None)
    charge(len(lhs)+m+1, phase='full_verification')
    if rebuilt != {key: q for key, q in target.items() if q}:
        raise ValueError('leaf restored full original equality mismatch')
    info.update(reduced_solution=list(map(str, remaining)), exact_support_weights=list(map(str, answer)),
                backsubstitution_values=recovered, status='full_original_equality_verified')
    # Reserves must dominate actual postprocessing, never just a native proxy.
    leaf_post = ledger.get('backsubstitution', 0)+ledger.get('full_verification', 0)
    if leaf_post > post_work or cells-pre_cells-comp['preprocessing_cells'] > post_cells:
        raise OverflowError('leaf postprocessing exceeded declared reserves')
    if info['total_work_proxy'] > max_work:
        raise OverflowError('leaf total charged reconstruction work cap')
    emit()
    return answer


def reconstruct_dual_fixed_support(columns, lhs, monomials, nonnegative_indices,
                                   relation_indices, saved_support, *, time_limit=180,
                                   max_rows=2500, max_variables=60000,
                                   max_cells=4000000, max_work=450000000,
                                   max_denominator=2**4096, max_coefficient_bits=4096,
                                   max_preprocessing_operations=200000000,
                                   max_preprocessing_cells=4000000,
                                   max_receipt_bytes=8388608, compilation_work_reserve=0,
                                   on_checkpoint=None):
    """Reconstruct the SAME dual support, restoring all leaf/slack weights."""
    start = time.monotonic()
    diagnostics = dict(method='saved support; exact singleton-column elimination; unchanged compressed native RREF',
                       native_call_interruptible=False)
    try:
        if type(time_limit) not in (int, float) or not math.isfinite(time_limit) or not 0 < time_limit <= 360:
            raise ValueError('positive cooperative time limit at most 360 seconds')
        if any(type(v) is not int or v < 1 for v in (max_rows,max_variables,max_cells,max_work,max_denominator,max_coefficient_bits,max_preprocessing_operations,max_preprocessing_cells,max_receipt_bytes)):
            raise ValueError('positive strict resource bounds')
        if max_work > 450000000 or type(compilation_work_reserve) is not int or compilation_work_reserve < 0:
            raise ValueError('authorized total work ceiling and nonnegative compilation reserve')
        if on_checkpoint is not None and not callable(on_checkpoint):
            raise ValueError('optional synchronous checkpoint callback')
        if type(columns) is not list or type(lhs) is not dict or type(monomials) is not list or len(set(monomials)) != len(monomials):
            raise ValueError('dual exact domain')
        ids = nonnegative_indices+relation_indices
        if any(type(i) is not int or not 0 <= i < len(columns) for i in ids) or len(set(ids)) != len(ids) or set(ids) != set(range(len(columns))):
            raise ValueError('complete unique dual classifications')
        if set(monomials) != set(lhs)|{m for p in columns for m in p}:
            raise ValueError('complete dual monomial domain')
        for p in columns+[lhs]:
            if type(p) is not dict or any(type(q) not in (int,F) for q in p.values()):
                raise ValueError('exact rational input only')
            if any(max(abs(F(q).numerator).bit_length(),F(q).denominator.bit_length()) > max_coefficient_bits for q in p.values()):
                raise OverflowError('original dual coefficient bits')
        selected = relation_indices+nonnegative_indices
        rows = len(selected)+1; M = len(monomials); variables = 2*M+len(nonnegative_indices)
        if rows > max_rows or variables > max_variables:
            raise OverflowError('dual equation dimensions')
        build = rows*variables
        verification = 3*sum(map(len,columns))+2*len(lhs)+variables+2*M+len(saved_support)+1
        reserve = compilation_work_reserve+build+verification
        if reserve >= max_work:
            raise OverflowError('dual construction/verification/compilation work reserve')
        eq = []
        for m in monomials:
            p = {j:F(columns[i].get(m,0)) for j,i in enumerate(selected) if columns[i].get(m,0)}
            if lhs.get(m,0):p[rows-1] = F(lhs[m])
            eq.append(p)
        eq.extend({r:-q for r,q in p.items()} for p in eq[:M])
        eq.extend({len(relation_indices)+j:F(-1)} for j in range(len(nonnegative_indices)))
        target = {rows-1:F(-1)}; deadline = start+time_limit
        def checkpoint(info):
            info.update(compilation_work_reserve=compilation_work_reserve,
                        dual_build_work_proxy=build,dual_verification_work_reserve=verification)
            if 'leaf_total_work_proxy' in info:
                info['total_work_proxy'] = info['leaf_total_work_proxy']+reserve
            if len(json.dumps(info,sort_keys=True,separators=(',',':'),allow_nan=False).encode()) > max_receipt_bytes:
                raise OverflowError('leaf dual checkpoint byte cap')
            if on_checkpoint is not None:
                on_checkpoint(info)
        try:
            answer = exact_support_solution(eq,target,saved_support,deadline=deadline,
                max_rows=max_rows,max_columns=max_variables,max_cells=max_cells,
                max_work=max_work-reserve,max_denominator=max_denominator,
                max_coefficient_bits=max_coefficient_bits,
                max_preprocessing_operations=max_preprocessing_operations,
                max_preprocessing_cells=max_preprocessing_cells,max_receipt_bytes=max_receipt_bytes,
                diagnostics=diagnostics,on_checkpoint=checkpoint if on_checkpoint is not None else None)
        finally:
            if 'leaf_elimination' in diagnostics:
                info = diagnostics['leaf_elimination']
                info.update(compilation_work_reserve=compilation_work_reserve,
                            dual_build_work_proxy=build,dual_verification_work_reserve=verification)
                if 'leaf_total_work_proxy' in info:
                    info['total_work_proxy'] = info['leaf_total_work_proxy']+reserve
        diagnostics.update(equation_rows=rows, variables=variables, support_size=len(saved_support),
                           elapsed_seconds=time.monotonic()-start)
        if answer is None or any(q < 0 for q in answer):
            return dict(status='uncertified',certified=False,
                        reason='same selected support has no admitted nonnegative exact reconstruction',
                        diagnostics=diagnostics, **FLAGS)
        full = [F(0)]*variables
        for i,q in zip(saved_support,answer):full[i] = q
        def checked(q):
            if max(abs(q.numerator).bit_length(),q.denominator.bit_length()) > max_coefficient_bits:
                raise OverflowError('full dual verification coefficient bits')
            if time.monotonic() > deadline:
                raise TimeoutError('full dual verification deadline')
            return q
        y = {m:checked(full[j]-full[j+M]) for j,m in enumerate(monomials)}
        def dot(p):
            total = F(0)
            for m,q in p.items():total = checked(total+checked(y[m]*F(q)))
            return total
        dots = list(map(dot,columns)); target_dot = dot(lhs)
        if target_dot != -1 or any(dots[i] < 0 for i in nonnegative_indices) or any(dots[i] != 0 for i in relation_indices):
            raise ValueError('restored original dual equality/sign mismatch')
        info = diagnostics['leaf_elimination']
        if info['total_work_proxy'] > max_work:
            raise OverflowError('total charged leaf dual reconstruction work cap')
        if len(json.dumps(info,sort_keys=True,separators=(',',':'),allow_nan=False).encode()) > max_receipt_bytes:
            raise OverflowError('leaf dual receipt byte cap')
        return dict(status='exact_separator',certified=True,monomials=monomials,
                    weights=[str(y[m]) for m in monomials],columns_dot_y=list(map(str,dots)),
                    lhs_dot_y=str(target_dot),exact_support_weights=list(map(str,answer)),
                    saved_support=list(saved_support),diagnostics=diagnostics,
                    scope='same declared finite support; no floating refit or arithmetic refutation',**FLAGS)
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:
        return dict(status='missing_resource',certified=False,reason=str(e),diagnostics=diagnostics,**FLAGS)
    except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError) as e:
        return dict(status='uncertified',certified=False,reason=str(e),diagnostics=diagnostics,**FLAGS)
