"""Independent bounded numerical trace audit; no producer or solver imports.

All computed floating metrics use Python binary64 conversions and math.fsum.
They are diagnostic approximations, never exact feasibility or infeasibility.
"""
import hashlib
import json
import math
import time
from fractions import Fraction
import check_primitive_state_numerical_proposals as independent

FLAGS = dict(certified=False, exact_admission=False, infeasibility_proved=False,
             global_bound_proved=False, RH_proved=False)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def _finite(value):
    if type(value) not in (int, float) or not math.isfinite(value):
        raise ValueError('finite explicit numerical coordinate required')
    return float(value)


def _sparse(encoded, width):
    rows = []
    for row in encoded:
        if type(row) is not list:
            raise ValueError('explicit sparse row required')
        decoded = {}
        for pair in row:
            if type(pair) is not list or len(pair) != 2:
                raise ValueError('coordinate coefficient pair required')
            j, q = pair
            if type(j) is not int or not 0 <= j < width or j in decoded:
                raise ValueError('unique bounded row coordinate required')
            if type(q) is not str or len(q) > 16388:
                raise ValueError('bounded exact coefficient text required')
            decoded[j] = Fraction(q)
        rows.append(decoded)
    return rows


def verify_trace(trace, *, expected_source_hashes=None, expected_solver=None,
                 expected_options=None, rows=None, rhs=None, n_variables=None,
                 deadline=None, max_trace_bytes=8388608, max_metric_cells=100000000,
                 max_log_bytes=1048576):
    """Bind a trace to trusted original equations and recompute explicit-vector metrics."""
    if type(trace) is not dict:
        raise ValueError('trace dictionary required')
    raw = json.dumps(trace, allow_nan=False).encode()
    if len(raw) > max_trace_bytes:
        raise OverflowError('trace byte cap')
    if trace.get('schema') != 'primitive-state-solver-trace-v1':
        raise ValueError('trace schema')
    if trace.get('kind') not in ('support','primal'):
        raise ValueError('explicit known trace kind')
    for record in (trace, trace.get('diagnostics', {})):
        if type(record) is not dict:
            raise ValueError('explicit trace diagnostic dictionary required')
        for key in FLAGS:
            if key in record and record[key] is not False:
                raise ValueError('numerical trace cannot certify a theorem')
    for key, expected in [('source_hashes', expected_source_hashes)]:
        if expected is not None and trace.get(key) != expected:
            raise ValueError(key+' binding mismatch')
    role = trace.get('vector_role')
    if role not in ('raw_failed_last_iterate', 'accepted_proposal', 'unavailable'):
        raise ValueError('explicit vector acceptance role required')
    if (trace.get('original_vector') is None) != (role == 'unavailable'):
        raise ValueError('vector availability and role mismatch')
    solver = trace.get('solver')
    if type(solver) is not dict or not isinstance(solver.get('name'), str) or not solver['name'] or type(solver.get('versions')) is not dict or not solver['versions']:
        raise ValueError('solver name/version binding required')
    if type(solver.get('options')) is not dict or solver.get('options_hash') != digest(solver['options']):
        raise ValueError('solver options hash binding required')
    if solver.get('versions_hash') != digest(solver['versions']):
        raise ValueError('solver version hash binding required')
    if expected_solver is not None and solver != expected_solver:
        raise ValueError('solver binding mismatch')
    if expected_options is not None and solver['options'] != expected_options:
        raise ValueError('options binding mismatch')
    if trace.get('kind') == 'support' and (solver['options'].get('threads') != 1 or solver['options'].get('parallel') is not False):
        raise ValueError('single-thread support options required')
    if trace.get('kind') == 'primal' and solver['options'].get('max_threads') != 1:
        raise ValueError('single-thread primal options required')
    if 'error' not in trace:
        native_status = trace.get('raw_result', trace.get('raw_solution', {})).get('status')
        if native_status is not None and native_status != trace.get('termination_status'):
            raise ValueError('native result and termination status mismatch')
    if 'termination_status' not in trace and 'error' not in trace:
        raise ValueError('termination status or explicit exception required')
    if role == 'accepted_proposal' and trace.get('termination_status') not in (0, 'optimal', 'optimal_inaccurate', 'Solved', 'AlmostSolved'):
        raise ValueError('failed last iterate cannot be an accepted proposal')
    log = trace.get('retained_log')
    if type(log) is dict and log.get('text') is None and isinstance(log.get('path'), str):
        with open(log['path'], 'rb') as stream:
            logbytes = stream.read(max_log_bytes+1)
    elif type(log) is dict and type(log.get('text')) is str:
        logbytes = log['text'].encode('utf-8')
    else:
        raise ValueError('retained log bytes unavailable')
    if type(log) is not dict or log.get('encoding') != 'utf-8':
        raise ValueError('explicit retained native log required')
    if len(logbytes)>max_log_bytes or type(log.get('retained_bytes')) is not int or log['retained_bytes'] != len(logbytes):
        raise ValueError('retained native log byte count/cap')
    if type(log.get('total_bytes')) is not int or log['total_bytes'] < len(logbytes) or type(log.get('truncated')) is not bool or log['truncated'] != (log['total_bytes'] > len(logbytes)):
        raise ValueError('native log truncation semantics')
    if log.get('sha256') != hashlib.sha256(logbytes).hexdigest():
        raise ValueError('retained native log hash')
    system = trace.get('original_system')
    if system is None and type(trace.get('original_system_metadata')) is dict and rows is not None and rhs is not None:
        system = dict(trace['original_system_metadata'])
        if system.pop('rows_count', None) != len(rows):
            raise ValueError('complete original row count mismatch')
        system.update(rows=[[[j,str(q)] for j,q in sorted(row.items())] for row in rows],rhs=list(map(str,rhs)))
    if type(system) is not dict or type(system.get('variables')) is not int or system['variables'] < 0:
        raise ValueError('complete original system required')
    width = system['variables']
    encoded_rows = system.get('rows')
    encoded_rhs = system.get('rhs')
    if type(encoded_rows) is not list or type(encoded_rhs) is not list or len(encoded_rows) != len(encoded_rhs):
        raise ValueError('complete original equations required')
    source_cells = sum(len(row)+1 for row in encoded_rows)
    if source_cells > max_metric_cells:
        raise OverflowError('original metric cell cap')
    actual_rows = _sparse(encoded_rows, width)
    if any(type(q) is not str or len(q)>16388 for q in encoded_rhs):
        raise ValueError('bounded exact target coefficient text required')
    actual_rhs = [Fraction(q) for q in encoded_rhs]
    if rows is None or rhs is None or n_variables is None:
        raise ValueError('trusted original system required; trace cannot trust itself')
    if actual_rows != rows or actual_rhs != rhs or width != n_variables:
        raise ValueError('trusted complete original system mismatch')
    if trace.get('original_system_hash') != digest(system):
        raise ValueError('original system hash mismatch')
    receipt = trace.get('transformation_receipt')
    if type(receipt) is not dict:
        raise ValueError('exact transformation receipt required')
    retained = receipt.get('retained_indices')
    if type(retained) is not list or any(type(i) is not int or not 0 <= i < len(rows) for i in retained):
        raise ValueError('retained original rows required')
    replay = independent.verify_transformation(rows, rhs, width,
        [rows[i] for i in retained], [rhs[i] for i in retained], receipt, deadline=deadline,
        max_operations=450000000 if trace['kind']=='support' else 200000000)
    scaled_rows = [{j: float(q/Fraction(scale)) for j,q in rows[i].items()} for i,scale in zip(retained,receipt['row_scales'])]
    scaled_rhs = [float(rhs[i]/Fraction(scale)) for i,scale in zip(retained,receipt['row_scales'])]
    expected_scaled = dict(rows=[[[j,q] for j,q in sorted(row.items())] for row in scaled_rows],rhs=scaled_rhs,variables=width,objective=system['objective'])
    if trace.get('scaled_original_system_hash') != digest(expected_scaled):
        raise ValueError('reconstructed scaled original system hash mismatch')
    if trace.get('kind') == 'support' and trace.get('solver_system_hash') != digest(expected_scaled):
        raise ValueError('support solver system hash mismatch')
    vector = trace.get('original_vector')
    metrics = None
    retained_cells = sum(len(row)+1 for row in scaled_rows)
    # Charged cumulative proxy includes parsing/rebuild/hash, coefficient
    # conversion, residual multiplication/sums, and summary traversals.
    metric_cells = 8*source_cells + 8*retained_cells + 3*width
    if metric_cells > max_metric_cells:
        raise OverflowError('cumulative metric cell cap')
    if vector is not None:
        independent.verify_complete_vector(vector,width)
        vector = list(map(_finite,vector))
        residuals = [math.fsum([float(q)*vector[j] for j,q in row.items()]+[-float(b)]) for row,b in zip(rows,rhs)]
        scaled_residuals = [math.fsum([q*vector[j] for j,q in row.items()]+[-b]) for row,b in zip(scaled_rows,scaled_rhs)]
        if any(not math.isfinite(v) for v in residuals+scaled_residuals):
            raise ValueError('nonfinite recomputed residual')
        indices = system.get('nonnegative_indices')
        if type(indices) is not list or len(set(indices)) != len(indices) or any(type(j) is not int or not 0 <= j < width for j in indices):
            raise ValueError('explicit scalar sign domain required')
        psd = []
        used = set()
        for block in system.get('psd_blocks',[]):
            size = block.get('size'); coords = block.get('indices')
            if type(size) is not int or size < 1 or type(coords) is not list or len(coords) != size*(size+1)//2:
                raise ValueError('complete PSD upper triangle required')
            if any(type(j) is not int or not 0 <= j < width or j in used for j in coords) or len(set(coords)) != len(coords):
                raise ValueError('unique complete PSD coordinates required')
            used.update(coords)
            metric_cells += size*size
            if metric_cells > max_metric_cells:
                raise OverflowError('PSD metric cell cap')
            diagonals=[0.0]*size; radii=[[] for _ in range(size)]; k=0
            for a in range(size):
                for b in range(a,size):
                    value=vector[coords[k]]; k+=1
                    if a==b: diagonals[a]=value
                    else: radii[a].append(abs(value)); radii[b].append(abs(value))
            psd.append(dict(name=block['name'], gershgorin_lower=min(d-math.fsum(r) for d,r in zip(diagonals,radii)), minimum_diagonal=min(diagonals)))
        metrics=dict(equality_max_abs=max(map(abs,residuals),default=0.0), scaled_equality_max_abs=max(map(abs,scaled_residuals),default=0.0), nonnegative_min=min((vector[j] for j in indices),default=None), psd_gershgorin=psd)
    nonzero = [abs(q) for row in scaled_rows for q in row.values() if q] + [abs(q) for q in scaled_rhs if q] + [abs(_finite(q)) for q in system['objective'] if q]
    coefficients = dict(nonzero_count=len(nonzero),min_nonzero=min(nonzero,default=None),max_abs=max(nonzero,default=None),dynamic_range=(max(nonzero)/min(nonzero) if nonzero else None))
    if trace.get('coefficient_metrics') is not None and trace['coefficient_metrics'] != coefficients:
        raise ValueError('scaled coefficient magnitude summary mismatch')
    if deadline is not None and time.monotonic()>deadline:
        raise TimeoutError('trace audit deadline')
    return dict(verified=True, diagnostics=metrics, coefficient_metrics=coefficients, canonical_system_independently_rebuilt=(trace.get('kind') == 'support'), transformation=replay, trace_bytes=len(raw), metric_cells=metric_cells, rounding='binary64 coefficient conversion/products; math.fsum sums; approximate, no certified error enclosure', **FLAGS)


def verify_system_trace(kind, columns, lhs, monomials, trace, *, shape=None, offset=None,
                        specs=None, nonnegative=None, relations=None, **kwargs):
    if trace.get('kind') != ('support' if kind in ('dual','support') else 'primal'):
        raise ValueError('trace kind matches trusted system')
    if kind == 'primal':
        rows,rhs,width,_ = independent.rebuild_primal_system(columns,lhs,monomials,shape,offset,specs)
    elif kind in ('dual','support'):
        rows,rhs,width = independent.rebuild_dual_system(columns,lhs,monomials,nonnegative,relations)
    else:
        raise ValueError('known original system kind required')
    system = trace.get('original_system', trace.get('original_system_metadata', {}))
    if kind == 'primal':
        expected_signs = list(range(offset))
        blocks=[]; start=offset
        for name,size in specs.items():
            count=size*(size+1)//2
            blocks.append(dict(name=name,size=size,indices=list(range(start,start+count))))
            start+=count
    else:
        expected_signs=list(range(width)); blocks=[]
    if system.get('nonnegative_indices') != expected_signs or system.get('psd_blocks') != blocks:
        raise ValueError('trusted scalar/PSD layout mismatch')
    return verify_trace(trace,rows=rows,rhs=rhs,n_variables=width,**kwargs)
