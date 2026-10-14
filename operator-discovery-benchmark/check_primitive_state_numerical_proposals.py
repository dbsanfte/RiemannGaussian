"""Independent exact audit of numerical proposal transformations.

Imports no numerical producer or solver. Verification here concerns only exact
row equivalence and complete coordinate transport, never exact admission of a
floating proposal or proof of infeasibility.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import time

FLAGS = dict(certified=False, global_bound_proved=False, RH_proved=False)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


class _Budget:
    def __init__(self, deadline, max_operations, max_cells, max_coefficient_bits):
        for n in (max_operations, max_cells, max_coefficient_bits):
            if type(n) is not int or n < 1:
                raise ValueError('positive strict audit limits')
        if deadline is not None and (type(deadline) not in (int, float) or not math.isfinite(deadline)):
            raise ValueError('finite absolute deadline')
        self.deadline = deadline
        self.max_operations = max_operations
        self.max_cells = max_cells
        self.bits = max_coefficient_bits
        self.operations = self.cells = 0

    def charge(self, operations=1, cells=0):
        self.operations += operations
        self.cells += cells
        if self.operations > self.max_operations or self.cells > self.max_cells:
            raise OverflowError('numerical transformation audit resource cap')
        if self.deadline is not None and time.monotonic() > self.deadline:
            raise TimeoutError('numerical transformation audit deadline')

    def rational(self, value, output=False):
        self.charge()
        if type(value) not in ((int, F, str) if output else (int, F)):
            raise ValueError('exact rational required')
        if type(value) is str and (len(value) > 4*self.bits+4 or any(c not in '0123456789+-/' for c in value)):
            raise ValueError('bounded rational text required')
        q = F(value)
        if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > self.bits:
            raise OverflowError('audit coefficient bit cap')
        return q


def _rows(rows, rhs, n_variables, budget):
    if type(n_variables) is not int or n_variables < 0:
        raise ValueError('complete variable dimension')
    if type(rows) is not list or type(rhs) is not list or len(rows) != len(rhs):
        raise ValueError('complete row and target arrays')
    result = []
    targets = []
    for row, target in zip(rows, rhs):
        budget.charge(cells=1)
        if type(row) is not dict:
            raise ValueError('sparse exact row required')
        clean = {}
        for index, value in row.items():
            if type(index) is not int or not 0 <= index < n_variables:
                raise ValueError('row coordinate outside complete variable domain')
            q = budget.rational(value)
            if q:
                clean[index] = q
                budget.charge(cells=1)
        result.append(clean)
        targets.append(budget.rational(target))
    return result, targets


def verify_complete_vector(vector, n_variables):
    """Every coordinate is explicit; a sparse map is never implicitly zero-filled."""
    if type(vector) is not list or len(vector) != n_variables:
        raise ValueError('complete explicit numerical coordinate vector required')
    if any(type(value) not in (int, float) or not math.isfinite(value) for value in vector):
        raise ValueError('finite numerical coordinates required')
    return dict(verified=True, coordinate_count=n_variables, exact_admission=False, **FLAGS)


def verify_domains(receipt, n_variables, variable_domains=None, psd_layout=None):
    if receipt.get('variable_mapping') != 'identity' or receipt.get('variables') != n_variables:
        raise ValueError('identity complete variable map required')
    if variable_domains is not None and receipt.get('variable_domains') != variable_domains:
        raise ValueError('signed/nonnegative variable domains altered')
    if psd_layout is not None and receipt.get('psd_layout') != psd_layout:
        raise ValueError('PSD matrix coordinate layout altered')
    return True


def verify_transformation(rows, rhs, n_variables, reduced_rows, reduced_rhs, receipt, *,
                          deadline=None, max_operations=200000000, max_cells=4000000,
                          max_coefficient_bits=4096, max_receipt_bytes=8388608,
                          max_audit_cells=12000000, max_audit_operations=600000000):
    """Audit every original augmented row and the deterministic first representatives."""
    budget = _Budget(deadline, max_audit_operations, max_audit_cells, max_coefficient_bits)
    if any(type(n) is not int or n < 1 for n in (max_operations, max_cells)):
        raise ValueError('positive strict source transformation limits')
    if type(max_receipt_bytes) is not int or max_receipt_bytes < 1:
        raise ValueError('positive receipt byte cap')
    if type(receipt) is not dict or len(json.dumps(receipt, allow_nan=False).encode()) > max_receipt_bytes:
        raise ValueError('bounded transformation receipt required')
    declared_limits = receipt.get('limits')
    if type(declared_limits) is not dict or set(declared_limits) != {'max_operations', 'max_cells', 'max_coefficient_bits'} or any(type(q) is not int or q < 1 for q in declared_limits.values()):
        raise ValueError('strict recorded transformation limits')
    budget.bits = min(budget.bits, declared_limits['max_coefficient_bits'])
    original, targets = _rows(rows, rhs, n_variables, budget)
    reduced, reduced_targets = _rows(reduced_rows, reduced_rhs, n_variables, budget)
    expected_hash = digest(dict(rows=[[[j, str(q)] for j, q in sorted(row.items())] for row in rows],
                                rhs=list(map(str, rhs)), variables=n_variables))
    if receipt.get('schema') != 'primitive-state-exact-row-compression-v1' or receipt.get('original_hash') != expected_hash:
        raise ValueError('source system hash/schema mismatch')
    if type(receipt.get('original_rows')) is not int or receipt['original_rows'] != len(rows) or type(receipt.get('variables')) is not int or receipt['variables'] != n_variables:
        raise ValueError('complete source dimensions mismatch')
    if receipt.get('variable_mapping') != 'identity':
        raise ValueError('signed and PSD coordinates require identity mapping')
    seen = {}
    retained = []
    reps = []
    ratios = []
    scales = []
    inconsistent = []
    producer_operations = producer_cells = 0
    for i, (row, target) in enumerate(zip(original, targets)):
        budget.charge()
        producer_operations += 1+len(rows[i])
        producer_cells += 1+len(rows[i])
        if not row and target:
            inconsistent.append(i)
        if not row and not target:
            reps.append(None)
            ratios.append(F(0))
            continue
        pivot = row[min(row)] if row else target
        signature = tuple((j, budget.rational(q/pivot)) for j, q in sorted(row.items())) + ((n_variables, budget.rational(target/pivot)),)
        budget.charge(cells=len(signature))
        producer_operations += len(row)+1
        if signature not in seen:
            seen[signature] = (len(retained), pivot)
            retained.append(i)
            scales.append(max([abs(target)]+[abs(q) for q in row.values()]))
        k, first_pivot = seen[signature]
        reps.append(k)
        ratios.append(budget.rational(pivot/first_pivot))
    for key, expected in (('retained_indices', retained), ('row_representative', reps), ('inconsistent_zero_rows', inconsistent)):
        actual = receipt.get(key)
        if type(actual) is not list or actual != expected or any(type(v) is not int for v in actual if v is not None):
            raise ValueError('complete deterministic '+key+' mismatch')
    for key, expected in (('row_multiplier', ratios), ('row_scales', scales)):
        actual = receipt.get(key)
        if type(actual) is not list or len(actual) != len(expected) or [budget.rational(q, output=True) for q in actual] != expected:
            raise ValueError('exact '+key+' mismatch')
    if reduced != [original[i] for i in retained] or reduced_targets != [targets[i] for i in retained]:
        raise ValueError('retained complete matrix/target mismatch')
    limits = receipt.get('limits')
    if type(limits) is not dict or set(limits) != {'max_operations', 'max_cells', 'max_coefficient_bits'} or any(type(q) is not int or q < 1 for q in limits.values()):
        raise ValueError('strict recorded transformation limits')
    if any(limits[k] > bound for k, bound in (('max_operations', max_operations), ('max_cells', max_cells), ('max_coefficient_bits', max_coefficient_bits))):
        raise ValueError('recorded transformation exceeds authorized limits')
    if type(receipt.get('operations')) is not int or receipt['operations'] != producer_operations or producer_operations > limits['max_operations']:
        raise ValueError('transformation operations receipt mismatch')
    if type(receipt.get('cells')) is not int or receipt['cells'] != producer_cells or producer_cells > limits['max_cells']:
        raise ValueError('transformation cells receipt mismatch')
    source_cells = sum(len(row)+1 for row in rows)
    retained_cells = sum(len(row)+1 for row in reduced_rows)
    # Conservative transparent charged proxy: source assembly, producer exact
    # preprocessing, sparse scaling/assembly, source hash, independent replay.
    reserve = 4*source_cells+n_variables+producer_operations+4*retained_cells+2*source_cells+budget.operations+1
    return dict(verified=True, original_rows=len(rows), reduced_rows=len(retained), variables=n_variables,
                numerical_assembly_work_reserve=reserve,
                numerical_assembly_work_components=dict(source_assembly=4*source_cells+n_variables,
                    exact_compression=producer_operations,scaled_sparse_assembly=4*retained_cells,
                    source_hash=2*source_cells,independent_replay=budget.operations,overhead=1),
                signed_and_PSD_coordinates_preserved=True, exact_admission=False,
                audit_operations=budget.operations, audit_cells=budget.cells, **FLAGS)


def verify_proposal_diagnostics(diagnostics, proposal, n_variables, *, proposal_kind='primal', expected_source_hashes=None):
    """Audit proposal completeness/status without treating floating values as a proof."""
    if type(diagnostics) is not dict or proposal_kind not in ('primal', 'dual'):
        raise ValueError('numerical proposal diagnostics schema')
    for key in ('certified', 'global_bound_proved', 'RH_proved', 'exact_admission', 'optimality_claim', 'infeasibility_proved'):
        if key in diagnostics and diagnostics[key] is not False:
            raise ValueError('numerical proposal cannot claim exact admission/proof')
    if expected_source_hashes is not None and diagnostics.get('source_hashes') != expected_source_hashes:
        raise ValueError('complete source hashes mismatch')
    attempts = diagnostics.get('attempts')
    if type(attempts) is not list or any(type(a) is not dict or not isinstance(a.get('solver'), str) for a in attempts):
        raise ValueError('explicit solver attempt diagnostics required')
    if proposal is None:
        has_reason = any(isinstance(diagnostics.get(k), str) and diagnostics[k] for k in ('reason', 'solver_message', 'solver_error'))
        has_attempt_status = any(a.get('status') is not None or any(isinstance(a.get(k), str) and a[k] for k in ('error', 'message')) for a in attempts)
        if not has_reason and not has_attempt_status:
            raise ValueError('missing explicit no-vector diagnostic')
    elif proposal_kind == 'primal':
        verify_complete_vector(proposal, n_variables)
        if diagnostics.get('solver_error') or diagnostics.get('sdp_status') not in ('optimal', 'optimal_inaccurate'):
            raise ValueError('failed solver vector is not an accepted proposal')
    else:
        if type(proposal) is not list or any(type(j) is not int or not 0 <= j < n_variables for j in proposal) or len(set(proposal)) != len(proposal):
            raise ValueError('unique bounded support coordinates required')
        if diagnostics.get('solver_status') != 0 or diagnostics.get('support') != proposal:
            raise ValueError('support and successful numerical status required')
    if 'unaccepted_vector' in diagnostics:
        verify_complete_vector(diagnostics['unaccepted_vector'], n_variables)
    return dict(verified=True, proposal_present=proposal is not None, exact_admission=False, **FLAGS)


def rebuild_primal_system(columns, lhs, monomials, shape, offset, specs):
    """Rebuild the complete scalar and upper-triangle coordinates independently."""
    _complete_domain(columns, lhs, monomials)
    if type(shape) not in (list, tuple) or len(shape) != 2 or any(type(n) is not int or n < 0 for n in shape):
        raise ValueError('complete scalar signed layout')
    if type(offset) is not int or shape[0]+2*shape[1] > offset or offset > len(columns):
        raise ValueError('complete scalar block offset')
    if type(specs) is not dict or any(type(n) is not int or n < 1 for n in specs.values()):
        raise ValueError('complete PSD specifications')
    if offset+sum(n*(n+1)//2 for n in specs.values()) != len(columns):
        raise ValueError('PSD coordinates must include every upper-triangle entry')
    positions = {m:i for i,m in enumerate(monomials)}
    rows = [{} for _ in monomials]
    for j, column in enumerate(columns):
        for m,q in column.items():
            rows[positions[m]][j] = q
    layout=[]
    j=offset
    for name,n in specs.items():
        for a in range(n):
            for b in range(a,n):
                layout.append((name,a,b,j))
                j+=1
    return rows,[lhs.get(m,F(0)) for m in monomials],len(columns),layout


def _complete_domain(columns, lhs, monomials):
    if type(columns) is not list or any(type(p) is not dict for p in columns) or type(lhs) is not dict or type(monomials) is not list:
        raise ValueError('complete source columns/target/domain required')
    if len(set(monomials)) != len(monomials) or set(monomials) != set(lhs)|{m for p in columns for m in p}:
        raise ValueError('complete unique monomial domain required')


def rebuild_dual_system(columns, lhs, monomials, nonnegative, relations):
    """Rebuild y+, y- and explicit nonnegative slack coordinates independently."""
    _complete_domain(columns,lhs,monomials)
    if type(nonnegative) is not list or type(relations) is not list:
        raise ValueError('complete scalar classifications')
    indices=relations+nonnegative
    if any(type(j) is not int or not 0 <= j < len(columns) for j in indices) or len(set(indices)) != len(indices) or set(indices) != set(range(len(columns))):
        raise ValueError('every source column classified exactly once')
    width=len(monomials)
    positions={m:j for j,m in enumerate(monomials)}
    rows=[]
    for index in indices:
        row={}
        for m,q in columns[index].items():
            j=positions[m]
            row[j]=q
            row[width+j]=-q
        rows.append(row)
    for k in range(len(nonnegative)):
        rows[len(relations)+k][2*width+k]=F(-1)
    row={}
    for m,q in lhs.items():
        j=positions[m]
        row[j]=q
        row[width+j]=-q
    rows.append(row)
    return rows,[F(0)]*len(indices)+[F(-1)],2*width+len(nonnegative)


def verify_system_proposal(kind, columns, lhs, monomials, diagnostics, proposal, *,
                           shape=None, offset=None, specs=None, nonnegative=None, relations=None,
                           deadline=None, max_operations=200000000, max_cells=4000000,
                           max_coefficient_bits=4096):
    """Rebuild a complete original system and audit its numerical transformation."""
    if kind == 'primal':
        rows,rhs,n,layout = rebuild_primal_system(columns,lhs,monomials,shape,offset,specs)
        if diagnostics.get('numerical_threads') != 1:
            raise ValueError('single numerical SDP thread')
    elif kind == 'dual':
        rows,rhs,n = rebuild_dual_system(columns,lhs,monomials,nonnegative,relations)
        if diagnostics.get('threads') != 1 or diagnostics.get('parallel') is not False:
            raise ValueError('single numerical LP thread')
    else:
        raise ValueError('known numerical proposal kind')
    receipt = diagnostics.get('transformation_receipt')
    if type(receipt) is not dict:
        raise ValueError('complete exact numerical transformation receipt')
    retained = receipt.get('retained_indices')
    if type(retained) is not list or any(type(i) is not int or not 0 <= i < len(rows) for i in retained):
        raise ValueError('retained row indices in complete domain')
    checked = verify_transformation(rows,rhs,n,[rows[i] for i in retained],[rhs[i] for i in retained],receipt,
        deadline=deadline,max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits)
    checked['proposal_diagnostics'] = verify_proposal_diagnostics(diagnostics,proposal,n,proposal_kind=kind)
    if kind == 'primal' and proposal is not None:
        support = [i for i in range(offset) if proposal[i] > 1e-7]+list(range(offset,n))
        if diagnostics.get('support') != support:
            raise ValueError('complete original SDP active support')
    return checked
