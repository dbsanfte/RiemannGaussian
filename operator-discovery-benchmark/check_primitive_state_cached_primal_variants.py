"""Independent bounded full-source cache and fixed native variant audits.

No producer, numerical solver, or numerical array library imports. Cached
coordinates remain the FULL original optimization variables and cones.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import check_primitive_state_basis_primal as CORE
import check_primitive_state_numerical_proposals as EXACT

FLAGS=dict(CORE.FLAGS)
require=CORE.require
digest=CORE.digest
CACHE_BYTES=134217728


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


def floathex(value):
    require(type(value)is str and len(value)<=32,'bounded explicit canonical floathex')
    x=float.fromhex(value);require(math.isfinite(x) and x.hex()==value,'canonical finite binary64 hex coefficient')
    return x


def decode_original(cache,budget):
    original=cache.get('original');require(type(original)is dict,'complete original cache source')
    domain=original.get('monomials');columns=original.get('columns');rhs=original.get('rhs')
    require(type(domain)is list and 0<len(domain)<=100000 and all(type(m)is list and len(m)<=64 and all(type(j)is int and 0<=j and j.bit_length()<=63 for j in m) for m in domain),'complete original integer-tuple monomial domain')
    monomials=[tuple(m) for m in domain];require(len(set(monomials))==len(monomials),'unique cached monomial domain')
    require(type(columns)is list and 0<len(columns)<=2048 and type(rhs)is list and len(rhs)==len(domain),'complete cached source and explicit RHS coordinates')
    source_cells=sum(len(column) for column in columns if type(column)is list)+len(rhs)
    require(source_cells<=4000000,'bounded complete cached source cells');budget.charge(source_cells+sum(map(len,domain)),cells=source_cells+len(domain))
    def rational(text):
        q=budget.rational(text,output=True);require(str(q)==text,'canonical explicit exact rational source')
        return q
    decoded=[]
    for column in columns:
        require(type(column)is list,'explicit cached original column');result={};previous=-1
        for pair in column:
            require(type(pair)is list and len(pair)==2 and type(pair[0])is int and previous<pair[0]<len(domain),'sorted unique original monomial position')
            previous=pair[0];result[monomials[previous]]=rational(pair[1])
        decoded.append(result)
    target={}
    for m,text in zip(monomials,rhs):
        q=rational(text)
        if q:target[m]=q
    specs=original.get('specs');require(type(specs)is list and all(type(p)is list and len(p)==2 and type(p[0])is str and type(p[1])is int for p in specs),'explicit named original PSD block sizes')
    require([p[0] for p in specs]==sorted(set(p[0] for p in specs)),'sorted unique original PSD blocks')
    return dict(columns=decoded,lhs=target,monomials=monomials,shape=original.get('shape'),offset=original.get('offset'),specs=dict(specs),selected_indices=original.get('selected_original_indices'),source_cells=source_cells)


def verify_csc(canonical,rebuilt,budget):
    expected=rebuilt['canonical_system'];n=expected['variables'];m=len(expected['rows'])
    require(type(canonical)is dict and canonical.get('format')=='csc-floathex-v1' and canonical.get('shape')==[m,n],'complete canonical CSC format and shape')
    for key in ('shape',):require(all(type(i)is int for i in canonical[key]),'strict canonical dimensions')
    indptr=canonical.get('indptr');indices=canonical.get('indices');values=canonical.get('values')
    require(type(indptr)is list and len(indptr)==n+1 and all(type(i)is int for i in indptr) and indptr[0]==0 and all(a<=b for a,b in zip(indptr,indptr[1:])),'complete monotone CSC column pointers')
    require(type(indices)is list and type(values)is list and indptr[-1]==len(indices)==len(values),'complete explicit CSC entries')
    require(len(indices)<=4000000,'canonical CSC cell cap')
    actual=[{} for _ in range(m)];budget.charge(3*len(indices)+len(indptr)+m,cells=len(indices)+m)
    for j in range(n):
        previous=-1
        for k in range(indptr[j],indptr[j+1]):
            i=indices[k];require(type(i)is int and previous<i<m,'sorted unique finite CSC row positions');previous=i
            x=floathex(values[k]);require(x!=0,'no explicit zero canonical CSC entries');actual[i][j]=values[k]
    require([[[j,q] for j,q in sorted(row.items())] for row in actual]==expected['rows'],'independently rebuilt full native matrix CSC')
    for key,expected_key in [('rhs','rhs'),('objective','objective')]:
        require(type(canonical.get(key))is list and all(floathex(q) is not None for q in canonical[key]) and canonical[key]==expected[expected_key],'complete independently rebuilt canonical '+key)
    require(canonical.get('P')=='zero' and canonical.get('cones')==expected['cones'],'zero quadratic objective and unchanged full cones')
    budget.charge(sum(len(row)*max(1,len(row).bit_length()) for row in actual)+len(canonical['rhs'])+len(canonical['objective']),cells=len(canonical['rhs'])+len(canonical['objective']))


def _verify_cache(cache,*,expected_parent_assembly=None,expected_source_hashes=None,expected_parent_bindings=None,deadline=None,max_operations=450000000,max_cells=60000000,max_coefficient_bits=4096,max_cache_bytes=CACHE_BYTES):
    CORE.scope(cache);require(cache.get('schema')=='primitive-state-cached-primal-v1','full cached primal schema')
    raw=encoded(cache);require(len(raw)<=max_cache_bytes,'bounded full source cache bytes')
    budget=EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits);budget.charge(2*(len(raw)//64+1),cells=len(raw)//64+1)
    decoded=decode_original(cache,budget)
    rebuilt=CORE.reconstruct(decoded['columns'],decoded['lhs'],decoded['monomials'],decoded['shape'],decoded['offset'],decoded['specs'],decoded['selected_indices'],deadline=deadline,max_operations=max_operations-budget.operations,max_cells=max_cells-budget.cells,max_coefficient_bits=max_coefficient_bits)
    budget.charge(rebuilt['audit_operations'],cells=rebuilt['audit_cells']);assembly=cache.get('assembly');require(type(assembly)is dict,'complete cached assembly receipt')
    for k,v in rebuilt['receipt'].items():require(assembly.get(k)==v,'independently rebuilt cached assembly '+k)
    require(assembly.get('limits')==dict(max_operations=50000000,max_cells=4000000,max_coefficient_bits=4096),'unchanged native assembly allowance')
    verify_csc(cache.get('canonical'),rebuilt,budget)
    for key,value in [('original_source_hash',cache['original']),('canonical_cache_hash',cache['canonical']),('assembly_hash',assembly)]:
        payload=encoded(value);budget.charge(2*(len(payload)//64+1),cells=len(payload)//64+1);require(cache.get(key)==hashlib.sha256(payload).hexdigest(),'complete cache component hash '+key)
    if expected_parent_assembly is not None:require(assembly==expected_parent_assembly,'completed parent original/canonical assembly binding')
    if expected_source_hashes is not None:require(cache.get('source_hashes')==expected_source_hashes,'immutable cache producer source closure')
    if expected_parent_bindings is not None:require(cache.get('parent_bindings')==expected_parent_bindings,'completed parent fresh basis and native audit bindings')
    result=dict(verified=True,canonical_system_independently_rebuilt=True,full_original_rows=len(decoded['monomials']),full_original_variables=len(decoded['columns']),selected_rows=len(decoded['selected_indices']),
        original_system_hash=assembly['original_system_hash'],canonical_system_hash=assembly['canonical_system_hash'],canonical_cache_hash=cache['canonical_cache_hash'],original_source_hash=cache['original_source_hash'],assembly_hash=cache['assembly_hash'],
        cache_bytes=len(raw),cache_compact_sha256=hashlib.sha256(raw).hexdigest(),audit_operations=budget.operations,audit_cells=budget.cells,
        independent_audit_work_reserve=budget.operations+len(raw)+decoded['source_cells']+1,mathematical_feasibility='UNKNOWN',**FLAGS)
    decoded['_rebuilt']=rebuilt
    return decoded,result


def verify_cache(cache,**kwargs):return _verify_cache(cache,**kwargs)[1]


VARIANT_OPTIONS={'qdldl_default':{'direct_solve_method':'qdldl'},'faer_static_1e-6':{'direct_solve_method':'faer','static_regularization_constant':1e-6}}


class VerifiedCache:
    """Private in-process proof material, never accepted as a JSON receipt."""
    def __init__(self,cache,decoded,check):self.cache=cache;self.decoded=decoded;self.check=check


def prepare_verified_cache(cache,**kwargs):
    decoded,check=_verify_cache(cache,**kwargs)
    return VerifiedCache(cache,decoded,check)


def _verify_native(trace,witness,variant,*,expected_source_hashes=None,expected_options=None,expected_versions=None,expected_cache_file_hash=None,deadline=None,max_operations=450000000,max_cells=60000000,max_coefficient_bits=4096,max_trace_bytes=8388608,max_log_bytes=1048576):
    require(type(witness)is VerifiedCache,'independently constructed in-process cache witness')
    cache=witness.cache;decoded=witness.decoded;rebuilt=decoded['_rebuilt'];CORE.scope(trace)
    raw=encoded(trace);require(len(raw)<=max_trace_bytes,'bounded complete native trace')
    budget=EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits);budget.charge(2*(len(raw)//64+1),cells=len(raw)//64+1)
    require(trace.get('schema')=='primitive-state-basis-primal-v1' and trace.get('variant')==variant and variant in VARIANT_OPTIONS,'fixed original-coordinate numerical variant')
    require(trace.get('assembly')==cache['assembly'],'same complete independently verified native matrix/layout')
    binding=trace.get('cache_binding');require(type(binding)is dict,'explicit native cache binding')
    for key in ('original_source_hash','canonical_cache_hash','assembly_hash'):require(binding.get(key)==cache[key],'native cache component '+key)
    require(binding.get('cache_file_hash')==(expected_cache_file_hash or witness.check['cache_compact_sha256']),'complete actual cache file hash')
    require(trace.get('source_hashes')==(expected_source_hashes or cache['source_hashes']),'immutable native/cache producer source closure')
    solver=trace.get('solver');require(type(solver)is dict and solver.get('name')=='clarabel-native','direct original-coordinate native solver')
    options=solver.get('options');versions=solver.get('versions')
    require(type(options)is dict and type(options.get('max_threads'))is int and options['max_threads']==1 and type(options.get('time_limit'))in (int,float) and math.isfinite(options['time_limit']) and 0<=options['time_limit']<=900,'bounded single-thread native options')
    require(type(versions)is dict and versions and solver.get('options_hash')==digest(options) and solver.get('versions_hash')==digest(versions),'complete native option/version hashes')
    for key,value in VARIANT_OPTIONS[variant].items():require(options.get(key)==value and type(options.get(key))is type(value),'predeclared native variant option '+key)
    if expected_options is not None:require(options==expected_options,'all frozen variant options')
    if expected_versions is not None:require(versions==expected_versions,'frozen native library versions')
    require('termination_status' in trace,'explicit native solver termination')
    native=trace.get('raw_solution');x=trace.get('original_vector');n=len(decoded['columns'])
    require(type(native)is dict or native is None,'explicit native solution/unavailability')
    if native is not None:
        for key in ('s','z'):
            if key in native:require(type(native[key])is list and len(native[key])==cache['assembly']['canonical_rows'] and all(v is None or type(v)in (int,float) and math.isfinite(v) for v in native[key]),'complete raw canonical '+key)
    if x is not None:
        require(type(x)is list and len(x)==n and type(native)is dict and type(native.get('x'))is list and len(native['x'])==n and all(CORE.finite(a).hex()==CORE.finite(b).hex() for a,b in zip(x,native['x'])),'complete native x without clipping or missing coordinates')
        require(native.get('status')==trace['termination_status'] and trace.get('vector_role')==('raw_native_solution' if trace['termination_status']in ('Solved','AlmostSolved') else 'raw_failed_last_iterate'),'diagnostic native status/role binding')
    else:
        require(trace.get('vector_role')=='unavailable','explicit unavailable native vector')
        if native is not None and type(native.get('x'))is list and len(native['x'])==n and all(type(v)in (int,float) and math.isfinite(v) for v in native['x']):raise ValueError('finite full raw native x cannot be dropped')
    log=trace.get('retained_log');require(type(log)is dict and type(log.get('text'))is str and log.get('encoding')=='utf-8','complete retained native log')
    rawlog=log['text'].encode();require(len(rawlog)<=max_log_bytes and type(log.get('retained_bytes'))is int and log['retained_bytes']==len(rawlog),'retained native log count/cap')
    require(type(log.get('total_bytes'))is int and log['total_bytes']>=len(rawlog) and type(log.get('truncated'))is bool and log['truncated']==(log['total_bytes']>len(rawlog)) and log.get('sha256')==hashlib.sha256(rawlog).hexdigest(),'retained native log hash/truncation')
    if log.get('full_stream_sha256')is not None:
        h=log['full_stream_sha256'];require(type(h)is str and len(h)==64 and all(c in '0123456789abcdef' for c in h),'bounded full native stream hash')
        if not log['truncated']:require(h==log['sha256'],'complete stream equals retained log')
    if 'diagnostics' in trace:CORE.scope(trace['diagnostics'])
    budget.charge(2*(len(rawlog)//64+1)+2*n+3*sum(len(native.get(k,[])) for k in ('s','z')) if native is not None else 2*(len(rawlog)//64+1)+2*n)
    for value in (options,versions,rebuilt['receipt']):
        payload=encoded(value);budget.charge(2*(len(payload)//64+1),cells=len(payload)//64+1)
    metrics=CORE.diagnostics(x,rebuilt,decoded['selected_indices'],budget)
    return dict(verified=True,canonical_system_independently_rebuilt=True,native_coordinate_mapping='identity; complete original x without projection',original_rows=len(decoded['monomials']),original_variables=n,selected_rows=len(decoded['selected_indices']),
        assembly_hash=digest(rebuilt['receipt']),diagnostics=metrics,rounding='Python binary64 coefficient conversion and math.fsum; necessary PSD diagnostics, not certified error bounds',
        audit_operations=budget.operations,audit_cells=budget.cells,trace_bytes=len(raw),mathematical_feasibility='UNKNOWN',**FLAGS)


def verify_variant_against_cache(trace,witness,variant,**kwargs):
    """Reuse one independently verified cache within a whole-stage audit."""
    native=_verify_native(trace,witness,variant,**kwargs);cache_check=witness.check;decoded=witness.decoded
    operations=cache_check['audit_operations']+native['audit_operations'];cells=cache_check['audit_cells']+native['audit_cells']
    check=dict(verified=True,variant=variant,cache_check=cache_check,trace_check=native,canonical_system_independently_rebuilt=True,audit_operations=operations,audit_cells=cells,
        independent_audit_work_reserve=operations+cache_check['cache_bytes']+native['trace_bytes']+decoded['source_cells']+1,mathematical_feasibility='UNKNOWN',**FLAGS)
    return check,dict(audit_operations=native['audit_operations'],audit_cells=native['audit_cells'],cache_verification_reused=True)


def verify_variant_trace(trace,cache,variant,*,expected_source_hashes=None,expected_options=None,expected_versions=None,expected_parent_assembly=None,expected_parent_bindings=None,expected_cache_file_hash=None,deadline=None,max_operations=450000000,max_cells=60000000,max_coefficient_bits=4096,max_cache_bytes=CACHE_BYTES,max_trace_bytes=8388608,max_log_bytes=1048576):
    witness=prepare_verified_cache(cache,expected_parent_assembly=expected_parent_assembly,expected_parent_bindings=expected_parent_bindings,deadline=deadline,max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits,max_cache_bytes=max_cache_bytes)
    check,_=verify_variant_against_cache(trace,witness,variant,expected_source_hashes=expected_source_hashes,expected_options=expected_options,expected_versions=expected_versions,expected_cache_file_hash=expected_cache_file_hash,deadline=deadline,
        max_operations=max_operations-witness.check['audit_operations'],max_cells=max_cells-witness.check['audit_cells'],max_coefficient_bits=max_coefficient_bits,max_trace_bytes=max_trace_bytes,max_log_bytes=max_log_bytes)
    return check
