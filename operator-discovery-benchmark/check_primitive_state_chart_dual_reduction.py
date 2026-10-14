"""Independent finite elementary reduction and full Farkas witness checking.

Completed030 compression is a reusable licensed premise. Each new step is
checked with separate exact arithmetic; numerical optimization is not replayed.
Search-system contradiction alone has no primal cone implication.
"""
from fractions import Fraction as F
import math
import time

import check_primitive_state_chart_dual_search as DIRECT
import check_primitive_state_chart_dual_geometry_search as GEOMETRY
import primitive_state_chart_dual_reduction_protocol as PROTOCOL

require=DIRECT.require
encoded=DIRECT.encoded
FLAGS=dict(PROTOCOL.FLAGS)
SCHEMA='primitive-state-chart-dual-reduction-independent-check-v1'
REDUCTION_SCHEMA='primitive-state-chart-dual-reduction-v1'
OUTCOME_SCHEMA='primitive-state-chart-dual-reduction-search-v1'


class Budget(DIRECT.EXACT.Budget):
    def __init__(self,deadline,max_operations=80000000,max_cells=6000000,max_bits=4096):
        require(type(max_operations)is int and 0<max_operations<=80000000,'one shared80m reduction and separator audit')
        super().__init__(deadline,max_operations,max_cells,20000000,max_bits)
        self.resident_cells=0

    def live(self,n):
        super().live(self.resident_cells+n)


def scope(value):
    DIRECT.scope_flags(value)
    for key in FLAGS:require(value.get(key)is False,'finite reduction scope '+key)
    for key in ('finite_augmented_cone_infeasibility_certified','primal_feasibility_certified'):
        if key in value:require(value[key]is False,'producer cannot pre-admit '+key)


def ids(value,allowed,b,label,*,nonempty=False):
    require(type(value)is list and (value or not nonempty),'explicit '+label)
    last=-1
    for j in value:
        b.charge();require(type(j)is int and j>last and j in allowed,'unique ordered '+label);last=j
    return value


def _replay(input_rows,column_count,artifact,b):
    scope(artifact)
    steps=artifact.get('steps');require(type(steps)is list,'complete elementary reduction steps')
    final=artifact.get('final_rows');require(type(final)is list,'explicit final row records')
    # Original trace, exported final equations and input dictionaries remain
    # resident while replay constructs its own mutable exact row dictionaries.
    artifact_cells=128
    for step in steps:
        require(type(step)is dict,'explicit elementary reduction step');b.charge(len(step)+1)
        artifact_cells+=2*len(step)+sum(len(v)for v in step.values()if type(v)is list)
    for record in final:
        require(type(record)is dict and type(record.get('terms'))is list,'explicit final coefficient records');b.charge()
        artifact_cells+=4+2*len(record['terms'])
    for key in ('active_columns','forced_zero_columns','discarded_zero_target_columns'):
        require(type(artifact.get(key))is list,'explicit column dispositions');artifact_cells+=len(artifact[key])
    b.resident_cells+=artifact_cells;b.live(0)
    require(type(column_count)is int and 0<=column_count<=851 and type(input_rows)is dict and len(input_rows)<=443,'bounded compressed system')
    require(all(type(i)is int for i in input_rows)and sorted(input_rows)==list(range(len(input_rows))),'all initial row positions')
    rows={};cells=0
    for i,source in sorted(input_rows.items()):
        require(type(source)is dict and len(source)<=column_count+1,'complete sparse input row');row={}
        for j,value in source.items():
            require(type(j)is int and 0<=j<=column_count,'input coefficient or RHS position')
            q=b.rational(value);require(q!=0,'sparse zeros absent');row[j]=q
        rows[i]=row;cells+=len(row);b.live(2*cells+2*len(rows)+4*column_count)
    require(artifact.get('schema')==REDUCTION_SCHEMA and artifact.get('complete')is True
            and type(artifact.get('input_rows'))is int and artifact['input_rows']==len(rows)
            and type(artifact.get('input_columns'))is int and artifact['input_columns']==column_count
            and artifact.get('policy')==PROTOCOL.POLICY,'complete declared reduction policy and dimensions')
    active=set(range(column_count));forced=set();discarded=set();initial_cells=cells
    def live():
        b.charge(len(rows));b.live(initial_cells+3*sum(len(row)for row in rows.values())+8*column_count+4*len(rows))
    for step in steps:
        b.charge();require(type(step)is dict,'explicit elementary reduction step');kind=step.get('kind')
        if kind=='force_zero':
            require(set(step)=={'kind','row_id','columns'}and type(step['row_id'])is int and step['row_id']in rows,'active sign propagation row')
            row=rows[step['row_id']];columns=ids(step['columns'],active,b,'forced columns',nonempty=True)
            coefficients={j:q for j,q in row.items()if j!=column_count}
            require(row.get(column_count,F(0))==0 and columns==sorted(coefficients)
                    and (all(q>0 for q in coefficients.values())or all(q<0 for q in coefficients.values())),
                    'homogeneous full strictly one-sign support forces zero')
            for other in rows.values():
                b.charge(len(columns))
                for j in columns:other.pop(j,None)
            active.difference_update(columns);forced.update(columns)
        elif kind=='drop_zero_rows':
            require(set(step)=={'kind','rows'},'explicit zero row removal')
            removed=ids(step['rows'],set(rows),b,'zero rows',nonempty=True)
            require(all(not rows[i]for i in removed),'only complete zero augmented rows may be dropped')
            for i in removed:del rows[i]
        elif kind=='discard_homogeneous_components':
            require(set(step)=={'kind','columns','rows'},'explicit zero-target component removal')
            columns=ids(step['columns'],active,b,'discarded columns',nonempty=True)
            removed=ids(step['rows'],set(rows),b,'discarded component rows');column_set=set(columns);row_set=set(removed)
            for i,row in rows.items():
                b.charge(len(row))
                if i in row_set:
                    require(not row.get(column_count,F(0))and set(row).issubset(column_set),'removed component has zero target and closed coefficients')
                else:require(not(set(row)&column_set),'retained rows do not use discarded component columns')
            for i in removed:del rows[i]
            active.difference_update(columns);discarded.update(columns)
        elif kind=='pivot':
            require(set(step)=={'kind','row_id','column','eliminate'}and type(step['row_id'])is int
                    and step['row_id']in rows and type(step['column'])is int and step['column']in active,'active invertible pivot')
            i=step['row_id'];j=step['column'];pivot=rows[i].get(j,F(0));require(pivot!=0,'nonzero exact pivot')
            eliminated=ids(step['eliminate'],set(rows)-{i},b,'eliminated rows')
            require(all(rows[k].get(j,F(0))!=0 for k in eliminated),'each listed row has a pivot coefficient')
            rows[i]={k:b.div(q,pivot)for k,q in rows[i].items()}
            for k in eliminated:
                factor=rows[k][j]
                for column,q in rows[i].items():
                    value=b.add(rows[k].get(column,F(0)),-b.mul(factor,q))
                    if value:rows[k][column]=value
                    else:rows[k].pop(column,None)
                live()
        else:raise ValueError('unknown elementary reduction rule')
        live()
    require(len(final)==len(rows),'all retained original rows')
    for (i,row),record in zip(sorted(rows.items()),final):
        require(type(record)is dict and set(record)=={'row_id','terms','rhs'}and type(record['row_id'])is int and record['row_id']==i,'retained row identity')
        parsed=GEOMETRY.sparse(record['terms'],active,b)
        rhs=b.rational(record['rhs'])
        if rhs:parsed[column_count]=rhs
        require(parsed==row,'every final coefficient and RHS matches the invertible replay')
    require(ids(artifact.get('active_columns'),set(range(column_count)),b,'final active columns')==sorted(active)
            and ids(artifact.get('forced_zero_columns'),set(range(column_count)),b,'forced dispositions')==sorted(forced)
            and ids(artifact.get('discarded_zero_target_columns'),set(range(column_count)),b,'discarded dispositions')==sorted(discarded),
            'all original column dispositions match explicit proof steps')
    require(not(forced&discarded or active&forced or active&discarded)
            and active|forced|discarded==set(range(column_count)),'complete disjoint original column dispositions')
    contradictions=[i for i,row in sorted(rows.items())if not(set(row)-{column_count})and row.get(column_count,F(0))!=0]
    contradiction=artifact.get('contradiction_row')
    require((type(contradiction)is int and contradiction in contradictions)if contradictions else contradiction is None,'declared restricted search contradiction')
    require(artifact.get('status')==('RESTRICTED_SYSTEM_INCONSISTENT'if contradictions else'REDUCED'),'restricted system disposition only')
    rounds=artifact.get('rounds');require(type(rounds)is int and 0<=rounds<=PROTOCOL.POLICY['max_elimination_rounds']and type(artifact.get('fixed_point'))is bool,'bounded rounds without maximality claim')
    summary=dict(verified=True,complete=True,reduction_verified=True,reduced_rows=len(rows),reduced_columns=len(active),
                 active_columns=sorted(active),forced_zero_columns=sorted(forced),discarded_zero_target_columns=sorted(discarded),
                 steps=len(steps),rounds=rounds,restricted_system_inconsistent=bool(contradictions),
                 primal_feasibility_certified=False,**FLAGS)
    b.resident_cells+=initial_cells+sum(map(len,rows.values()))
    return summary,rows


def verify_reduction(input_rows,column_count,artifact,budget):
    return _replay(input_rows,column_count,artifact,budget)[0]


def _licensed_input(geometry,review,b):
    scope(geometry);scope(review)
    check=review.get('independent_check')
    require(review.get('schema')=='primitive-state-chart-dual-geometry-independent-review-v1'
            and review.get('status')=='GEOMETRY_VERIFIED'and review.get('all_passed')is True
            and review.get('geometry_verified')is True and review.get('resource_failure')is None
            and type(check)is dict and check.get('schema')==GEOMETRY.SCHEMA
            and check.get('verified')is True and check.get('complete')is True
            and check.get('exact_compression_verified')is True,'licensed complete030 exact compression premise')
    require(review.get('finite_augmented_cone_infeasibility_certified')is False,'prior geometry supplies no separator')
    require(geometry.get('schema')==GEOMETRY.GEOMETRY_SCHEMA and geometry.get('complete')is True
            and geometry.get('width')==1224 and geometry.get('policy')==GEOMETRY.POLICY,'known licensed030 geometry')
    compression=geometry.get('compression');require(type(compression)is dict,'licensed compressed system')
    representatives=ids(compression.get('column_representatives'),set(range(851)),b,'original ray representatives')
    free=geometry.get('free_indices');require(type(free)is list and len(free)==442,'licensed free coordinate partition')
    row_keys=ids(compression.get('row_representatives'),set(free)|{1224},b,'compressed original coordinates')
    n=len(representatives);require(len(row_keys)<=443,'bounded prior compressed rows')
    require(compression.get('row_target_included')is True and compression.get('row_keys')==free+[1224]
            and compression.get('compressed_rhs')==[[1224,'-1']]and 1224 in row_keys,'full augmented target included')
    columns=compression.get('compressed_columns');require(type(columns)is list and len(columns)==n,'all compressed representative columns')
    # The verified prior artifact stays in memory. Count its exported affine
    # records without recomputing their mathematical content.
    geometry_cells=8*1224+16*851
    for key in ('forms','responses'):
        records=geometry.get(key);require(type(records)is list,'resident prior affine records')
        b.charge(len(records))
        for record in records:
            require(type(record)is dict and type(record.get('terms'))is list,'resident prior sparse record')
            geometry_cells+=2*len(record['terms'])+4
    geometry_cells+=4*sum(len(col)for col in columns)
    b.resident_cells+=geometry_cells;b.live(0)
    positions={j:i for i,j in enumerate(row_keys)};rows={i:{}for i in range(len(row_keys))};cells=0
    for j,column in enumerate(columns):
        parsed=GEOMETRY.sparse(column,set(row_keys),b)
        for key,q in parsed.items():rows[positions[key]][j]=q;cells+=1
        b.live(3*cells+4*len(row_keys)+4*n)
    rows[positions[1224]][n]=F(-1)
    if 'compressed_rows'in check:require(check['compressed_rows']==len(rows),'licensed row count binding')
    if 'compressed_columns'in check:require(check['compressed_columns']==n,'licensed column count binding')
    return rows,n,representatives


def verify_outcome(chart,chart_review,rays,geometry,geometry_review,reduction,outcome,*,deadline=None,
                   max_operations=80000000,max_cells=6000000,max_bits=4096,
                   max_reduction_bytes=67108864,max_certificate_bytes=8388608):
    require(type(max_reduction_bytes)is int and 0<max_reduction_bytes<=67108864
            and type(max_certificate_bytes)is int and 0<max_certificate_bytes<=8388608,'bounded reduction and outcome artifacts')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,max_bits)
    try:
        require(type(outcome)is dict and outcome.get('schema')==OUTCOME_SCHEMA
                and outcome.get('status')in('CERTIFICATE_PROPOSED','NONCERTIFIED','UNKNOWN'),'explicit reduction outcome')
        scope(outcome)
        for value,cap,label in ((reduction,max_reduction_bytes,'reduction'),(outcome,max_certificate_bytes,'outcome')):
            data=encoded(value)
            if len(data)>cap:raise OverflowError('independent '+label+' byte cap')
            b.charge(2*(len(data)//64+1),cells=len(data)//64+1);b.live(len(data)//64+1)
        input_rows,n,representatives=_licensed_input(geometry,geometry_review,b)
        # JSON nodes require at least one encoded byte; this deliberately
        # conservative allowance covers the whole outcome, including saved
        # full rays/weights, while retained geometry and replay are also live.
        b.resident_cells+=len(encoded(outcome))
        summary,final_rows=_replay(input_rows,n,reduction,b);certificate=outcome.get('certificate');certificate_check=None
        if outcome['status']=='CERTIFICATE_PROPOSED':
            require(outcome.get('reduction_complete')is True and outcome.get('route')=='reduced_lp'
                    and not summary['restricted_system_inconsistent'],'certificate follows verified consistent reduction')
            rows,pivots,free,source_cells=DIRECT.parse_chart(chart,chart_review,b)
            require(geometry.get('pivot_columns')==pivots and geometry.get('free_indices')==free,'same licensed chart partition')
            generators,generator_cells=DIRECT.parse_rays(rays,b)
            b.live(source_cells+generator_cells+4*1224+4*851+3*sum(map(len,final_rows.values())))
            certificate_check=GEOMETRY.verify_saved_certificate(certificate,rays,rows,pivots,free,generators,b,max_certificate_bytes=max_certificate_bytes)
            active=summary['active_columns'];native=outcome.get('native')
            require(type(native)is dict and native.get('success')is True and native.get('attempted')is True,'single successful reduced native support proposal')
            vector=native.get('scaled_vector')
            require(type(vector)is list and len(vector)==len(active)and all(type(q)in(int,float)and math.isfinite(q)for q in vector),'all finite native reduced coordinates')
            support=[representatives[active[j]]for j,q in enumerate(vector)if q>0]
            stats=outcome.get('restoration_stats')
            require(len(support)<=443 and type(stats)is dict and stats.get('support')==support
                    and type(stats.get('support_size'))is int and stats['support_size']==len(support)
                    and stats.get('complete')is True and stats.get('free_rule')=='zero','all strictly positive reduced native coordinates lift to exact original support')
            alpha=[b.rational(q)for q in certificate['alpha']];support_set=set(support);b.charge(3*len(alpha)+len(active))
            free_support=ids(stats.get('free_support_coordinates'),set(range(len(support))),b,'free reconstruction positions')
            require(type(stats.get('rank'))is int and stats['rank']==len(support)-len(free_support)
                    and all(q==0 for j,q in enumerate(alpha)if j not in support_set)
                    and all(alpha[support[j]]==0 for j in free_support),'support-only full lift and zero declared free values')
        else:require(certificate is None,'unsuccessful reduction search has no certificate')
        summary.update(schema=SCHEMA,status='FINITE_CONE_INFEASIBLE'if certificate_check else outcome['status'],
                       certificate_verified=certificate_check is not None,
                       finite_augmented_cone_infeasibility_certified=certificate_check is not None,
                       certificate_check=certificate_check,original_unlearned_cone_infeasibility_certified=False,
                       native_LP_replayed=False,old_elimination_replayed=False)
        data=encoded(summary);b.charge(2*(len(data)//64+1))
        summary.update(audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,
                       independent_audit_work_reserve=b.operations)
        return summary
    except(OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        raise
