"""Independent proposal accounting and optional full finite Farkas admission.

The completed031 reduction is a licensed exact premise. Numerical checkpoint
scores are reported diagnostics: this audit does not replay the trajectory.
"""
from fractions import Fraction as F
import math
import time

import check_primitive_state_chart_dual_search as DIRECT
import check_primitive_state_chart_dual_geometry_search as GEOMETRY
import primitive_state_chart_dual_coordinate_protocol as PROTOCOL

require=DIRECT.require
encoded=DIRECT.encoded
FLAGS=dict(PROTOCOL.FLAGS)
SCHEMA='primitive-state-chart-dual-coordinate-independent-check-v1'
NUMERICAL_SCHEMA='primitive-state-chart-dual-coordinate-proposal-v1'
OUTCOME_SCHEMA='primitive-state-chart-dual-coordinate-search-v1'


class Budget(DIRECT.EXACT.Budget):
    def __init__(self,deadline,max_operations=90000000,max_cells=6000000,max_bits=4096):
        require(type(max_operations)is int and 0<max_operations<=90000000,'one shared90m coordinate and separator audit')
        super().__init__(deadline,max_operations,max_cells,20000000,max_bits)
        self.resident_cells=0

    def live(self,n):
        super().live(self.resident_cells+n)


def scope(value):
    DIRECT.scope_flags(value)
    for key in FLAGS:require(value.get(key)is False,'finite coordinate scope '+key)
    for key in ('finite_augmented_cone_infeasibility_certified','primal_feasibility_certified'):
        if key in value:require(value[key]is False,'producer cannot pre-admit '+key)


def finite(value,*,nonnegative=False):
    return type(value)in(int,float)and math.isfinite(value)and (not nonnegative or value>=0)


def ordered(value,allowed,b,label):
    require(type(value)is list,'explicit '+label);last=-1
    for j in value:
        b.charge();require(type(j)is int and j>last and j in allowed,'ordered distinct '+label);last=j
    return value


def _reservation(m,n,nnz,available,b):
    require(all(type(v)is int and v>0 for v in(m,n,nnz))and m<=443 and n<=851 and n<=nnz<=m*n
            and type(available)is int and 0<available<=190000000,'bounded numerical dimensions and allocation')
    setup=8*nnz+32*(m+n)+65536;sweep=8*nnz+32*n+2*m+64;refresh=8*nnz+16*(m+n)+256
    def total(s):return setup+17*(s*sweep+((s+15)//16+1)*refresh)
    low=0;high=10000
    while low<high:
        b.charge();middle=(low+high+1)//2
        if total(middle)<=available:low=middle
        else:high=middle-1
    return dict(setup=setup,sweep=sweep,refresh=refresh,phases=17,sweeps_per_phase=low,total=total(low))


def verify_numerical(numerical,rows,columns,nnz,budget):
    """Check finite metadata and proxy accounting, never recompute scores."""
    b=budget;scope(numerical)
    require(numerical.get('schema')==NUMERICAL_SCHEMA and type(numerical.get('complete'))is bool
            and type(numerical.get('attempted'))is bool,'explicit numerical trajectory disposition')
    for key,value in (('rows',rows),('columns',columns),('nonzeros',nnz)):
        require(type(numerical.get(key))is int and numerical[key]==value,'actual saved sparse model '+key)
    reservation=_reservation(rows,columns,nnz,numerical.get('max_operations'),b)
    reported=numerical.get('reservation');require(type(reported)is dict and reported==reservation
        and all(type(q)is int for q in reported.values()),'independent dimension-only numerical reservation')
    sweeps=numerical.get('sweeps_charged');refreshes=numerical.get('refreshes_charged');setup=numerical.get('setup_charged')
    visits=numerical.get('coordinate_visits');updates=numerical.get('nonzero_updates');S=reservation['sweeps_per_phase']
    require(type(setup)is bool and all(type(q)is int and q>=0 for q in(sweeps,refreshes,visits,updates)),
            'all explicit nonnegative numerical block counters')
    require(sweeps<=17*S and refreshes<=17*((S+15)//16+1)and visits<=columns*sweeps and updates<=nnz*sweeps,
            'charged work and sparse updates fit common reserved phase caps')
    counts=numerical.get('counts');operations=int(setup)*reservation['setup']+sweeps*reservation['sweep']+refreshes*reservation['refresh']
    require(type(counts)is dict and type(counts.get('operations'))is int and counts['operations']==operations
            and operations<=numerical['max_operations'],'exact numerical proxy-block accounting')
    peak=counts.get('peak_live_cells')
    require(type(peak)is int and peak>=0 and (peak<=6000000 or(not numerical['complete']
            and type(numerical.get('resource_failure'))is str and numerical['resource_failure'])),
            'saved numerical memory failure remains an incomplete diagnostic')
    bits=counts.get('maximum_rational_bits');require(type(bits)is int and 0<=bits<=4096,'bounded numerical coefficient bits')
    require(finite(numerical.get('elapsed_seconds'),nonnegative=True),'finite numerical elapsed time')
    checkpoints=numerical.get('checkpoints');require(type(checkpoints)is list and len(checkpoints)<=17,'at most17 complete phase checkpoints')
    reference=numerical.get('penalty_reference')
    require(finite(reference,nonnegative=True)or(reference is None and not numerical['complete']and not checkpoints),
            'finite penalty reference whenever numerical phases have completed')
    completed_sweeps=0;completed_refreshes=0;eligible=[]
    for i,record in enumerate(checkpoints):
        b.charge(16);require(type(record)is dict,'explicit phase checkpoint')
        require(type(record.get('phase'))is int and record['phase']==i,'successive phase order')
        penalty=0.0 if i==16 else math.ldexp(reference,-(2*i+1))
        require(finite(record.get('penalty'),nonnegative=True)and record['penalty']==penalty,'prescribed penalty schedule including final zero')
        completed=record.get('completed_sweeps')
        require(type(completed)is int and 1<=completed<=S,'common complete phase sweep allowance')
        support_size=record.get('support_size')
        require(type(support_size)is int and 0<=support_size<=columns
                and finite(record.get('residual_norm'),nonnegative=True)
                and finite(record.get('relative_residual'),nonnegative=True),'finite numerical checkpoint diagnostics')
        completed_sweeps+=completed;completed_refreshes+=completed//16+1
        if 1<=support_size<=443:eligible.append((record['relative_residual'],support_size,i))
    require(sweeps>=completed_sweeps and refreshes>=completed_refreshes,'every saved phase follows its charged end refresh')
    if numerical['complete']:
        require(numerical['attempted']is True and setup is True and S>=1 and len(checkpoints)==17
                and sweeps==completed_sweeps and refreshes==completed_refreshes and visits==columns*sweeps,
                'all17 complete phases and every exact charged block reconcile')
    else:
        remaining=1 if len(checkpoints)<17 else 0
        require(sweeps<=completed_sweeps+remaining*S
                and refreshes<=completed_refreshes+remaining*((S+15)//16+1),'partial charged work belongs to only the interrupted next phase')
    if not numerical['attempted']:
        require(not numerical['complete']and not setup and not sweeps and not refreshes and not visits
                and not updates and not checkpoints,'unattempted trajectory has no numerical work')
    if not setup:require(not sweeps and not refreshes and not visits and not updates,'setup precedes every numerical update')
    selected=numerical.get('selected')
    if not numerical['complete']or not eligible:
        require(selected is None,'incomplete or ineligible trajectory cannot propose a support')
        support=None
    else:
        best=min(eligible);require(type(selected)is dict and type(selected.get('phase'))is int
                and selected['phase']==best[2]and finite(selected.get('relative_residual'),nonnegative=True)
                and selected['relative_residual']==best[0],'prescribed reported-checkpoint ranking')
        vector=selected.get('scaled_vector');require(type(vector)is list and len(vector)==columns
                and all(finite(q,nonnegative=True)for q in vector),'full finite nonnegative selected vector')
        b.charge(3*columns);support=[j for j,q in enumerate(vector)if q>0]
        require(ordered(selected.get('support'),set(range(columns)),b,'all positive selected positions')==support
                and len(support)==best[1],'all strictly positive selected coordinates without trimming')
    b.live(4*columns+8*len(checkpoints)+len(checkpoints)*columns+nnz+rows)
    return dict(complete=numerical['complete'],selected_support=support,checkpoints=len(checkpoints),
                numerical_trajectory_replayed=False,numerical_scores_verified=False)


def _source(geometry,reduction,review,b):
    scope(geometry);scope(reduction);scope(review)
    check=review.get('independent_check')
    require(review.get('schema')=='primitive-state-chart-dual-reduction-independent-review-v1'
            and review.get('status')=='REDUCTION_VERIFIED'and review.get('all_passed')is True
            and review.get('reduction_verified')is True and review.get('resource_failure')is None
            and review.get('validation_failure')is None and review.get('finite_augmented_cone_infeasibility_certified')is False
            and type(check)is dict and check.get('schema')=='primitive-state-chart-dual-reduction-independent-check-v1'
            and check.get('verified')is True and check.get('complete')is True and check.get('reduction_verified')is True
            and check.get('restricted_system_inconsistent')is False,'licensed completed031 exact reduction premise')
    require(geometry.get('schema')==GEOMETRY.GEOMETRY_SCHEMA and geometry.get('complete')is True
            and geometry.get('width')==1224,'licensed030 geometry layout')
    compression=geometry.get('compression');require(type(compression)is dict,'licensed original representative mapping')
    representatives=ordered(compression.get('column_representatives'),set(range(851)),b,'original851 representatives')
    require(reduction.get('schema')=='primitive-state-chart-dual-reduction-v1'and reduction.get('complete')is True
            and reduction.get('status')=='REDUCED'and reduction.get('contradiction_row')is None
            and type(reduction.get('input_rows'))is int and 0<reduction['input_rows']<=443
            and type(reduction.get('input_columns'))is int and reduction['input_columns']==len(representatives),
            'complete consistent licensed reduction and representative domain')
    active=ordered(reduction.get('active_columns'),set(range(len(representatives))),b,'retained original compressed columns')
    records=reduction.get('final_rows');require(type(records)is list and 0<len(records)<=443 and active,'nonempty saved reduced equations')
    nnz=0;row_ids=[];previous=-1;used=set();target=False
    for record in records:
        require(type(record)is dict and set(record)=={'row_id','terms','rhs'}and type(record['row_id'])is int
                and previous<record['row_id']<reduction['input_rows'],'actual ordered saved row ids')
        previous=record['row_id'];row_ids.append(previous)
        parsed=GEOMETRY.sparse(record['terms'],set(active),b);nnz+=len(parsed);used.update(parsed)
        rhs=b.rational(record['rhs']);target=target or rhs!=0
    require(used==set(active)and target,'nonzero retained columns and nonzero reduced target')
    require(type(check.get('reduced_rows'))is int and check['reduced_rows']==len(records)
            and type(check.get('reduced_columns'))is int and check['reduced_columns']==len(active),'licensed reduced dimensions match saved equations')
    # Keep all prior exports resident across old direct helper live() calls.
    cells=8*1224+16*851+4*nnz+4*len(records)+4*len(active)
    for key in ('forms','responses'):
        values=geometry.get(key);require(type(values)is list,'resident licensed affine records');b.charge(len(values))
        for record in values:
            require(type(record)is dict and type(record.get('terms'))is list,'resident licensed sparse record')
            cells+=4+2*len(record['terms'])
    steps=reduction.get('steps');require(type(steps)is list,'resident licensed reduction trace')
    for step in steps:
        require(type(step)is dict,'resident licensed trace step');b.charge(len(step)+1)
        cells+=2*len(step)+sum(len(v)for v in step.values()if type(v)is list)
    for col in compression.get('compressed_columns',[]):
        require(type(col)is list,'resident prior compressed columns');cells+=2*len(col)
    b.resident_cells+=cells;b.live(0)
    return len(records),len(active),nnz,active,row_ids,representatives


def verify_outcome(chart,chart_review,rays,geometry,reduction,reduction_review,outcome,*,deadline=None,
                   max_operations=90000000,max_cells=6000000,max_bits=4096,max_certificate_bytes=8388608):
    require(type(max_certificate_bytes)is int and 0<max_certificate_bytes<=8388608,'bounded coordinate proposal')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,max_bits)
    try:
        scope(outcome);require(outcome.get('schema')==OUTCOME_SCHEMA and outcome.get('status')in('CERTIFICATE_PROPOSED','NONCERTIFIED','UNKNOWN')
                               and outcome.get('route')=='coordinate_descent'and outcome.get('policy')==PROTOCOL.POLICY
                               and outcome.get('limits')==PROTOCOL.LIMITS,'known single coordinate search policy and disposition')
        data=encoded(outcome)
        if len(data)>max_certificate_bytes:raise OverflowError('independent coordinate outcome byte cap')
        b.charge(2*(len(data)//64+1),cells=len(data)//64+1);b.resident_cells+=len(data);b.live(0)
        m,n,nnz,active,row_ids,representatives=_source(geometry,reduction,reduction_review,b)
        numerical=outcome.get('numerical');stats=outcome.get('model_stats');numeric_check=None
        if numerical is not None:
            require(type(stats)is dict and stats.get('rows')==m and stats.get('columns')==n and stats.get('nonzeros')==nnz
                    and all(type(stats.get(k))is int for k in('rows','columns','nonzeros'))
                    and stats.get('active_columns')==active and stats.get('row_ids')==row_ids,'model metadata from actual saved equations')
            scaling=stats.get('scaling');require(type(scaling)is dict,'explicit positive exact scaling diagnostics')
            require(scaling.get('positive_exact')is True and scaling.get('finite_nonunderflowing_conversion')is True,
                    'declared positive scaling and finite nonunderflowing conversion')
            for prefix in ('row','column'):
                low=b.rational(scaling.get(prefix+'_scale_min'));high=b.rational(scaling.get(prefix+'_scale_max'))
                require(0<low<=high,'finite positive scaling range')
            numeric_check=verify_numerical(numerical,m,n,nnz,b)
        certificate=outcome.get('certificate');certificate_check=None
        if outcome['status']=='CERTIFICATE_PROPOSED':
            require(numeric_check is not None and numeric_check['complete']and numeric_check['selected_support']is not None,
                    'only a completed eligible trajectory can propose exact restoration')
            rows,pivots,free,source_cells=DIRECT.parse_chart(chart,chart_review,b)
            require(geometry.get('pivot_columns')==pivots and geometry.get('free_indices')==free,'same licensed original chart partition')
            generators,generator_cells=DIRECT.parse_rays(rays,b);b.live(source_cells+generator_cells+4*1224+4*851)
            certificate_check=GEOMETRY.verify_saved_certificate(certificate,rays,rows,pivots,free,generators,b,max_certificate_bytes=max_certificate_bytes)
            support=[representatives[active[j]]for j in numeric_check['selected_support']]
            restoration=outcome.get('restoration_stats')
            require(type(restoration)is dict and restoration.get('support')==support and type(restoration.get('support_size'))is int
                    and restoration['support_size']==len(support)and restoration.get('complete')is True
                    and restoration.get('free_rule')=='zero','complete exact reconstruction binds every positive selected original ray')
            alpha=[b.rational(q)for q in certificate['alpha']];b.charge(3*len(alpha));support_set=set(support)
            free_positions=ordered(restoration.get('free_support_coordinates'),set(range(len(support))),b,'declared reconstruction free positions')
            require(type(restoration.get('rank'))is int and restoration['rank']==len(support)-len(free_positions)
                    and all(q==0 for j,q in enumerate(alpha)if j not in support_set)
                    and all(alpha[support[j]]==0 for j in free_positions),'full representative support-only lift and zero declared free values')
        else:
            require(certificate is None,'unsuccessful coordinate search has no certificate')
            if numeric_check is None or not numeric_check['complete']:
                require(outcome['status']=='UNKNOWN','incomplete numerical trajectory remains UNKNOWN')
            elif numeric_check['selected_support']is None:
                require(outcome['status']=='NONCERTIFIED','complete ineligible trajectory remains NONCERTIFIED')
        summary=dict(schema=SCHEMA,verified=True,complete=certificate_check is not None,
                     status='FINITE_CONE_INFEASIBLE'if certificate_check else outcome['status'],
                     certificate_verified=certificate_check is not None,finite_augmented_cone_infeasibility_certified=certificate_check is not None,
                     certificate_check=certificate_check,numerical_trajectory_replayed=False,numerical_scores_verified=False,
                     original_unlearned_cone_infeasibility_certified=False,primal_feasibility_certified=False,**FLAGS)
        payload=encoded(summary);b.charge(2*(len(payload)//64+1))
        summary.update(audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,
                       independent_audit_work_reserve=b.operations)
        return summary
    except(OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        raise
