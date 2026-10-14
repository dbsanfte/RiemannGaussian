"""Independent accelerated-proposal accounting and full finite witness audit.

Numerical trajectory, line tests and scores are diagnostics, not proof
premises. A licensed031 system and a complete original Farkas identity are
the only mathematical premises used for any new finite-cone conclusion.
"""
import math
import time

import check_primitive_state_chart_dual_coordinate as REUSE
import primitive_state_chart_dual_metric_protocol as PROTOCOL

DIRECT=REUSE.DIRECT
GEOMETRY=REUSE.GEOMETRY
require=REUSE.require
encoded=REUSE.encoded
finite=REUSE.finite
scope=REUSE.scope
ordered=REUSE.ordered
Budget=REUSE.Budget
FLAGS=dict(PROTOCOL.FLAGS)
SCHEMA='primitive-state-chart-dual-metric-independent-check-v1'
NUMERICAL_SCHEMA='primitive-state-chart-dual-metric-proposal-v1'
OUTCOME_SCHEMA='primitive-state-chart-dual-metric-search-v1'


def _work_model(m,n,nnz,b):
    b.charge(16)
    require(all(type(q)is int for q in(m,n,nnz))and 1<=m<=443 and 1<=n<=851 and n<=nnz<=m*n,
            'bounded actual sparse dimensions')
    setup=8*nnz+48*(m+n)+65536;gradient=8*nnz+32*(m+n)+512
    trial=16*nnz+80*(m+n)+1024;commit=32*(m+n)+512;final=12*nnz+80*(m+n)+2048
    reserve=gradient+32*trial+commit
    return dict(setup=setup,gradient=gradient,trial=trial,commit=commit,final=final,
                iteration_reserve=reserve,minimum_attempt=setup+reserve+final,
                max_iterations=10000,max_backtracking_trials=32)


def verify_numerical(numerical,rows,columns,nnz,budget):
    b=budget;scope(numerical)
    require(numerical.get('schema')==NUMERICAL_SCHEMA and type(numerical.get('complete'))is bool
            and type(numerical.get('attempted'))is bool,'explicit accelerated trajectory disposition')
    for key,value in (('rows',rows),('columns',columns),('nonzeros',nnz)):
        require(type(numerical.get(key))is int and numerical[key]==value,'actual sparse model '+key)
    cap=numerical.get('max_operations');require(type(cap)is int and 0<cap<=190000000,'bounded numerical allocation')
    work=_work_model(rows,columns,nnz,b);reported=numerical.get('work_model')
    require(type(reported)is dict and reported==work and all(type(q)is int for q in reported.values()),
            'independent dimension-only work model')
    setup=numerical.get('setup_charged');final=numerical.get('final_charged')
    gradient=numerical.get('gradient_blocks');trials=numerical.get('trial_blocks');commit=numerical.get('commit_blocks')
    require(type(setup)is bool and type(final)is bool and all(type(q)is int and q>=0 for q in(gradient,trials,commit)),
            'explicit charged numerical blocks')
    operations=int(setup)*work['setup']+gradient*work['gradient']+trials*work['trial']+commit*work['commit']+int(final)*work['final']
    counts=numerical.get('counts');require(type(counts)is dict and type(counts.get('operations'))is int
            and counts['operations']==operations and operations<=cap,'exact accelerated proxy-block reconciliation')
    peak=counts.get('peak_live_cells');require(type(peak)is int and peak>=0 and (peak<=6000000 or(
        not numerical['complete']and type(numerical.get('resource_failure'))is str and numerical['resource_failure'])),
        'preserved incomplete memory-failure diagnostic')
    bits=counts.get('maximum_rational_bits');require(type(bits)is int and 0<=bits<=4096,'bounded coefficient metadata')
    require(finite(numerical.get('elapsed_seconds'),nonnegative=True),'finite numerical elapsed time')
    checkpoints=numerical.get('checkpoints');require(type(checkpoints)is list and len(checkpoints)<=10000,'bounded accepted checkpoint prefix')
    initial=numerical.get('initial_lipschitz')
    require(initial is None or(finite(initial)and initial==1),'fixed unit initial step estimate when available')
    metric=numerical.get('metric_diagonal')
    if initial is not None:
        require(type(metric)is list and len(metric)==columns and all(finite(q)and q>0 for q in metric),
                'full finite positive diagonal metric before iteration')
        b.charge(columns)
    else:require(metric is None,'uninitialized metric is not a completed setup')
    require(not checkpoints or initial is not None,'accepted checkpoints follow initial step setup')
    require(not(gradient or trials or commit)or initial is not None,'every iteration block follows the positive initial step estimate')
    cumulative=work['setup']if setup else 0;trial_sum=0;eligible=[];previous_L=initial
    for index,checkpoint in enumerate(checkpoints,1):
        b.charge(32);require(type(checkpoint)is dict and type(checkpoint.get('iteration'))is int
                and checkpoint['iteration']==index,'successive1-based accepted checkpoints')
        require(cumulative+work['iteration_reserve']+work['final']<=cap,
                'every accepted start reserves32 trials, commit and final diagnostic')
        count=checkpoint.get('backtracking_trials');require(type(count)is int and 1<=count<=32,'bounded accepted trial count')
        expected=math.ldexp(previous_L,count-1)
        L=checkpoint.get('lipschitz');require(finite(L)and L>0 and finite(expected)and L==expected,
                'carried step estimate doubles once per rejected trial')
        previous_L=L;trial_sum+=count
        cumulative+=work['gradient']+count*work['trial']+work['commit']
        require(type(checkpoint.get('cumulative_operations'))is int and checkpoint['cumulative_operations']==cumulative,
                'every accepted cumulative charge matches all preceding blocks')
        require(type(checkpoint.get('momentum_restarted'))is bool and checkpoint['momentum_restarted']==(index%64==0),
                'prescribed64-step momentum restart')
        size=checkpoint.get('support_size');require(type(size)is int and 0<=size<=columns
                and finite(checkpoint.get('residual_norm'),nonnegative=True)
                and finite(checkpoint.get('relative_residual'),nonnegative=True),'finite accepted diagnostics and support size')
        if index<len(checkpoints):require(checkpoint['residual_norm']>0,'zero reported residual stops before another iteration')
        if 1<=size<=443:eligible.append((checkpoint['relative_residual'],size,index))
    k=len(checkpoints)
    require(gradient>=k and commit>=k and trials>=trial_sum,'saved accepted prefix follows its charged blocks')
    stop=numerical.get('stop_reason');require(stop in(None,'work_boundary','iteration_limit','zero_reported_residual'),'declared numerical stop rule')
    diagnostic=numerical.get('final_diagnostic')
    if numerical['complete']:
        require(numerical['attempted']is True and setup is True and final is True and k>=1
                and gradient==k and commit==k and trials==trial_sum,'completed accepted trajectory and final charge')
        last=checkpoints[-1]
        if last['residual_norm']==0:require(stop=='zero_reported_residual','zero reported residual has immediate stop priority')
        elif k==10000:require(stop=='iteration_limit','hard accepted-iteration stop priority')
        else:require(stop=='work_boundary'and operations+work['iteration_reserve']>cap,'normal bounded work boundary without convergence claim')
        require(type(diagnostic)is dict and type(diagnostic.get('iteration'))is int and diagnostic['iteration']==k
                and finite(diagnostic.get('lipschitz'))and diagnostic['lipschitz']==last['lipschitz']
                and finite(diagnostic.get('residual_norm'),nonnegative=True)
                and finite(diagnostic.get('relative_residual'),nonnegative=True)
                and finite(diagnostic.get('projected_gradient_norm'),nonnegative=True)
                and diagnostic.get('mapping_metric')=='diagonal column curvature',
                'finite final weighted stationarity diagnostic at last accepted iterate')
    else:
        require(numerical.get('selected')is None and diagnostic is None,'interrupted trajectory proposes no support or complete final diagnostic')
        extra_gradient=gradient-k;extra_commit=commit-k;extra_trials=trials-trial_sum
        require(extra_gradient in(0,1)and extra_commit in(0,1)and 0<=extra_trials<=32,'only one interrupted step after the accepted prefix')
        if final:
            require(k>=1 and extra_gradient==extra_commit==extra_trials==0,'only one interrupted final diagnostic at an accepted boundary')
        elif extra_gradient:
            require(k<10000 and (not checkpoints or checkpoints[-1]['residual_norm']>0)
                    and cumulative+work['iteration_reserve']+work['final']<=cap,'interrupted next step obeys the same worst-case start guard')
            require(extra_commit==0 or extra_trials>=1,'commit follows at least one charged trial')
        else:require(extra_commit==extra_trials==0,'trial and commit blocks follow their gradient')
        if final or stop is not None:
            require(k>=1 and extra_gradient==extra_commit==extra_trials==0 and stop is not None,
                    'final diagnostic follows a declared normal accepted-boundary stop')
            last=checkpoints[-1]
            if last['residual_norm']==0:require(stop=='zero_reported_residual','interrupted final retains zero-stop priority')
            elif k==10000:require(stop=='iteration_limit','interrupted final retains hard iteration stop')
            else:require(stop=='work_boundary'and cumulative+work['final']+work['iteration_reserve']>cap,
                         'interrupted final still follows a valid bounded work stop')
    if not numerical['attempted']:
        require(not numerical['complete']and not setup and not final and not gradient and not trials and not commit
                and not checkpoints and initial is None and cap<work['minimum_attempt'],'unattempted proposal fails the initial complete-attempt reserve')
    else:require(cap>=work['minimum_attempt'],'attempted numerical setup has full initial worst-case room')
    if not setup:
        require(not gradient and not trials and not commit and not final and not checkpoints and initial is None,
                'setup precedes every iteration and diagnostic')
    selected=numerical.get('selected');support=None
    if numerical['complete']and eligible:
        best=min(eligible);require(type(selected)is dict and type(selected.get('iteration'))is int and selected['iteration']==best[2]
                and finite(selected.get('relative_residual'),nonnegative=True)and selected['relative_residual']==best[0],
                'prescribed ranking among reported eligible accepted checkpoints')
        vector=selected.get('scaled_vector');require(type(vector)is list and len(vector)==columns
                and all(finite(q,nonnegative=True)for q in vector),'full finite nonnegative selected vector')
        b.charge(3*columns);support=[j for j,q in enumerate(vector)if q>0]
        require(ordered(selected.get('support'),set(range(columns)),b,'every strictly positive selected position')==support
                and len(support)==best[1],'no threshold or trimming of selected support')
    else:require(selected is None,'incomplete or ineligible proposal cannot select support')
    b.live(4*nnz+25*columns+12*rows+12*k)
    return dict(complete=numerical['complete'],selected_support=support,checkpoints=k,
                numerical_trajectory_replayed=False,numerical_scores_verified=False)


def verify_outcome(chart,chart_review,rays,geometry,reduction,reduction_review,outcome,*,deadline=None,
                   max_operations=90000000,max_cells=6000000,max_bits=4096,max_certificate_bytes=8388608):
    require(type(max_certificate_bytes)is int and 0<max_certificate_bytes<=8388608,'bounded accelerated proposal')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,max_bits)
    try:
        scope(outcome);require(outcome.get('schema')==OUTCOME_SCHEMA and outcome.get('status')in('CERTIFICATE_PROPOSED','NONCERTIFIED','UNKNOWN')
                and outcome.get('route')=='metric_acceleration'and outcome.get('policy')==PROTOCOL.POLICY
                and outcome.get('limits')==PROTOCOL.LIMITS,'known accelerated search policy and disposition')
        data=encoded(outcome)
        if len(data)>max_certificate_bytes:raise OverflowError('independent accelerated outcome byte cap')
        b.charge(2*(len(data)//64+1),cells=len(data)//64+1);b.resident_cells+=len(data);b.live(0)
        m,n,nnz,active,row_ids,representatives=REUSE._source(geometry,reduction,reduction_review,b)
        numerical=outcome.get('numerical');stats=outcome.get('model_stats');numeric_check=None
        if numerical is not None:
            require(type(stats)is dict and stats.get('rows')==m and stats.get('columns')==n and stats.get('nonzeros')==nnz
                    and all(type(stats.get(key))is int for key in('rows','columns','nonzeros'))
                    and stats.get('active_columns')==active and stats.get('row_ids')==row_ids,'model metadata matches actual saved reduced equations')
            scaling=stats.get('scaling');require(type(scaling)is dict and scaling.get('positive_exact')is True
                and scaling.get('finite_nonunderflowing_conversion')is True,'positive exact scaling and nonunderflowing conversion diagnostics')
            for prefix in('row','column'):
                low=b.rational(scaling.get(prefix+'_scale_min'));high=b.rational(scaling.get(prefix+'_scale_max'))
                require(0<low<=high,'positive exact scaling ranges')
            numeric_check=verify_numerical(numerical,m,n,nnz,b)
        certificate=outcome.get('certificate');certificate_check=None
        if outcome['status']=='CERTIFICATE_PROPOSED':
            require(numeric_check is not None and numeric_check['complete']and numeric_check['selected_support']is not None,
                    'only completed eligible accelerated trajectory restores an exact witness')
            rows,pivots,free,source_cells=DIRECT.parse_chart(chart,chart_review,b)
            require(geometry.get('pivot_columns')==pivots and geometry.get('free_indices')==free,'same licensed original chart partition')
            generators,generator_cells=DIRECT.parse_rays(rays,b);b.live(source_cells+generator_cells+4*1224+4*851)
            certificate_check=GEOMETRY.verify_saved_certificate(certificate,rays,rows,pivots,free,generators,b,max_certificate_bytes=max_certificate_bytes)
            support=[representatives[active[j]]for j in numeric_check['selected_support']];restoration=outcome.get('restoration_stats')
            require(type(restoration)is dict and restoration.get('support')==support and type(restoration.get('support_size'))is int
                    and restoration['support_size']==len(support)and restoration.get('complete')is True
                    and restoration.get('free_rule')=='zero','exact reconstruction binds every positive selected original ray')
            alpha=[b.rational(q)for q in certificate['alpha']];b.charge(3*len(alpha));support_set=set(support)
            free_positions=ordered(restoration.get('free_support_coordinates'),set(range(len(support))),b,'declared reconstruction free positions')
            require(type(restoration.get('rank'))is int and restoration['rank']==len(support)-len(free_positions)
                    and all(q==0 for j,q in enumerate(alpha)if j not in support_set)
                    and all(alpha[support[j]]==0 for j in free_positions),'full representative support-only lift and zero declared free values')
        else:
            require(certificate is None,'unsuccessful accelerated search has no certificate')
            if numeric_check is None or not numeric_check['complete']:require(outcome['status']=='UNKNOWN','interrupted trajectory remains UNKNOWN')
            elif numeric_check['selected_support']is None:require(outcome['status']=='NONCERTIFIED','complete ineligible trajectory remains NONCERTIFIED')
        summary=dict(schema=SCHEMA,verified=True,complete=certificate_check is not None,
            status='FINITE_CONE_INFEASIBLE'if certificate_check else outcome['status'],certificate_verified=certificate_check is not None,
            finite_augmented_cone_infeasibility_certified=certificate_check is not None,certificate_check=certificate_check,
            numerical_trajectory_replayed=False,numerical_scores_verified=False,original_unlearned_cone_infeasibility_certified=False,
            primal_feasibility_certified=False,**FLAGS)
        data=encoded(summary);b.charge(2*(len(data)//64+1));summary.update(audit_operations=b.operations,audit_cells=b.audit_cells,
            peak_live_cells=b.peak_live_cells,independent_audit_work_reserve=b.operations)
        return summary
    except(OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        raise
