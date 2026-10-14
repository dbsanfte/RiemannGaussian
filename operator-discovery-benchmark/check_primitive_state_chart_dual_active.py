"""Independent active-face accounting and optional original Farkas admission.

Reported correlations, CG steps and residual rankings are numerical
diagnostics. No trajectory or score is independently replayed here.
"""
import time
import check_primitive_state_chart_dual_coordinate as REUSE
import primitive_state_chart_dual_active_protocol as PROTOCOL

DIRECT=REUSE.DIRECT
GEOMETRY=REUSE.GEOMETRY
require=REUSE.require
encoded=REUSE.encoded
finite=REUSE.finite
scope=REUSE.scope
ordered=REUSE.ordered
Budget=REUSE.Budget
FLAGS=dict(PROTOCOL.FLAGS)
SCHEMA='primitive-state-chart-dual-active-independent-check-v1'
NUMERICAL_SCHEMA='primitive-state-chart-dual-active-proposal-v1'
OUTCOME_SCHEMA='primitive-state-chart-dual-active-search-v1'
METRIC='diagonal column curvature, unit step'


def _full_work(m,n,z,b):
    b.charge(20);require(all(type(q)is int for q in(m,n,z))and 1<=m<=443 and 1<=n<=851 and n<=z<=m*n,'bounded sparse full source')
    setup=12*z+64*(m+n)+65536;gradient=8*z+32*(m+n)+512
    face_setup=8*z+48*(m+n)+1024;cg=12*z+64*(m+n)+1024
    commit=8*z+48*(m+n)+1024;final=12*z+64*(m+n)+2048;limit=min(128,2*n)
    reserve=gradient+face_setup+limit*cg+commit
    return dict(setup=setup,gradient=gradient,face_setup_full=face_setup,cg_step_full=cg,commit=commit,final=final,
                cg_limit_full=limit,max_faces=1000,iteration_reserve=reserve,minimum_attempt=setup+reserve+final)


def _face_work(m,k,z,b):
    b.charge(8)
    return dict(setup=8*z+48*(m+k)+1024,cg_step=12*z+64*(m+k)+1024,cg_limit=min(128,2*k))


def _vector(value,n,label,b):
    require(type(value)is list and len(value)==n and all(finite(q,nonnegative=True)for q in value),'full finite nonnegative '+label)
    b.charge(3*n);return [j for j,q in enumerate(value)if q>0]


def verify_numerical(numerical,rows,columns,nnz,budget,*,column_nonzeros,initial_vector=None):
    b=budget;scope(numerical)
    require(numerical.get('schema')==NUMERICAL_SCHEMA and type(numerical.get('complete'))is bool
            and type(numerical.get('attempted'))is bool,'explicit active-set proposal disposition')
    for key,value in (('rows',rows),('columns',columns),('nonzeros',nnz)):
        require(type(numerical.get(key))is int and numerical[key]==value,'actual sparse model '+key)
    require(type(column_nonzeros)is list and len(column_nonzeros)==columns
            and all(type(q)is int and 1<=q<=rows for q in column_nonzeros)and sum(column_nonzeros)==nnz,'actual source column sparsity')
    b.charge(3*columns);work=_full_work(rows,columns,nnz,b)
    reported=numerical.get('work_model');require(type(reported)is dict and reported==work
            and all(type(q)is int for q in reported.values()),'independent full-source work model')
    cap=numerical.get('max_operations');require(type(cap)is int and 0<cap<=190000000,'bounded numerical allocation')
    setup=numerical.get('setup_charged');final=numerical.get('final_charged');gradients=numerical.get('gradient_blocks')
    require(type(setup)is bool and type(final)is bool and type(gradients)is int and gradients>=0,'explicit charged full blocks')
    expected_initial=[0.0]*columns if initial_vector is None else initial_vector
    initial_support=_vector(expected_initial,columns,'bound initial vector',b)
    initial=numerical.get('initial_vector');diagonal=numerical.get('metric_diagonal')
    if initial is not None:
        _vector(initial,columns,'saved initial vector',b);require(initial==expected_initial,'saved complete initial vector bound to seed or zeros')
    if diagonal is not None:
        require(type(diagonal)is list and len(diagonal)==columns and all(finite(q)and q>0 for q in diagonal),'full positive finite diagonal metric');b.charge(3*columns)
    faces=numerical.get('faces');checkpoints=numerical.get('checkpoints')
    require(type(faces)is list and len(faces)<=1000 and type(checkpoints)is list and len(checkpoints)<=1001,'bounded face and checkpoint prefixes')
    require(not checkpoints or(initial is not None and diagonal is not None and setup),'initial checkpoint follows complete setup')
    require(not(faces or gradients)or checkpoints,'every face gradient follows initial checkpoint')
    cumulative=work['setup']if setup else 0;support=initial_support;support_at={0:initial_support};eligible=[]
    def checkpoint(record,index,expected_support,charge):
        b.charge(18);require(type(record)is dict and type(record.get('iteration'))is int and record['iteration']==index
            and type(record.get('support_size'))is int and record['support_size']==len(expected_support)
            and finite(record.get('residual_norm'),nonnegative=True)and finite(record.get('relative_residual'),nonnegative=True)
            and type(record.get('cumulative_operations'))is int and record['cumulative_operations']==charge,
            'ordered checkpoint support and exact cumulative work')
        if 1<=len(expected_support)<=443:eligible.append((record['relative_residual'],len(expected_support),index))
    if checkpoints:checkpoint(checkpoints[0],0,support,cumulative)
    committed=0;partial=False;last_damped=False;last_cg=None;face_cells=0
    for index,face in enumerate(faces,1):
        b.charge(36);require(type(face)is dict and type(face.get('iteration'))is int and face['iteration']==index,'ordered1-based face records')
        require(not partial and committed==index-1,'at most one final incomplete face')
        require(checkpoints[committed]['residual_norm']>0
                and last_cg!='zero_curvature','no gradient follows earlier zero residual or Krylov breakdown')
        require(cumulative+work['iteration_reserve']+work['final']<=cap,'every face start reserves worst full-source solve and final')
        mode='initial_face'if index==1 and support else'refine_face'if last_damped and support else'enter_column'
        require(face.get('mode')==mode,'prescribed initial, refine or entry face transition')
        active=ordered(face.get('active'),set(range(columns)),b,'active face positions')
        face_cells+=24+len(active)
        if mode=='enter_column':
            entry=face.get('entered');require(type(entry)is int and 0<=entry<columns and entry not in support
                and finite(face.get('entry_score'))and face['entry_score']>0 and active==sorted(support+[entry]),'exactly one inactive positive-score entry')
        else:require(face.get('entered')is None and face.get('entry_score')is None and active==support,'unchanged initial or damped surviving face')
        z=sum(column_nonzeros[j]for j in active);fw=_face_work(rows,len(active),z,b)
        require(active and type(face.get('nonzeros'))is int and face['nonzeros']==z
            and type(face.get('cg_limit'))is int and face['cg_limit']==fw['cg_limit'],'face sparsity and CG cap from actual active columns')
        face_setup=face.get('setup_charged');commit=face.get('commit_charged');complete=face.get('complete')
        blocks=face.get('cg_blocks');completed=face.get('cg_steps_completed');cg_stop=face.get('cg_stop')
        require(type(face_setup)is bool and type(commit)is bool and type(complete)is bool
            and type(blocks)is int and type(completed)is int and 0<=completed<=blocks<=fw['cg_limit'],'bounded charged/completed face blocks')
        require(cg_stop in(None,'zero_normal_residual','zero_curvature','iteration_limit'),'known reported CG stop')
        if cg_stop=='zero_curvature':require(blocks==completed+1,'zero curvature consumes one unsuccessful charged CG attempt')
        elif cg_stop=='iteration_limit':require(blocks==completed==fw['cg_limit'],'CG iteration cap reached exactly')
        elif cg_stop=='zero_normal_residual':require(blocks==completed,'zero normal residual follows full completed updates')
        else:require(not complete and blocks-completed<=1,'incomplete CG has only one interrupted attempt')
        require(face_setup or(not blocks and not completed and not commit and cg_stop is None),'face setup precedes every CG/commit block')
        require(not commit or cg_stop is not None,'commit follows a normal bounded CG stop')
        cumulative+=work['gradient']+int(face_setup)*fw['setup']+blocks*fw['cg_step']+int(commit)*work['commit']
        face_cumulative=face.get('cumulative_operations')
        if face_cumulative is not None:require(type(face_cumulative)is int and face_cumulative==cumulative,'face cumulative work including partial blocks')
        if complete:
            require(face_setup and commit and face_cumulative is not None,'complete face includes setup, CG disposition and commit')
            damped=face.get('damped');fraction=face.get('step_fraction');require(type(damped)is bool
                and finite(fraction,nonnegative=True)and fraction<=1,'finite nonnegative boundary interpolation')
            hits=ordered(face.get('boundary_hits'),set(active),b,'boundary minimizers')
            survivors=ordered(face.get('surviving_support'),set(active)-set(hits),b,'all surviving positive face positions')
            face_cells+=len(hits)+len(survivors)
            if damped:require(hits,'damped face explicitly removes all reported boundary minimizers')
            else:require(fraction==1 and not hits and survivors==active,'undamped face preserves every active positive coordinate')
            committed+=1;support=survivors;support_at[index]=survivors;last_damped=damped;last_cg=cg_stop
            require(len(checkpoints)>index,'each completed face has its checkpoint')
            checkpoint(checkpoints[index],index,support,cumulative)
        else:
            partial=True
            require(not commit or face_setup,'partial commit follows face setup')
            # Values already saved before a failed commit remain finite, but
            # cannot serve as a surviving support or accepted checkpoint.
            if face.get('damped')is not None:require(type(face['damped'])is bool,'partial damping flag')
            if face.get('step_fraction')is not None:require(finite(face['step_fraction'],nonnegative=True)and face['step_fraction']<=1,'partial finite interpolation')
            for key in ('boundary_hits','surviving_support'):
                if face.get(key)is not None:ordered(face[key],set(active),b,'partial '+key)
    require(len(checkpoints)==(committed+1 if checkpoints else 0),'only initial and complete-face checkpoints are saved')
    require(len(faces)<=gradients<=len(faces)+1,'one gradient per face and at most one terminal/interrupted gradient')
    extra=gradients-len(faces)
    if extra:
        require(not partial and committed<1000 and checkpoints and checkpoints[-1]['residual_norm']>0
            and last_cg!='zero_curvature'and cumulative+work['iteration_reserve']+work['final']<=cap,
            'extra terminal/interrupted gradient obeys full start guard and stop priority')
        cumulative+=work['gradient']
    operations=cumulative+int(final)*work['final'];counts=numerical.get('counts')
    require(type(counts)is dict and type(counts.get('operations'))is int and counts['operations']==operations and operations<=cap,'exact sum of actual full and per-face charged blocks')
    peak=counts.get('peak_live_cells');require(type(peak)is int and peak>=0 and (peak<=6000000 or(
        not numerical['complete']and type(numerical.get('resource_failure'))is str and numerical['resource_failure'])),'preserved incomplete memory failure')
    bits=counts.get('maximum_rational_bits');require(type(bits)is int and 0<=bits<=4096,'bounded coefficient metadata')
    require(finite(numerical.get('elapsed_seconds'),nonnegative=True),'finite elapsed diagnostic')
    stop=numerical.get('stop_reason');require(stop in(None,'zero_reported_residual','krylov_breakdown','face_limit','work_boundary','no_positive_inactive_correlation'),'known normal stop')
    if numerical['complete']or final or stop is not None:
        require(numerical['attempted']is True and setup and checkpoints and not partial and stop is not None,'normal final diagnostic follows a complete accepted boundary')
        last=checkpoints[-1]
        if last['residual_norm']==0:require(stop=='zero_reported_residual'and not extra,'zero reported residual has immediate stop priority')
        elif last_cg=='zero_curvature':require(stop=='krylov_breakdown'and not extra,'committed curvature breakdown has stop priority')
        elif committed==1000:require(stop=='face_limit'and not extra,'hard committed face limit')
        elif stop=='no_positive_inactive_correlation':
            require(extra==1 and not(committed==0 and support)and not(last_damped and support),'terminal correlation gradient occurs only when an entry is due')
        else:require(stop=='work_boundary'and not extra and cumulative+work['final']+work['iteration_reserve']>cap,'normal bounded work stop with reserved final diagnostic')
    diagnostic=numerical.get('final_diagnostic')
    if numerical['complete']:
        require(final and len(faces)==committed and gradients==committed+(stop=='no_positive_inactive_correlation'), 'complete face and terminal-gradient counters')
        require(type(diagnostic)is dict and type(diagnostic.get('iteration'))is int and diagnostic['iteration']==committed
            and diagnostic.get('mapping_metric')==METRIC and all(finite(diagnostic.get(key),nonnegative=True)for key in(
                'residual_norm','relative_residual','projected_gradient_norm')),'finite final diagonal-metric diagnostic at last committed point')
    else:require(numerical.get('selected')is None and diagnostic is None,'incomplete trajectory cannot select support or publish final diagnostic')
    if not numerical['attempted']:
        require(not numerical['complete']and not setup and not final and not gradients and not faces and not checkpoints
            and initial is None and diagonal is None and cap<work['minimum_attempt'],'unattempted proposal has no setup or iteration work')
    else:require(cap>=work['minimum_attempt'],'initial setup has worst first-iteration and final room')
    if not setup:require(not gradients and not faces and not checkpoints and not final and initial is None and diagonal is None,'setup precedes all initial and subsequent state')
    selected=numerical.get('selected');selected_support=None
    if numerical['complete']and eligible:
        best=min(eligible);require(type(selected)is dict and type(selected.get('iteration'))is int and selected['iteration']==best[2]
            and finite(selected.get('relative_residual'),nonnegative=True)and selected['relative_residual']==best[0],'ranking over reported initial and committed checkpoint diagnostics')
        selected_support=_vector(selected.get('scaled_vector'),columns,'selected vector',b)
        require(ordered(selected.get('support'),set(range(columns)),b,'every selected positive position')==selected_support
            and selected_support==support_at[best[2]],'selected strict support equals saved initial or surviving face support')
        if best[2]==0:require(selected['scaled_vector']==initial,'selected initial point equals the complete bound seed vector')
    else:require(selected is None,'ineligible or incomplete proposal has no selected vector')
    b.live(5*nnz+32*columns+16*rows+face_cells+10*len(checkpoints))
    return dict(complete=numerical['complete'],selected_support=selected_support,numerical_trajectory_replayed=False,numerical_scores_verified=False)


def _seed_vector(seed,n,b):
    if seed is None:return None
    require(type(seed)is dict and seed.get('schema')=='primitive-state-chart-dual-coordinate-search-v1','fixed032 seed proposal schema')
    numerical=seed.get('numerical');require(type(numerical)is dict and numerical.get('schema')=='primitive-state-chart-dual-coordinate-proposal-v1'
        and numerical.get('complete')is True,'complete032 numerical seed, without imported score')
    selected=numerical.get('selected');require(type(selected)is dict,'saved complete selected seed vector')
    vector=selected.get('scaled_vector');_vector(vector,n,'archived seed vector',b)
    data=encoded(seed)
    if len(data)>8388608:raise OverflowError('bounded archived warm seed')
    b.charge(2*(len(data)//64+1));b.resident_cells+=len(data);b.live(0)
    return vector


def verify_outcome(chart,chart_review,rays,geometry,reduction,reduction_review,outcome,*,seed=None,deadline=None,
    max_operations=90000000,max_cells=6000000,max_bits=4096,max_certificate_bytes=8388608):
    require(type(max_certificate_bytes)is int and 0<max_certificate_bytes<=8388608,'bounded active proposal')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,max_bits)
    try:
        scope(outcome);require(outcome.get('schema')==OUTCOME_SCHEMA and outcome.get('status')in('CERTIFICATE_PROPOSED','NONCERTIFIED','UNKNOWN')
            and outcome.get('route')=='active_set'and outcome.get('policy')==PROTOCOL.POLICY and outcome.get('limits')==PROTOCOL.LIMITS,'known active-set policy and disposition')
        data=encoded(outcome)
        if len(data)>max_certificate_bytes:raise OverflowError('independent active outcome byte cap')
        b.charge(2*(len(data)//64+1),cells=len(data)//64+1);b.resident_cells+=len(data);b.live(0)
        m,n,nnz,active,row_ids,representatives=REUSE._source(geometry,reduction,reduction_review,b)
        positions={j:k for k,j in enumerate(active)};column_nonzeros=[0]*n
        for record in reduction['final_rows']:
            b.charge(2*len(record['terms'])+1)
            for j,q in record['terms']:column_nonzeros[positions[j]]+=1
        require(sum(column_nonzeros)==nnz,'actual saved source column sparsity');b.charge(n)
        initial=_seed_vector(seed,n,b);numeric=outcome.get('numerical');model_stats=outcome.get('model_stats');proposal=None
        if numeric is not None:
            require(type(model_stats)is dict and model_stats.get('rows')==m and model_stats.get('columns')==n and model_stats.get('nonzeros')==nnz
                and all(type(model_stats.get(key))is int for key in('rows','columns','nonzeros'))and model_stats.get('active_columns')==active
                and model_stats.get('row_ids')==row_ids,'model statistics bound to actual saved reduced equations')
            scaling=model_stats.get('scaling');require(type(scaling)is dict and scaling.get('positive_exact')is True
                and scaling.get('finite_nonunderflowing_conversion')is True,'positive exact scaling and conversion diagnostics')
            for prefix in('row','column'):
                low=b.rational(scaling.get(prefix+'_scale_min'));high=b.rational(scaling.get(prefix+'_scale_max'));require(0<low<=high,'positive exact scaling range')
            proposal=verify_numerical(numeric,m,n,nnz,b,column_nonzeros=column_nonzeros,initial_vector=initial)
        certificate=outcome.get('certificate');certificate_check=None
        if outcome['status']=='CERTIFICATE_PROPOSED':
            require(proposal is not None and proposal['complete']and proposal['selected_support']is not None,'only completed eligible active-set proposal restores exact witness')
            rows,pivots,free,source_cells=DIRECT.parse_chart(chart,chart_review,b)
            require(geometry.get('pivot_columns')==pivots and geometry.get('free_indices')==free,'same licensed original chart partition')
            generators,generator_cells=DIRECT.parse_rays(rays,b);b.live(source_cells+generator_cells+4*1224+4*851)
            certificate_check=GEOMETRY.verify_saved_certificate(certificate,rays,rows,pivots,free,generators,b,max_certificate_bytes=max_certificate_bytes)
            support=[representatives[active[j]]for j in proposal['selected_support']];restoration=outcome.get('restoration_stats')
            require(type(restoration)is dict and restoration.get('support')==support and type(restoration.get('support_size'))is int
                and restoration['support_size']==len(support)and restoration.get('complete')is True and restoration.get('free_rule')=='zero','exact reconstruction binds every selected positive original ray')
            alpha=[b.rational(q)for q in certificate['alpha']];b.charge(3*len(alpha));support_set=set(support)
            free_positions=ordered(restoration.get('free_support_coordinates'),set(range(len(support))),b,'declared free reconstruction positions')
            require(type(restoration.get('rank'))is int and restoration['rank']==len(support)-len(free_positions)
                and all(q==0 for j,q in enumerate(alpha)if j not in support_set)and all(alpha[support[j]]==0 for j in free_positions),'full representative support-only lift with zero free values')
        else:
            require(certificate is None,'unsuccessful active search has no certificate')
            if proposal is None or not proposal['complete']:require(outcome['status']=='UNKNOWN','incomplete active trajectory remains UNKNOWN')
            elif proposal['selected_support']is None:require(outcome['status']=='NONCERTIFIED','complete ineligible trajectory remains NONCERTIFIED')
        summary=dict(schema=SCHEMA,verified=True,complete=certificate_check is not None,
            status='FINITE_CONE_INFEASIBLE'if certificate_check else outcome['status'],certificate_verified=certificate_check is not None,
            finite_augmented_cone_infeasibility_certified=certificate_check is not None,certificate_check=certificate_check,
            numerical_trajectory_replayed=False,numerical_scores_verified=False,original_unlearned_cone_infeasibility_certified=False,
            primal_feasibility_certified=False,**FLAGS)
        payload=encoded(summary);b.charge(2*(len(payload)//64+1));summary.update(audit_operations=b.operations,audit_cells=b.audit_cells,
            peak_live_cells=b.peak_live_cells,independent_audit_work_reserve=b.operations)
        return summary
    except(OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        raise
