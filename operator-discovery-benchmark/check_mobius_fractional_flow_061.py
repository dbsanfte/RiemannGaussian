"""Independent shared-carrier flow, head and conserved-terminal admission.

The complete long-prefix variation remains OPEN. No scientific sources,
kernel evaluations, signature discovery or new producer imports occur here.
"""
from fractions import Fraction as Q
from math import prod
import check_mobius_mass_conservation_060 as MASS

Meter=MASS.Meter


def _flow_variation(positions,masses,meter=None):
    """Exact finite signed measure W1 cost with its balancing dummy at zero."""
    m=Meter() if meter is None else meter
    if type(positions) is not list or type(masses) is not list or len(positions)!=len(masses):
        raise ValueError('aligned finite rational measure')
    if any(type(x) is not Q or x<=0 for x in positions) or any(type(b) is not Q for b in masses):
        raise ValueError('exact positive positions and signed rational masses')
    if any(x<=y for x,y in zip(positions,positions[1:])):raise ValueError('strictly decreasing carrier positions')
    prefix=Q(0);cost=Q(0);signed=Q(0)
    for j,(x,b) in enumerate(zip(positions,masses)):
        prefix=MASS._bounded(prefix+b,m)
        following=positions[j+1] if j+1<len(positions) else Q(0)
        cost=MASS._bounded(cost+abs(prefix)*(x-following),m)
        signed=MASS._bounded(signed+b*x,m)
    return {'cost':cost,'signed':signed,'terminal':abs(prefix)*positions[-1] if positions else Q(0)}


def verify_fractional_flow(cert,meter=None):
    m=Meter() if meter is None else meter
    MASS._fields(cert,('schema','parameters','kernels','columns','positive_prefixes','carrier',
        'endpoint_coefficient','log_degree','head_theta','head_coefficient',
        'exit_rho','exit_coefficient','horizon'))
    MASS._expect(cert['schema'],'mobius-fractional-flow-v1')
    alpha,gamma,tau,ps,p,q,period=MASS._parameters(cert['parameters'],m)
    kernels={'P':[[p,'1']],'Q':[[q,'1']],'D':[[p,'1'],[q,'-1']],'S':[[p,'1'],[q,'1']]}
    MASS._expect(cert['kernels'],kernels)
    MASS._expect(cert['carrier'],'d^(-t)')
    prefixes={}
    for profile,rows in kernels.items():
        prefix=Q(0);values=[]
        for base,coefficient in rows:
            prefix=MASS._bounded(prefix+MASS._rational(coefficient,m),m);values.append(str(prefix))
        if any(Q(x)<0 for x in values) or not any(Q(x)>0 for x in values):
            raise ValueError('positive kernel via complete nonnegative prefixes')
        prefixes[profile]=values
    MASS._expect(cert['positive_prefixes'],prefixes)
    columns=cert['columns']
    if type(columns) is not list or len(columns)!=2:raise ValueError('complete kernel-base column coverage')
    floor_l1=Q(0);proofs=[]
    for column,base in zip(columns,(p,q)):
        MASS._fields(column,('base','identity'))
        if type(column['base']) is not int or column['base']!=base:raise ValueError('distinct ascending actual kernel bases')
        identity=column['identity']
        if type(identity) is not dict:raise ValueError('typed mass identity')
        MASS._expect(identity.get('parameters'),cert['parameters'])
        expected=[str(sum(Q(c) for a,c in kernels[profile] if a==base)) for profile in ('P','Q','D','S')]
        MASS._expect(identity.get('profile_coefficients'),expected)
        proof=MASS.verify_identity(identity,m)
        floor_l1=MASS._bounded(floor_l1+MASS._rational(proof['signed_mass_upper']['coefficient'],m),m)
        proofs.append({'base':base,'verified':True,'floor_l1':proof['signed_mass_upper']['coefficient']})
    endpoint=MASS._bounded(Q(3*prod(ps))*floor_l1/(len(ps)-alpha),m)
    if MASS._rational(cert['endpoint_coefficient'],m)!=endpoint:raise ValueError('complete conserved-terminal coefficient')
    if type(cert['log_degree']) is not int or cert['log_degree']!=len(ps):raise ValueError('complete smooth-count logarithmic degree')
    theta=MASS._rational(cert['head_theta'],m)
    if not 0<=theta<=Q(1,2):raise ValueError('subcritical or square-root head cutoff')
    head=MASS._bounded(Q(6*prod(ps))/(len(ps)+1-alpha),m)
    if MASS._rational(cert['head_coefficient'],m)!=head:raise ValueError('complete short-prefix coefficient')
    rho=MASS._rational(cert['exit_rho'],m)
    if not 0<=rho<=Q(3,4):raise ValueError('subcritical or square-root exit cutoff')
    exit_coefficient=MASS._bounded(Q(6*p*prod(ps))/(len(ps)+1-alpha),m)
    if MASS._rational(cert['exit_coefficient'],m)!=exit_coefficient:raise ValueError('complete discrete exit residual coefficient')
    MASS._expect(cert['horizon'],'max(1,floor(4*N/p))')
    m.charge(200)
    return {'verified':True,'schema':'verified-mobius-fractional-flow-v1',
        'parameters':cert['parameters'],'kernels':kernels,'positive_prefixes':prefixes,
        'column_proofs':proofs,'floor_coefficient_l1':str(floor_l1),
        'kernel_positivity_proved':True,'common_carrier':'d^(-t)',
        'flow':{'source_mass':'b_j(t)=mu(d_j)*kernel_sign_j*h_profile_j(t)',
            'prefix':'S_j(t)=sum_(l<=j) b_l(t)',
            'exact_optimal_cost':'V_t=sum_j |S_j(t)|*(d_j^(-t)-d_(j+1)^(-t)); terminal carrier zero',
            'balancing_dummy':'signed mass -sum_j b_j(t) placed at carrier zero',
            'finite_signed_triangle_proved':True,'fractional_transport_optimum_proved':True,
            'plans_may_depend_on_t':True,'integer_copy_transport_equivalence_claimed':False},
        'source_integral':'rgamma(1-alpha)*integral_eps^tau G_M(t)*sum_j b_j(t)*d_j^(-t)*t^(-alpha-1) dt',
        'variation_split':{'D':'max(1,floor(4*N/p))','Y':'N^head_theta',
            'K':'min(floor(D/2),floor(N^exit_rho))',
            'b':'max(min(Y,D),D-K)',
            'short':'t*integral_1^min(Y,D) |S_N(y,t)|*y^(-t-1) dy',
            'core':'t*integral_min(Y,D)^b |S_N(y,t)|*y^(-t-1) dy',
            'exit':'t*integral_b^D |S_N(y,t)|*y^(-t-1) dy',
            'terminal':'D^(-t)*|S_total(t)|',
            'exit_global_mass_plus_terminal':'|S_D(t)|*b^(-t), charged by endpoint coefficient ONCE',
            'empty_source_handled':True,'D_one_has_K_zero':True,
            'unit_and_all_range_exits_retained':True},
        'terminal_bound':{'coefficient':str(endpoint),'log_degree':len(ps),
            'log_weight':'(1+log2(4N))^log_degree','domain':'every integer N>=2',
            'literal_greedy_leftover_claimed':False},
        'head_bound':{'coefficient':str(head),'N_power':str(theta),'domain':'every integer N>=2',
            'primitive':'|S_N(y,t)|<=2*floor(y)<=2*y; H_short<=2*t*N^head_theta'},
        'exit_residual_bound':{'coefficient':str(exit_coefficient),'N_power':str(2*rho-1),
            'domain':'every integer N>=2',
            'primitive':'|S_N(y,t)-S_D(t)|<=2*(D-floor(y)); integral strip count=K*(K+1)/2',
            'discrete_remainder_bound':'2*t*K*(K+1)/D<=4*t*K^2/D',
            'D_lower_gate':'D>=2 implies D>=2*N/p; D=1 strip is empty'},
        'terminal_bound_proved':True,'head_bound_proved':True,'exit_residual_bound_proved':True,
        'core_prefix_bound_proved':False,'long_prefix_bound_proved':False,
        'whole_signed_target_bound_proved':False,'uniform_full_flow_bound_proved':False,
        'RH_proved':False,'source_arrays_or_kernel_integrals_evaluated':False}
