"""Reject under-normalized pure-prime energies by an imported PNT proof rule.

This is an asymptotic obstruction to an auxiliary energy, NOT a lower bound
on its signed arithmetic residual. No finite threshold is asserted.
"""
from fractions import Fraction as Q

import mobius_residual_fold_077 as F

PNT_REFERENCE='https://people.mpim-bonn.mpg.de/zagier/files/doi/10.2307/2975232/fulltext.pdf'


def canonical_kernel(raw):
    if type(raw) is not list or not 1 <= len(raw) <= 1024:
        raise ValueError('bounded nonempty prefix kernel')
    result={}
    for row in raw:
        if type(row) is not dict or set(row)!={'divisor','weight'}:
            raise ValueError('literal prefix-kernel schema')
        d=row['divisor']
        if type(d) is not int or not 1 <= d <= 1000000:
            raise ValueError('positive bounded fixed divisor')
        a=F.S.B.rational(row['weight'])
        result[d]=result.get(d,Q(0))+a
    return [dict(divisor=d,weight=str(a)) for d,a in sorted(result.items()) if a]


def fixed_kernel(base_kernel,program):
    """Expand only finite constant-coefficient direct dilation operators."""
    base=canonical_kernel(base_kernel)
    F.S.parse_spec(program['spec'])
    if len(program['atoms'])!=len(program['operator']):
        raise ValueError('matched atom/operator dimensions')
    cut=len(program['spec']['theta'])-1
    ds=program['spec']['multipliers']
    result=list(base)
    for atom,raw in zip(program['atoms'],program['operator']):
        a=F.S.B.rational(raw)
        if type(atom) is not dict or set(atom)!={'column','gamma'}:
            raise ValueError('literal source atom')
        column=atom['column']
        g=F.S.B.rational(atom['gamma'])
        if type(column) is not int or not 0<=column<cut+len(ds) or g<0:
            raise ValueError('source atom domain')
        if not a:
            continue
        if column<cut:
            return dict(status='UNSUPPORTED_VARIABLE_PRIME_OPERATOR',kernel=None,
                uniform_energy_obstructed=False,arithmetic_residual_refuted=False)
        d=ds[column-cut]
        result.extend(dict(divisor=d*x['divisor'],weight=str(-a*Q(x['weight']))) for x in base)
    kernel=canonical_kernel(result)
    return dict(status='FIXED_KERNEL_PROPOSAL',kernel=kernel,
        source_binding_still_required=True,arithmetic_residual_refuted=False)


def propose_gate(kernel,excluded_primes,gamma,program,ray_index):
    kernel=canonical_kernel(kernel)
    F.admit_primes(excluded_primes)
    if list(excluded_primes)!=sorted(excluded_primes):raise ValueError('sorted prime exclusions')
    g=F.S.B.rational(gamma);q=F.S.B.rational(program['q'])
    if not 0<g<1 or not 1<=q<2:
        return dict(status='OUTSIDE_ASYMPTOTIC_RULE',uniform_energy_obstructed=False)
    mass=sum((Q(x['weight'])/x['divisor'] for x in kernel),Q(0))
    if not mass:
        return dict(status='UNPAID_ZERO_MASS_LOGARITHMIC_TERMS',uniform_energy_obstructed=False)
    if type(ray_index) is not int or not 0<=ray_index<len(program['rays']):raise ValueError('active ray index')
    ray=program['rays'][ray_index]
    direction=list(map(F.S.B.rational,ray['a']))
    eta=F.S.B.rational(ray['eta']);weight=F.S.B.rational(ray['lambda'])
    if len(direction)!=10 or not direction[1] or any(a for j,a in enumerate(direction) if j!=1):
        return dict(status='COUPLED_RAY_REQUIRES_SIGNED_ANALYSIS',uniform_energy_obstructed=False)
    if eta<0 or weight<=0:raise ValueError('positive square with nonnegative normalization')
    sigma=2-2*eta-q
    if sigma<=0:
        return dict(status='NO_POWER_OBSTRUCTION_FROM_THIS_RULE',uniform_drift_proved=False)
    delta=Q(1)
    for p in excluded_primes:delta*=Q(p-1,p)
    leading=-mass*delta
    certificate=dict(mass=str(mass),delta=str(delta),leading_prime=str(leading),sigma=str(sigma),
        eventual_lower_coefficient=str(weight*(direction[1]*leading)**2/4),ray_index=ray_index)
    return dict(status='PNT_PRIME_MASS_OBSTRUCTION_PROPOSAL',certificate=certificate,
        imported_theorem=dict(name='prime number theorem',statement='pi(x)~x/log(x)',source=PNT_REFERENCE),
        consequence='E(u)/u^q eventually exceeds every constant times log(u)',
        effective_finite_threshold_supplied=False,arithmetic_residual_refuted=False,
        uniform_source_bound_proved=False,RH_proved=False)


def next_search_feedback(candidate,validation_result,gate_admissions):
    """Turn actual failed recurrences into source-bound next search inputs."""
    successful=[g for g in gate_admissions if g.get('status')=='VERIFIED_PRIME_MASS_OBSTRUCTION']
    return dict(schema='signed-rough-drift-feedback-v1',id=candidate['id'],
        source_id=candidate['source_id'],gamma=candidate['gamma'],energy_program=candidate['program'],
        frozen_drift='E(u)/u^q-tau*E(floor(u/2))/floor(u/2)^q <= innovation_C',
        finite_status='REFUTED_FINITE' if validation_result['validation_refuted'] else 'FINITE_ONLY',
        finite_witnesses=validation_result['refutation_witnesses'],
        uniform_energy_obstructions=successful,
        prohibit_if_applicable='nonzero fixed-kernel prime mass with a pure-prime positive square and 2-2*eta>q',
        necessary_prime_square_normalization=str((2-Q(candidate['program']['q']))/2),
        normalization_filter_scope='only fixed finite constant-coefficient kernels with a proved nonzero prime mass; variable prime operators and coupled rays remain unpaid',
        normalization_gate_is_not_a_drift_certificate=True,
        next_state=dict(name='signed scale-change vector',expression='D(u)=V(u)-V(floor(u/2))',
            mandatory_terms=['new outer-shell integers','prime/factor category boundary changes',
                'inherited count tokens at both original parents','all signed prime/composite cross terms']),
        next_lemma='prove a signed quadratic bound on the complete scale-change vector, optionally retaining its correlation with V(floor(u/2))',
        no_circular_replacement='a flux energy equal to the old unpaid drift is not a paid bound',
        retained_obligations=['complete residual-energy base','all-integer parameter-uniform drift',
            'original source correlation','full head/core and RH transfer'],
        arithmetic_residual_refuted=False,uniform_drift_proved=False,RH_proved=False)
