"""Keep full generated-state prefixes and prime profiles distinctly typed."""
from copy import deepcopy
from fractions import Fraction as Q


def _q(value):
    if type(value) is not str or len(value)>2500:
        raise ValueError('bounded canonical rational text')
    result=Q(value)
    if str(result)!=value:
        raise ValueError('canonical rational text')
    return result


def inverse(matrix):
    if type(matrix) is not list or not 1<=len(matrix)<=32:
        raise ValueError('nonempty bounded matrix')
    n=len(matrix)
    if any(type(row) is not list or len(row)!=n for row in matrix):
        raise ValueError('square exact basis')
    a=[[_q(x) for x in row]+[Q(i==j) for j in range(n)] for i,row in enumerate(matrix)]
    for j in range(n):
        pivot=next((k for k in range(j,n) if a[k][j]),None)
        if pivot is None:
            raise ValueError('singular source-state basis')
        a[j],a[pivot]=a[pivot],a[j]
        denominator=a[j][j]
        a[j]=[x/denominator for x in a[j]]
        for i in range(n):
            if i!=j:
                factor=a[i][j]
                a[i]=[x-factor*y for x,y in zip(a[i],a[j])]
    result=[[str(x) for x in row[n:]] for row in a]
    verify_inverse(matrix,result)
    return result


def verify_inverse(matrix,result):
    n=len(matrix)
    if len(result)!=n or any(len(row)!=n for row in result):
        raise ValueError('complete inverse dimensions')
    left=[[_q(x) for x in row] for row in matrix]
    right=[[_q(x) for x in row] for row in result]
    for A,B in ((left,right),(right,left)):
        for i in range(n):
            for j in range(n):
                if sum((A[i][k]*B[k][j] for k in range(n)),Q(0))!=int(i==j):
                    raise ValueError('exact two-sided inverse identity')
    return True


def convert_row(row,basis_inverse):
    """An exact coordinate substitution, not a bound or a prime restriction."""
    if row.get('schema')!='arithmetic-floor-prefix-row-v1' or row.get('prefix_kind')!='weighted_channel':
        raise ValueError('complete weighted-channel prefix relation')
    channel=row['channel']
    if type(channel) is not int or not 0<=channel<len(basis_inverse):
        raise ValueError('declared weighted channel')
    coefficients=[_q(x) for x in basis_inverse[channel]]
    lhs=[]
    for term in row['lhs']:
        for i,c in enumerate(coefficients):
            if c:
                lhs.append(dict(variable=dict(kind='full_generated_state_prefix',state=i,
                                             argument=term['prefix_floor']),
                    scalar=str(c),kernel_argument=term['kernel_argument'],
                    kernel_coefficient=deepcopy(term['coefficient'])))
    return dict(schema='generated-state-floor-constraint-v1',N=row['N'],channel=channel,
                lhs=lhs,rhs=deepcopy(row['rhs']),
                uses_complete_prefixes=True,prime_profile_substitution_permitted=False)


def verify_conversion(row,basis_inverse,converted):
    """Replay the coefficient map, including repeated floors and signed rows."""
    expected=[]
    for term in row['lhs']:
        expected.extend((i,term['prefix_floor'],str(_q(coefficient)),term['kernel_argument'],term['coefficient'])
                        for i,coefficient in enumerate(basis_inverse[row['channel']]) if _q(coefficient))
    if converted.get('schema')!='generated-state-floor-constraint-v1' or converted.get('N')!=row['N'] or converted.get('channel')!=row['channel']:
        raise ValueError('matching relation identity')
    actual=[]
    for t in converted.get('lhs',[]):
        v=t.get('variable',{})
        if v.get('kind')!='full_generated_state_prefix':
            raise ValueError('full arithmetic prefixes cannot become prime profiles')
        actual.append((v.get('state'),v.get('argument'),t.get('scalar'),t.get('kernel_argument'),t.get('kernel_coefficient')))
    if (actual!=expected or converted.get('rhs')!=row['rhs']
            or converted.get('uses_complete_prefixes') is not True
            or converted.get('prime_profile_substitution_permitted') is not False):
        raise ValueError('all signed coefficients, units and floors must be preserved')
    return True


def prime_profile_contract(state):
    if type(state) is not int or state<0:
        raise ValueError('nonnegative generated-state index')
    return dict(kind='explicit_prime_profile',state=state,
        value_below_one='0',
        definition='V_i(1)+sum_(y<p<=t,p prime)(V_i(p)-V_i(p-1))',
        V_kind='full_generated_state_prefix',unit_retained=True,
        all_primes_in_declared_range=True,
        equals_complete_rough_prefix_without_domain_proof=False,
        constraint='V_i(0)=0; V_i(n)-V_i(n-1)=h_i(n) for every integer n>=1')
