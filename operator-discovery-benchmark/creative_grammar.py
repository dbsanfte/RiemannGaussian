"""Typed exploration across arithmetic sequences and prime residue spaces.

Numerical semantics are for discovery. Universal certificates and native
verification are separate artifacts; NumPy matches never constitute a proof.
"""

from dataclasses import dataclass
from math import gcd
import numpy as np

from exact_arithmetic import require_prime

MAP='residue_map'
VECTOR='residue_vector'
SCALAR='complex_scalar'
ARITHMETIC='arithmetic_sequence'


@dataclass(frozen=True)
class Term:
    op: str
    sort: str
    args: tuple=()
    parameter: object=None

    def data(self):
        out={'op':self.op,'sort':self.sort,'args':[a.data() for a in self.args]}
        if self.parameter is not None:out['parameter']=self.parameter
        return out

    @staticmethod
    def read(data):
        return Term(data['op'],data['sort'],tuple(Term.read(a) for a in data.get('args',[])),data.get('parameter'))


def atom(name,sort,parameter=None):return Term(name,sort,(),parameter)


def compose(a,b):
    if a.sort!=MAP or b.sort!=MAP:raise TypeError('Composition requires two residue maps')
    return Term('compose',MAP,(a,b))


def apply(A,f):
    if A.sort!=MAP or f.sort!=VECTOR:raise TypeError('Apply requires a residue map and residue vector')
    return Term('apply',VECTOR,(A,f))


def combine(op,a,b):
    if op not in ('add','subtract','pointwise','scalar_product'):raise ValueError('Unknown binary production')
    if a.sort!=b.sort or a.sort not in (VECTOR,MAP,SCALAR):raise TypeError('Binary production requires matching sorts')
    if op=='pointwise' and a.sort!=VECTOR:raise TypeError('Pointwise product requires vectors')
    if op=='scalar_product' and a.sort!=SCALAR:raise TypeError('Scalar product requires scalars')
    return Term(op,a.sort,(a,b))


def adjoint(A):
    if A.sort!=MAP:raise TypeError('Adjoint requires a residue map')
    return Term('adjoint',MAP,(A,))


def defect(a,b):
    return combine('subtract',compose(a,b),compose(b,a))


def gram(A):return compose(adjoint(A),A)


def embed(arithmetic,cutoff):
    if arithmetic.sort!=ARITHMETIC:raise TypeError('Embedding requires an arithmetic sequence')
    if cutoff<1:raise ValueError('A complete positive cutoff must be declared')
    return Term('embed_mod_prime',VECTOR,(arithmetic,),cutoff)


def primitive_matrix(name,p):
    I=np.eye(p,dtype=complex);x=np.arange(p)
    if name=='I':return I,False
    if name=='F':return np.fft.fft(I,axis=0)/np.sqrt(p),False
    if name=='FI':return np.fft.ifft(I,axis=0)*np.sqrt(p),False
    if name=='INV':return I[[0]+[pow(int(n),-1,p) for n in range(1,p)]],False
    if name=='MASK':I[0]=0;return I,False
    if name=='CONJ':return I,True
    if name=='T':return np.roll(I,1,axis=0),False
    if name=='M':return np.exp(2j*np.pi*x/p)[:,None]*I,False
    if name.startswith('C') and name[1:].isdigit():
        d=int(name[1:]);phase=np.array([pow(int(n),d,p) for n in x])
        return np.exp(2j*np.pi*phase/p)[:,None]*I,False
    raise ValueError('Unknown residue primitive '+name)


def outer(name,values,anti,p):
    """Apply a primitive to matrix rows or a vector, preserving anti-linearity."""
    if name=='F':return np.fft.fft(values,axis=0)/np.sqrt(p),anti
    if name=='FI':return np.fft.ifft(values,axis=0)*np.sqrt(p),anti
    if name=='INV':return values[[0]+[pow(n,-1,p) for n in range(1,p)]].copy(),anti
    if name=='MASK':result=values.copy();result[0]=0;return result,anti
    if name=='CONJ':return values.conjugate(),not anti
    if name=='T':return np.roll(values,1,axis=0),anti
    if name=='M':phase=np.arange(p)
    elif name.startswith('C') and name[1:].isdigit():phase=np.array([pow(n,int(name[1:]),p) for n in range(p)])
    elif name=='I':return values.copy(),anti
    else:raise ValueError('Unknown word primitive '+name)
    factor=np.exp(2j*np.pi*phase/p)
    if values.ndim>1:factor=factor[:,None]
    return factor*values,anti


def word_matrix(word,p):
    require_prime(p);A=np.eye(p,dtype=complex);anti=False
    for name in reversed(word):A,anti=outer(name,A,anti,p)
    return A,anti


def word_term(word):
    result=atom('I',MAP)
    for name in reversed(word):result=compose(atom(name,MAP),result)
    return result


def residue_character(p,order=6,power=1):
    if not isinstance(order,int) or order<1 or (p-1)%order:raise ValueError('Positive character order must divide p-1')
    if p==2:return np.array([0,1],dtype=complex)
    # A generator of F_p^*; the choice of character is part of its data.
    factors=[];m=p-1;q=2
    while q*q<=m:
        if m%q==0:
            factors.append(q)
            while m%q==0:m//=q
        q+=1
    if m>1:factors.append(m)
    generator=next(g for g in range(2,p) if all(pow(g,(p-1)//q,p)!=1 for q in factors))
    values=np.zeros(p,dtype=complex);x=1
    for k in range(p-1):values[x]=np.exp(2j*np.pi*power*k/order);x=x*generator%p
    return values


def validate(term):
    """Reject malformed serialized trees as well as invalid builder calls."""
    if term.sort not in (MAP,VECTOR,SCALAR,ARITHMETIC):raise TypeError('Unknown term sort')
    for arg in term.args:validate(arg)
    if term.op=='input':
        if term.args or term.sort not in (VECTOR,ARITHMETIC,SCALAR):raise TypeError('Invalid input term')
        return
    if term.op in ('compose','add','subtract','pointwise','scalar_product'):
        if len(term.args)!=2:raise TypeError('Binary term needs two arguments')
        a,b=term.args
        required=MAP if term.op=='compose' else VECTOR if term.op=='pointwise' else SCALAR if term.op=='scalar_product' else term.sort
        if required not in (MAP,VECTOR,SCALAR) or term.sort!=required or a.sort!=required or b.sort!=required:raise TypeError('Binary term sort mismatch')
    elif term.op=='apply':
        if len(term.args)!=2 or term.sort!=VECTOR or term.args[0].sort!=MAP or term.args[1].sort!=VECTOR:raise TypeError('Invalid map application')
    elif term.op=='adjoint':
        if len(term.args)!=1 or term.sort!=MAP or term.args[0].sort!=MAP:raise TypeError('Invalid adjoint')
    elif term.op=='embed_mod_prime':
        if len(term.args)!=1 or term.sort!=VECTOR or term.args[0].sort!=ARITHMETIC or not isinstance(term.parameter,int) or term.parameter<1:raise TypeError('Invalid arithmetic embedding')
    elif term.op in ('pointwise_power','weighted_cyclic_product','learned_phase_product'):
        arity=1 if term.op=='pointwise_power' else 2
        if len(term.args)!=arity or term.sort!=VECTOR or any(a.sort!=VECTOR for a in term.args):raise TypeError('Invalid vector production')
        if term.op=='pointwise_power' and (not isinstance(term.parameter,int) or term.parameter<0):raise ValueError('Pointwise power requires a nonnegative integer')
        if term.op=='weighted_cyclic_product' and (not isinstance(term.parameter,(list,tuple)) or len(term.parameter)!=2 or any(not isinstance(n,int) or n<0 for n in term.parameter)):raise ValueError('Phase exponents must be nonnegative integers')
        if term.op=='learned_phase_product':
            if not isinstance(term.parameter,dict):raise ValueError('Learned phase kernel needs coefficient and feature data')
            coefficients=term.parameter.get('coefficients');features=term.parameter.get('monomials')
            if not isinstance(coefficients,(list,tuple)) or not isinstance(features,(list,tuple)) or len(coefficients)!=len(features):raise ValueError('Kernel coefficient/feature size mismatch')
            if any(not isinstance(c,int) for c in coefficients) or any(not isinstance(v,(list,tuple)) or len(v)!=2 or any(not isinstance(n,int) or n<0 for n in v) for v in features):raise ValueError('Kernel coefficients and exponents must be integers; exponents nonnegative')
    elif term.op=='scalar_conjugate':
        if len(term.args)!=1 or term.sort!=SCALAR or term.args[0].sort!=SCALAR:raise TypeError('Invalid scalar conjugate')
    else:
        if term.args:raise TypeError('Unknown non-leaf production '+term.op)
        if term.op in ('I','F','FI','INV','MASK','CONJ','T','M') or (term.op.startswith('C') and term.op[1:].isdigit()):required=MAP
        elif term.op in ('character','constant_one','unit_mask'):required=VECTOR
        elif term.op in ('eisenstein_gauss','eisenstein_character_at','eisenstein_generator','eisenstein_unit_direction','root_of_unity'):required=SCALAR
        else:raise ValueError('Unknown typed primitive '+term.op)
        if term.sort!=required:raise TypeError('Primitive sort mismatch')
        if term.op in ('character','root_of_unity'):
            if not isinstance(term.parameter,(list,tuple)) or len(term.parameter)!=2 or any(not isinstance(n,int) for n in term.parameter) or term.parameter[0]<1:raise ValueError('Character/root-of-unity data need a positive order and integer exponent')
        if term.op in ('eisenstein_gauss','eisenstein_character_at') and not isinstance(term.parameter,int):raise ValueError('Gauss/character parameter must be an integer')


def evaluate(term,p,inputs):
    """Evaluate a typed term at one declared prime; invalid sorts reject."""
    require_prime(p)
    validate(term)
    args=lambda:[evaluate(a,p,inputs) for a in term.args]
    if term.op=='input':
        value=inputs[term.parameter]
        if term.sort==VECTOR:
            value=np.asarray(value,dtype=complex)
            if value.shape!=(p,):raise ValueError('Residue input must have p entries')
        return value
    if term.sort==MAP and not term.args:return primitive_matrix(term.op,p)
    if term.op=='character':return residue_character(p,*term.parameter)
    if term.op in ('eisenstein_gauss','eisenstein_character_at','eisenstein_generator','eisenstein_unit_direction'):
        if term.sort!=SCALAR:raise TypeError('Prime arithmetic scalar has invalid sort')
        if p%6!=1:raise ValueError('This Eisenstein scalar model requires a prime norm congruent to 1 modulo 6')
        from qrh_operator_benchmark import primary,character
        pi=primary(p);chi=character(p,pi)
        if term.op in ('eisenstein_generator','eisenstein_unit_direction'):
            value=complex(pi[0]-pi[1]/2,pi[1]*np.sqrt(3)/2)
            return value/np.sqrt(p) if term.op=='eisenstein_unit_direction' else value
        if term.op=='eisenstein_character_at':
            x=term.parameter%p
            return 0j if x==0 else np.exp(2j*np.pi*chi[x]/6)
        j=term.parameter
        return sum(np.exp(2j*np.pi*((j*chi[x]/6)-pi[1]*x/p)) for x in range(1,p))/np.sqrt(p)
    if term.op=='scalar_conjugate':return complex(args()[0]).conjugate()
    if term.op=='scalar_product':
        a,b=args();return a*b
    if term.op=='root_of_unity':
        if term.sort!=SCALAR:raise TypeError('Root of unity is a scalar')
        order,exponent=term.parameter
        return np.exp(2j*np.pi*exponent/order)
    if term.op=='constant_one':return np.ones(p,dtype=complex)
    if term.op=='unit_mask':return np.array([0]+[1]*(p-1),dtype=complex)
    if term.op=='compose':
        (A,a),(B,b)=args();return A@(B.conjugate() if a else B),a^b
    if term.op=='adjoint':
        A,a=args()[0]
        if a:raise TypeError('Complex Hilbert adjoint is not defined here for anti-linear maps')
        return A.conjugate().T,False
    if term.op=='apply':
        (A,a),v=args();return A@(v.conjugate() if a else v)
    if term.op in ('add','subtract'):
        left,right=args();sign=1 if term.op=='add' else -1
        if term.sort==MAP:
            A,a=left;B,b=right
            if a!=b:raise TypeError('Sum mixes linear and anti-linear maps')
            return A+sign*B,a
        return left+sign*right
    if term.op=='pointwise':
        a,b=args();return a*b
    if term.op=='pointwise_power':return args()[0]**term.parameter
    if term.op=='weighted_cyclic_product':
        f,g=args();a,b=term.parameter;out=np.zeros(p,dtype=complex)
        for x in range(p):
            for y in range(p):out[(x+y)%p]+=np.exp(2j*np.pi*(pow(x,a,p)*pow(y,b,p)%p)/p)*f[x]*g[y]
        return out
    if term.op=='learned_phase_product':
        f,g=args();out=np.zeros(p,dtype=complex)
        coefficients=term.parameter['coefficients'];features=term.parameter['monomials']
        if len(coefficients)!=len(features):raise ValueError('Kernel coefficient/feature size mismatch')
        for x in range(p):
            for y in range(p):
                phase=sum(c*pow(x,a,p)*pow(y,b,p) for c,(a,b) in zip(coefficients,features))%p
                out[(x+y)%p]+=np.exp(2j*np.pi*phase/p)*f[x]*g[y]
        return out
    if term.op=='embed_mod_prime':
        values=args()[0];N=term.parameter
        if len(values)<=N:raise ValueError('Embedding needs every coefficient through its declared cutoff')
        out=np.zeros(p,dtype=complex)
        for n in range(1,N+1):out[n%p]+=complex(values[n])
        return out
    raise ValueError('Unknown typed production '+term.op)


def word_normal_form(word):
    """Sound universal rewrites; deliberately incomplete.

    A failed rewrite is left unproved. Numerical equality cannot add a rule.
    """
    w=list(word);steps=[]
    commuting={'INV':'MASK','MASK':'INV'}
    changed=True
    while changed:
        changed=False
        for i in range(len(w)-1):
            pair=w[i:i+2]
            replacement=None;rule=None
            if pair in (['F','FI'],['FI','F'],['INV','INV'],['CONJ','CONJ']):replacement=[];rule='inverse_or_involution'
            elif pair==['MASK','MASK']:replacement=['MASK'];rule='support_projection'
            elif pair==['MASK','INV']:replacement=['INV','MASK'];rule='inversion_preserves_nonzero_support'
            elif pair[0]=='CONJ' and pair[1] in ('F','FI','INV','MASK','T'):
                name={'F':'FI','FI':'F'}.get(pair[1],pair[1]);replacement=[name,'CONJ'];rule='conjugation_intertwining'
            elif pair[0] in ('C2','C3','C4','M','MASK') and pair[1] in ('C2','C3','C4','M','MASK') and pair[0]>pair[1]:
                replacement=sorted(pair);rule='diagonal_maps_commute'
            if replacement is not None:
                before=list(w);w[i:i+2]=replacement;steps.append({'rule':rule,'before':before,'after':list(w)})
                changed=True;break
        if changed:continue
        for i in range(len(w)-3):
            if w[i:i+4] in (['F']*4,['FI']*4):
                before=list(w);del w[i:i+4];steps.append({'rule':'Fourier_order_four','before':before,'after':list(w)})
                changed=True;break
    return tuple(w),steps


def universal_kloosterman_certificate(word):
    # This certificate comes from generic projection/permutation algebra.
    # It covers every prime, rather than recognizing a finite fingerprint.
    if tuple(word)!=('FI','INV','MASK','F'):return None
    return {'domain':'Every prime p; complex vectors on F_p; zero support retained',
            'definition':'K=F^* I_inv P_nonzero F',
            'proof_steps':['F^*F=FF^*=I by finite additive-character orthogonality',
                           'I_inv^2=I because (x^-1)^-1=x on units, and 0 is fixed',
                           'P_nonzero^2=P_nonzero and I_inv P_nonzero=P_nonzero I_inv',
                           'K^*=K and K^2=F^*P_nonzero F=I-J/p',
                           'K^3=K, kernel is constants, and l2 operator norm is 1'],
            'kernel':'K(a,b)=p^-1 sum_(x!=0) exp(2*pi*i*(a*x-b/x)/p)',
            'written_proof':'creative_grammar_proof.txt section 2',
            'historical_novelty_established':False,'ordinary_zeta_zero_bridge_proved':False,
            'new_uniform_prime_distribution_estimate_proved':False}


def information_gates(certificate=None):
    return {'universal_law':'proved by explicit schema' if certificate else 'unproved',
            'finite_prime_data':'must use fresh primes and all residues, including nonunits',
            'ordinary_zeta_zero_fidelity':'requires a separate bridge to full ordinary zeta',
            'all_scale_prime_information_gain':'requires a new arithmetic observable or estimate',
            'historical_novelty':'unresolved until substantive prior-art comparison',
            'penalize_generic_basis_transport_and_automatic_Gram_positivity':True,
            'nonassociative_operators_allowed':True,'low_rank_defects_allowed':True}


PRODUCTION_CATALOGUE={
    'residue_maps':['F','FI','INV','MASK','CONJ','C2','C3','C4','T','M',
                    'compose','adjoint','add','subtract'],
    'residue_vectors':['input','character','unit_mask','constant_one','apply','pointwise',
                       'pointwise_power','weighted_cyclic_product','learned_phase_product','embed_mod_prime'],
    'scalar_prime_arithmetic':['eisenstein_gauss','eisenstein_character_at','eisenstein_generator',
                               'eisenstein_unit_direction','root_of_unity','scalar_conjugate','scalar_product'],
    'arithmetic_bridge':'embed a complete declared coefficient prefix by its residues; arithmetic input grammar remains available',
    'search_families':['operator words','representation changes','commutators and Gram defects',
                       'nonassociative phase products and their associators','unknown polynomial-kernel synthesis',
                       'Gauss/character scalar conversion',
                       'whole-index prime marks and multiscale compensation'],
    'proof_rules':['finite Fourier orthogonality','permutation/involution','support projection',
                   'diagonal phase unitarity','linear adjoint','exact symbolic phase defect'],
    'global_energy_grammar':'global_moment_grammar.py: even and mixed moments, unknown energy transfers, positive functionals, support and scale-cost certificates',
    'unimplemented_proof_targets':['full cubic-theta reflection','global Hecke-family mean-square bounds',
                                   'a new ordinary-zeta critical-strip prime-information estimate']}
