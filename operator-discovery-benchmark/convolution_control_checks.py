"""Independent development checks for the c=mu*lambda signed inverse route.

Algebraic identities and complete finite Gram evaluations are not critical
energy estimates. No production arithmetic or discovery implementation is
imported. Computational limits are explicit; unsupported work is not truncated.
"""
from fractions import Fraction
from math import isqrt


def _positive_integer(n):
    if type(n) is not int or n < 1:
        raise ValueError('positive integer required')


def factor(n):
    _positive_integer(n)
    result={};rest=n
    for p in range(2,isqrt(n)+1):
        while rest%p==0:
            result[p]=result.get(p,0)+1;rest//=p
    if rest>1:result[rest]=result.get(rest,0)+1
    return result


def actual_sequences(N):
    """Actual prime factorization, independent of divisor inversion producers."""
    _positive_integer(N)
    mu=[0];lam=[0];c=[0];h=[0]
    for n in range(1,N+1):
        fs=factor(n);omega=len(fs);total=sum(fs.values())
        sign=(-1)**total;positive=2**omega
        mu.append((-1)**omega if all(k==1 for k in fs.values()) else 0)
        lam.append(sign);c.append(sign*positive);h.append(positive)
    return {'mu':mu,'lambda':lam,'c':c,'h':h,
            'scope':'actual factorized coefficients through N only',
            'critical_energy_estimate_proved':False,'RH_proved':False}


def one_prime_sequences(N,p=2,A=2):
    """Counterfeit local inverse pair: all other prime-power locals vanish."""
    _positive_integer(N);_positive_integer(p)
    if factor(p)!={p:1}:raise ValueError('prime required')
    A=Fraction(A)
    if A<=0:raise ValueError('positive rational amplitude required')
    c=[Fraction(0)]*(N+1);h=c.copy();c[1]=h[1]=Fraction(1)
    power=p;k=1
    while power<=N:
        h[power]=2*A**k;c[power]=2*(-A)**k;power*=p;k+=1
    return {'c':c,'h':h,'prime':p,'amplitude':str(A),'actual_mobius_normalization':False}


def modified_prime_sequences(N,p,A):
    """Actual locals except one changed prime; preserves c=actual_lambda*h."""
    _positive_integer(N);_positive_integer(p)
    if factor(p)!={p:1}:raise ValueError('prime required')
    A=Fraction(A)
    if A<=0:raise ValueError('positive rational amplitude required')
    data=actual_sequences(N);c=[];h=[]
    for n in range(N+1):
        amplitude=Fraction(0) if n==0 else A**factor(n).get(p,0)
        c.append(Fraction(data['c'][n])*amplitude);h.append(Fraction(data['h'][n])*amplitude)
    return {'c':c,'h':h,'lambda':data['lambda'],'prime':p,'amplitude':str(A),
            'matches_actual_below_prime':True,'actual_mobius_normalization':False}


def convolution(a,b,N=None):
    if N is None:N=min(len(a),len(b))-1
    _positive_integer(N)
    if len(a)<=N or len(b)<=N:raise ValueError('complete input prefix required')
    out=[Fraction(0)]*(N+1)
    for n in range(1,N+1):
        out[n]=sum((Fraction(a[d])*Fraction(b[n//d]) for d in range(1,n+1) if n%d==0),Fraction(0))
    return out


def signed_involution(f,h,lam):
    """JH on one complete finite divisor-prefix domain."""
    N=len(f)-1
    if len(h)<=N or len(lam)<=N:raise ValueError('complete operator inputs required')
    values=convolution(h,f,N)
    return [Fraction(0)]+[Fraction(lam[n])*values[n] for n in range(1,N+1)]


def prefixes(c):
    if not c or c[0]!=0:raise ValueError('zero sentinel required')
    out=[Fraction(0)]
    for value in c[1:]:out.append(out[-1]+Fraction(value))
    return out


def coefficient_gram(c,h,N):
    """Full squared divisor constraint, with exact dense cross subtraction."""
    _positive_integer(N)
    if len(c)<=N or len(h)<=N:raise ValueError('complete prefix required')
    full=diagonal=Fraction(0);operations=0
    for n in range(1,N+1):
        terms=[Fraction(c[d])*Fraction(h[n//d]) for d in range(1,n+1) if n%d==0]
        full+=sum(terms,Fraction(0))**2;diagonal+=sum((v*v for v in terms),Fraction(0));operations+=len(terms)
    return {'full':full,'diagonal':diagonal,'signed_cross':full-diagonal,
            'complete_dense_cross_retained':True,'product_terms_evaluated':operations,
            'cross_method':'exact square expansion, not absolute values or projected pairs'}


def prefix_gram_profile(c,h,X,max_terms=2000000):
    """Both full block Grams with fixed all-positive-prefix scale program.

    Cross subtraction is exact: (sum v)^2-sum v^2 retains every ordered
    offdiagonal product without an O(X^3) pair materialization.
    """
    _positive_integer(X);_positive_integer(max_terms)
    N=4*X-1
    if len(c)<=N or len(h)<=N:raise ValueError('complete prefix through 4X-1 required')
    work=sum(range(X,4*X))
    if work>max_terms:return {'status':'missing','reason':'complete_gram_term_budget','requested_terms':work,'max_terms':max_terms}
    C=prefixes(c)
    def block(Y):
        full=diag=energy=Fraction(0)
        for n in range(Y,2*Y):
            terms=[Fraction(h[d])*C[n//d] for d in range(1,n+1)]
            full+=sum(terms,Fraction(0))**2;diag+=sum((v*v for v in terms),Fraction(0));energy+=C[n]**2
        return {'full':full,'diagonal':diag,'signed_cross':full-diag,'C_energy':energy,'other_diagonal':diag-energy,
                'potential':(diag-energy)/(Y*Y)}
    parent=block(X);child=block(2*X)
    delta={k:child[k]-4*parent[k] for k in ('full','diagonal','signed_cross','C_energy','other_diagonal')}
    return {'status':'available','X':X,'parent':parent,'child':child,'delta':delta,
        'potential_innovation':child['diagonal']/(4*X*X)-parent['diagonal']/(X*X),
        'complete_dense_cross_retained':True,'requested_terms':work,'max_terms':max_terms,
        'critical_energy_estimate_proved':False,'RH_proved':False}


def dyadic_one_prime_energy(K):
    """Exact p=A=2 countermodel energy on X=2^K."""
    if type(K) is not int or K<0:raise ValueError('nonnegative integer required')
    X=2**K;C=Fraction(4*(-2)**K-1,3);child_C=-2*C-1
    return {'X':X,'prefix':C,'energy':X*C*C,
            'defect':2*X*child_C*child_C-4*X*C*C,
            'actual_mobius_normalization':False,'refutes_actual_mobius_claim':False}


ANALYTICAL_ASSESSMENT = r"""
All statements concern a new post-discovery analytical proposal. Exact algebra
is proved; no actual critical signed estimate or RH is proved.

One-prime counterfeit. On powers of2 let h(2^k)=2*2^k,
c(2^k)=2*(-2)^k for k>=1, h(1)=c(1)=1; other values vanish.
The local formal generating functions are h(z)=(1+2z)/(1-2z) and
c(z)=(1-2z)/(1+2z). Their product is1 and h=|c|. With actual completely
multiplicative lambda, c(n)=lambda(n)h(n) and JHJ=H^{-1}, (JH)^2=I.
For X=2^K the prefix is C(X)=(4*(-2)^K-1)/3 and is constant throughout
[X,2X). Thus A_C(X)=X*(4*(-1)^K*X-1)^2/9, genuine cubic energy.
Writing C_K=C(X), C_(K+1)=-2C_K-1 gives
Delta_C(X)=X*(4C_K^2+8C_K+2), asymptotic (64/9)X^3.
For every epsilon<1 this violates any finite independent-of-X upper
constant times X^(2+epsilon). Positivity/inversion/involution and the
complete Gram identities therefore do not force critical energy.
This is not actual mu: its arithmetic prime local normalizations fail.

Finite-prefix-matching counterfeit. Given any finite N choose prime P>N.
Keep every other actual Euler local and change only at P to
h(P^k)=2 A^k, c(P^k)=2(-A)^k, A>sqrt(P). Extend multiplicatively.
Then c(n)=lambda(n)h(n), c*h=Unit, h=|c|, and the involution all hold globally;
every coefficient below P matches the actual c,h. The matched finite
prefix cannot distinguish this counterfeit. At P, reconstruction
mu_fake=c*mu_actual^2 gives mu_fake(P)=1-2A, exposing the missing actual
prime normalization (A=1 is the actual local amplitude).

It really violates critical energy, not merely a heuristic growth model.
Its Dirichlet function, initially in an absolute-convergence right half-plane,
is
 F_fake(s)=zeta(2s)/zeta(s)^2
           * (1-A P^(-s))/(1+A P^(-s))
           * (1+P^(-s))/(1-P^(-s)).
Let beta=log(A)/log(P)>1/2, s0=beta+i*pi/log(P). Then P^(-s0)=-1/A:
the added denominator vanishes, and its other numerator/denominator factors
are nonzero. zeta(2s0) is nonzero by its absolutely convergent Euler product,
since Re(2s0)>1. zeta(s) is meromorphic with its only pole at1, so it is
finite at this nonreal s0. If it is nonzero the new factor supplies a pole;
if it vanishes it supplies still more pole order, never cancellation.
Thus F_fake has a genuine pole at s0. If dyadic C-energy satisfied
A_C(X)<=K_epsilon X^(2+epsilon) with epsilon<2beta-1, dyadic
Cauchy-Schwarz would give absolute locally uniform convergence of
s integral_1^infinity C(floor x) x^(-s-1)dx on
Re(s)>1/2+epsilon/2, continuing F_fake analytically through s0, contradiction.
In particular A=P works (beta=1, every epsilon<1). The argument needs no
assumed zero-free result for zeta on Re(s)=1. It uses actual other Euler
locals only to show this counterfeit agrees with arbitrary finite actual
prefixes; it never disproves an actual Mobius claim.

Complete prefix Gram and potential. Put S_diag(X)=sum_(d>=1)h(d)^2
sum_(X<=n<2X) C(floor(n/d))^2 and S_cross=2 sum_(d<e)h(d)h(e)
sum_(X<=n<2X) C(floor(n/d))C(floor(n/e)); all terms with d>2X-1 vanish.
The inverse identity gives S_diag+S_cross=X exactly. The term d=1 is
A_C(X); V(X)=(S_diag(X)-A_C(X))/X^2 is nonnegative, with V(1)=0.
But its proposed Lyapunov innovation is exactly
 E_C(2X)+V(2X)-E_C(X)-V(X)
 =-1/(2X)-[S_cross(2X)-4S_cross(X)]/(4X^2).
A bound <=Cq ceil(X^(1/q)) is therefore equivalent to the unproved lower
bound Delta_cross>=-4Cq X^2 ceil(X^(1/q))-2X, with no terms dropped.
The total S_cross is always nonpositive, but its innovation has no forced
sign, and the counterfeit makes this proposed estimate false. This is a
concrete, testable actual signed arithmetic forcing family, not a proof by
renaming the complete energy. Its cofinal premise would telescope to a
critical C-energy estimate and then RH via zeta(2s)/zeta(s)^2, but the
premise remains unknown.

Actual-only easy envelope and normalization costs. For actual h=2^omega,
h<=d(n) implies |C(t)|<=t(1+log t). Also
sum_(d>=1)h(d)^2/d^2=product_p (1+4/(p^2-1))
<=exp(sum_(n>=2)4/(n^2-1))=exp(3)<27.
Hence S_diag(X)<=108 X^3(1+log(2X))^2. The natural X^2 potential has only
an unconditional O(X log^2 X) bound, not a globally subpower bound from this
calculation. Dividing the other diagonal by X^3 instead gives a nonnegative
O(log^2 X) potential, but breaks the exact E_C+V=S_diag/X^2 normalization;
its innovation still contains the unproved ordinary C defect. Denominator
changes must not be described as supplying critical control.

Development-only exact actual measurements (X,E_C,V,innovation):
1: 1,0,9/2; 2: 5/2,3,21/4; 4: 3/4,10,79/16;
8: 1,235/16,675/64; 16: 51/32,1577/64,927/64;
32: 287/128,4925/128,5415/256;
64: 1529/512,30149/512,117887/4096;
128: 2609/512,350439/4096,39289/1024.
These use actual factorization through511, complete row squares and exact
cross subtraction. They are not a frozen validation split, parameter fit,
all-scale success or evidence that the displayed innovation stays small.
The new generic search should retain inverse/character operator relations,
fixed scale programs and full cross forcing, with these counterfeits as
negative controls; actual prime-local admission is essential.
"""
