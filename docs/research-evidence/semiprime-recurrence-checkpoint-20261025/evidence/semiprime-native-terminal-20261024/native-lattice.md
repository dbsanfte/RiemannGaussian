# Native congruences: primitive small-root lattice audit

24 October2026. Scratch only. This report audits the actual quadratic native congruence. The separate `cubic-cover.md` develops the new degree-three real-weight construction. No small-root theorem below supplies a soft-k factorization of the entire continuing family. The excluded applications are specific sufficient guarantees, not lower bounds on lattice algorithms.

## Input and prior credit

N=PQ, P<Q, k=Theta(N^(1/6)), H=k², P>16H, P<=sqrt N<=k³, Q<H²/16. For a unit tag1<=j<k put q0=[N j^-1]_k and

    a=[N j^-2]_k, d_j=(N-a j²)/k,
    b=center_k(-d_j j^-1), ell=k b-2a j.

At the own tag P=j modulo k, the exact acquired native relation is

    aP+Q+ell=H I.

The parity-repaired variant replaces a by a'<2k and b,ell accordingly; all identities below survive that substitution. The authoritative native proof is `../semiprime-zero-query-20261024/native-pairing.md`, SHA256 `06548c974c61d9922a4ec6c2f41ba1c95d7dfcbb92442b3b2e5ceff984cd8016`.

Duplicate check: the preserved journal near lines34020--34085 and34210--34258 already audits shaped Coppersmith bounds for Lehman multiplier/carry charts, primitive content, and heuristic resultant independence. Those are different polynomials; their general cautions and old lattice methods are credited. No new method is claimed merely from rewriting the native discriminant.

## 1. Remove the EXACT factor k before measuring height

Write P=j+kx,Q=q0+ky and c=(j q0-N)/k. The actual integer equation is

    f(x,y)=kxy+q0 x+j y+c=0.                      (1)

The unnormalized product equation has content exactly k: after division the coefficients include k and the unit tag j, so gcd of all coefficients is1. The affine change to PQ-N proves irreducibility over Q, and the primitive polynomial is therefore irreducible over Z.

Use public dyadic P boxes S<=P<2S, with S between constant multiples of N^(1/3) and sqrt N; constants and the finite prefix cause no exponent change. Safe root bounds are X=O(S/k),Y=O(N/(Sk)). They satisfy

    XY=Theta(N/k²),
    W=max |[x^i y^h]f| X^i Y^h=Theta(N/k).         (2)

In particular the constant c already has size Theta(N/k). Taking W=N instead would retain a removed content factor and invalidate the application.

Coppersmith's proved bivariate integer bound with individual degree delta=1 requires XY<W^(2/3), with the usual slack/constant treatment. On (2) this is equivalent at exponent scale to

    N/k² < (N/k)^(2/3), or k>N^(1/4).             (3)

The native k=N^(1/6) does not meet it. The tempting unnormalized bound XY<N^(2/3) would incorrectly suggest a one-sixth threshold; (3) shows exactly why that inference fails. This rejects this theorem invocation, not successful short vectors outside the guarantee.

## 2. Native derivative cancellation yields a second exact content

Let s0=(a j+q0+ell)/k, an actual integer. The weighted-sum relation gives

    y=k I-a x-s0.

Substituting into the PRIMITIVE equation (1) gives another factor k:

    f(x,kI-a x-s0)=k*g(x,I),
    g(x,I)=(j+kx)I-a x²-b x-c_j,
    c_j=(d_j+j b)/k.                             (4)

All divisions are exact. In detail q0-a j-k s0=-k b and c-j s0=-k c_j. The coefficients of g again have content1 because gcd(j,k)=1. It is irreducible over Q: its I-coefficient j+kx cannot divide the x-only quadratic, whose evaluation at x=-j/k equals N/k², not0.

Equation(4) is the strongest straightforward native coordinate reduction here. It does not reveal an additional residue of P modulo H. Reducing the original product equation modulo H already gives

    y=-a x-s0 modulo k.

Thus the integrality of I is exactly the existing PQ=N modulo k² constraint in these coordinates. Equivalently the Hensel quadratic has a double root modulo k² and imposes P=j modulo k, not an acquired choice of P modulo k².

For X=O(S/k) and the actual index bound

    Y_I=O((aS+N/S)/k²+1),

the weighted height is W_g=Theta((N+aS²)/k²), and XY_I=Theta((N+aS²)/k³), on the growing branch (with harmless constant enlargements). The polynomial g has TOTAL degree TWO, not three: its mixed term is xI. The separate-degree(delta=2) bound requires XY_I<W_g^(1/3); the stronger total-degree2 bound requires XY_I<const*W_g^(1/2). Even the latter fails, since XY_I/sqrt(W_g)=Theta(sqrt(N+aS²)/k²)>=Theta(sqrt(N)/k²)=Theta(N^(1/6)). This does not rule out a better shaped lattice, additional small parameters or a different integer coordinate chart. The own-tag relation has not, by itself, supplied another independent equation.

## 3. Fully explicit unknown-factor univariate lattice

For comparison execute the degree-one unknown-divisor construction, including its determinant. Since gcd(k,N)=1, set f0(X)=X+j k^-1 modulo N. At the own tag x0=(P-j)/k is a root modulo the UNKNOWN divisor P. In a public P box take P>=N^beta with known lower beta, and X a safe bound for |x0|. Constants in the box can be absorbed by slightly enlarging X or a few subboxes.

For integers t>=1,s>=1, dimension d=t+s, use rows corresponding to

    N^(t-i) f0(X)^i,              0<=i<t,
    X^l f0(X)^t,                 0<=l<s,

with coefficient column n scaled by X_bound^n. Choose the monic integer representative f0; basis degrees are0,...,d-1 and its exact determinant is

    det L=N^[t(t+1)/2] X_bound^[d(d-1)/2].         (5)

Every lattice polynomial vanishes modulo P^t at x0. Standard LLL supplies a nonzero row of norm at most2^[(d-1)/4](det L)^(1/d). The elementary norm certificate

    sqrt(d)*2^[(d-1)/4]*(det L)^(1/d) < N^(beta t) (6)

forces its value at x0 to be zero as an INTEGER. Integer root isolation followed by gcd(N,j+kx) certifies every candidate; it does not assume the unknown factor or a field oracle. For fixed exponent slack, t,s are constants depending on that slack, all entries have O(log N) bits, and each tag/box lattice and certified root extraction have polylogarithmic bit cost. Processing O(k) tags and logarithmically many size boxes would therefore fit soft k IF its certificate held.

To optimize (6), write X_bound=N^xi and theta=t/d. Ignoring vanishing finite-dimension/slack terms, its necessary determinant-guarantee inequality is

    xi < 2 beta theta-theta² <= beta².            (7)

Even at finite d, ignoring the positive norm/LLL penalties, the determinant inequality necessarily requires xi<[2 beta t d-t(t+1)]/[d(d-1)]<=((beta d-1/2)^2)/(d(d-1))=beta²+[beta²-beta+1/(4d)]/(d-1)<beta² for d>=2 and beta in[1/3,1/2]. Thus finite dimension does not improve this certificate. The native unknown coordinate has xi=beta-1/6+o(1), while beta is in[1/3,1/2]+o(1). Throughout that interval beta(1-beta)>=2/9>1/6, so xi>beta² by a fixed exponent gap. Increasing lattice dimension does not make THIS determinant certificate meet the native bound. This is a theorem/certificate audit, not a statement that LLL cannot occasionally find a useful polynomial.

Guessing additional quotient intervals can shrink X to a certified range, but those guesses must be paid for every tag; they are not supplied by a,ell. Likewise the residue k² suggested by derivative cancellation cannot be substituted for k in x0 without an actual acquisition of the missing lift.

## 4. Primary contracts and independence

Don Coppersmith, *Finding a Small Root of a Bivariate Integer Equation; Factoring with High Bits Known*, EUROCRYPT1996: [primary paper scan](https://static.aminer.org/pdf/PDF/000/192/858/finding_a_small_root_of_a_bivariate_integer_equation_factoring.pdf). Its opening theorem/bound uses an irreducible integer polynomial, separate degree delta and weighted coefficient height W, giving XY<W^(2/(3delta)). The constants/slack do not repair a fixed exponent failure in (3). The cached scan was inspected as an image because it has no text layer. The later paper is identified at [IBM's primary publication page](https://research.ibm.com/publications/small-solutions-to-polynomial-equations-and-low-exponent-rsa-vulnerabilities); no secondary abstract is used to strengthen the theorem.

Nick Howgrave-Graham, *Computational Mathematics Inspired by RSA*,1998 thesis, Chapter4, [primary thesis](https://cr.yp.to/bib/1998/howgrave-graham.pdf). Its small-norm integer-vanishing argument underlies (6); equations(5)--(7) here explicitly derive the unknown-divisor specialization rather than importing a full-modulus theorem with P replaced by N. The construction is univariate, so a single nonzero integer polynomial permits deterministic candidate isolation. No multivariate independence hypothesis is hidden in that step.

Ellen Jochemsz and Alexander May, *A Strategy for Finding Roots of Multivariate Polynomials with New Applications in Attacking RSA Variants*, ASIACRYPT2006: [primary IACR paper](https://www.iacr.org/archive/asiacrypt2006/42840270/42840270.pdf), [author primary copy](https://www.cits.ruhr-uni-bochum.de/imperia/md/content/may/paper/jochemszmay.pdf). The modular strategy explicitly requires its resultant/nonzero-independence Assumption1 for multivariate extraction. A favorable determinant for auxiliary relations does not prove that condition on these native roots. Boneh--Durfee-style modular secret-exponent relations likewise require their actual equation/modulus hypotheses; the native weighted sum is not a hidden RSA private exponent relation. No such heuristic is counted as all-input coverage here. The primary web text was inspected; direct PDF downloads failed and no local PDF fingerprint is claimed for it.

## Scoped conclusion

The exact primitive bilinear height is N/k. Substituting the native weighted relation removes a SECOND factor k but raises the coordinate degrees; it is not another block of known prime bits. The explicit dimension/determinant/norm certificate of the univariate unknown-factor lattice also misses the native full boxes. These facts do not close the one-sixth goal, and they do not prove a general lattice obstruction. The separate cubic-cover report tests a different construction: fixed-dimensional real-weight lattice approximation plus a proved factor-covering product, not heuristic multivariate root isolation.

Cache pins: `sources/coppersmith-bivariate-1996.pdf` SHA256 `cd5c115a45f5d219faea843d373271934292f017dc059f22e6be99340cebb737`; `sources/howgrave-graham-thesis-1998.pdf` SHA256 `82779caf391a140f10d4272f887288eb8a1d5436437a17bb944abed5a8631984`. The Coppersmith first-page raster is retained for the inspected bound. No repository/source edits or numerical examples were used.
