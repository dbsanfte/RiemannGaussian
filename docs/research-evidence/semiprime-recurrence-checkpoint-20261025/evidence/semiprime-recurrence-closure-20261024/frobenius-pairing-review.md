# Independent review of the aligned quadratic constructor

24 October 2026. Verdict: **PASS**. Exact source reviewed: `/tmp/semiprime-recurrence-closure-20261024/frobenius-pairing.md`, SHA256 `215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`. No source changes requested. This is a paid constructor/recovery improvement, not a faster terminal product or a compression of the earlier full Gauss vectors.

## Constructor and discovery

The discriminant discovery is uniform under the explicitly stated asymptotic convention. Lau--Wu Theorem 1 on printed page 2 of the [primary preprint](https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf) supplies the cubefree-modulus exponent 1/(4 sqrt(e))+epsilon. Taking a fixed epsilon below 5/32 minus that exponent proves success of the bounded scan for all sufficiently large inputs. The Jacobi character of distinct odd semiprime N is primitive and nonprincipal; no prime-modulus substitution is used. The trial-division fallback on the finite exceptional input set is explicitly retained, with no practical/effective threshold asserted. Scan work soft N^(5/32) is below soft N^(1/6).

For N=1 mod4, squarefree-core extraction preserves the negative Jacobi value, and the prescribed negative fundamental D has the same value since (-1/N)=1. The N=3 mod4 case D=-4 is correct. The chosen k is even, divisible by the ACTUAL conductor |D|, and within r+2|D| of r. Thus all chi_D(j) at unit tags are public, nonzero and constant on residue classes modulo k; in particular the own tag has chi_D(j)=(D/P). A factor of k+1 need not be prime: the report correctly abandons that former Gauss-conductor requirement. Public factoring, conductor synchronization and character acquisition fit soft k.

After scalar preparation, 1-D=1+|D| is below each hidden prime, since |D|<=k/2. The explicit Cayley inverse is legal; equivalently Norm(1-tau)=1-D. The algebra is rank-two etale, its field/split classification is correct, and Jacobi(D,N)=-1 forces exactly one unknown nonsplit side. Norm(W)=1 and W^p=W^(chi_D(p)) hold on each local side. No lower order bound for W is inferred.

## All rows and the actual cover

All actual pairs of coordinates V_j are acquired, not supplied as a deferred circuit: constant-rank binary powering costs polylog N per tag and there are at most k tags. Their signed exponents have O(log N) bits. Native metadata requires only inverses at public unit tags. The pinned composite-row contract provides the exact own-index integer and its bound; its proof does not require k prime.

The exponent calculations check exactly. Write e=chi_D(j). At the own P,

    E_j-HI=(P-1)(Q-a_j),
    Texp_j-HI=(P-1)(Q-a_j)       if e=+1,
    Texp_j-HI=-(P+1)(Q+a_j)     if e=-1.

These annihilate beta and W under their actual local orders. Thus V_j=z^I holds as a whole local quadratic-algebra equality, on either possible own side. Keeping every raw tag avoids unsafe delta-only deduplication. Target repeats are legal for the zero-safe monic algorithm and do not require auxiliary separation.

## Seed screen and full cost

The norm of z is beta^(2H). At the unknown field side p*, z^d=1 for d<=16k² would force the odd order of beta^H to divide d, contrary to its paid >16k² guard. Therefore every short-difference norm is nonzero at p*. A nonunit block norm can only give a proper factor, never a saturated obstruction.

The specified b=4k baby polynomial and b giant points cover exactly d=bu+v in 1,...,b², with no missing endpoint or overhang. Its evaluation is a known unit times the block product. Monic product trees and monic multipoint evaluation are valid over B even before their node differences are certified units; no colliding-value division is used. The construction, starts, evaluations, norms and gcds cost soft k. Unit block norms certify every individual short difference on BOTH sides. The later blocked-query sizes are below that certified range (bounded cases may multiply directly), and target separation is not a hidden hypothesis.

The original scalar setup is invoked at the FINAL synchronized k; beta^H is actually screened. It is not inferred from a beta order bound under composite-H powering. Polynomial arithmetic over B has constant overhead, so all rows, guards and target coefficients fit soft k, while the complete long query plus restriction descent retains soft(J+sqrt(JL)). Nothing in the report prices a rank-k operation as scalar or omits conductor discovery, a kernel branch, a giant start or the old bounded decoder.

## Saturated leaves and restrictions

The identity

    beta^(2E_j)-beta^(2Hi)=bar(V_j)*(V_j-z^i)+z^i*bar(V_j-z^i)

and its stated ideal equality are exact. A proper leaf norm gcd is a factor. For a saturated norm LEAF, at the one nonsplit side norm zero implies the whole element is zero, hence its conjugate is zero and the SAME row/index scalar beta condition vanishes there. Its gcd is therefore nontrivial. Proper gives a factor; saturated, together with odd local beta orders, gives the original beta leaf at BOTH primes. The global coprime-order bound and native short-index bounds then give the checked original factor sum. This does not invoke an order certificate for W or z.

For family products, localization precedes this identity. If a saturated parent has no proper child gcd, at least one child is saturated; descend until an original leaf. This handles distinct witness leaves at the two primes without a cross-leaf inference. Every restriction has the same valid factor-or-discard-or-original-witness consumer, and own coverage makes the complete query nonunit. The separate supplied-vector primitive half-GCD discussion is explicitly not a same-leaf family test; its fast guarded execution does not acquire its input and does not enter this constructor's recovery proof.

## Supporting recurrence check after coupling

A further exact scalar recurrence makes the remaining terminal obligation concrete. Let c=Norm(z)=beta^(2H), t=Tr(z), and h_i=Norm(V_j-z^i). In B,

    h_i=Norm(V_j)+c^i-bar(V_j)*z^i-V_j*bar(z)^i.

Thus each actual scalar sequence, including the chi-minus rows, is annihilated by the SAME acquired monic polynomial

    (T-1)(T-c)(T²-t*T+c).

In coordinates this gives

    h_(i+4)=(1+c+t)*h_(i+3)
       -[2c+(1+c)*t]*h_(i+2)
       +c*(1+c+t)*h_(i+1)-c²*h_i.

Coefficients and four starts for every row are acquired in soft k, with no distinct-eigenvalue or division requirement. Individual distant values can consequently be evaluated cheaply. This remains valid when the four spectral values coincide or a leaf is zero. It does not acquire product_(j,i) h_i; directly iterating and multiplying costs soft(JL), and the paid blocked product remains the faster soft(J+sqrt(JL)) completion.

The two-base interpretation agrees: A=beta W, B=bar(A)=beta/W; chi-plus targets are A^E and chi-minus targets are A^ell_j*B^(N+a_j). At a nonsplit own prime p, A^p=B, and ell_j+p*(N+a_j)-HI=Q*(p²-1). This verifies Frobenius alignment, but P is proof-side and cannot be inserted into the acquired two-base exponents. No smaller initialized interval-product rule is supplied by this interpretation or by the common order-four recurrence.

The report's positive claim and its terminal limitation are both correct. It closes the uniform useful-leaf recovery gap for this new rank-two constructor, with all preparation and guards paid; it does not prove a soft-k full query or improve the factoring exponent.
