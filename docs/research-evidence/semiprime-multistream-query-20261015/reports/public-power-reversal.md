# Public power masks cannot be reversal-stable collision projectors on the actual source

2026-10-15. New classical actual-source phase analysis. No general computational lower bound or fast projector/query algorithm is claimed.

## Exact contract and result

For a positive public exponent kappa, consider the proposed zero mask

M_kappa(a)=1-a^kappa.

A true field zero indicator equals one at a=0 and zero at a nonzero row value. In particular it is an idempotent collision projector after reduction in each hidden field. This note tests a concrete normalization-stable use of that mask: apply the SAME kappa both to original canonical row products and to their exact finite reciprocal reversals. Those two products have identical zero support and differ by an explicitly known unit.

On the retained actual unit-row family, suppose gcd(kappa,D)=1, where D=ord_N(gamma)>16m^4 is odd. For any 1<=L<=4m^2, among the m-o(m) unit rows, all but at most TWO have at least one of their original/reversed masks fail to be a zero indicator (indeed fail idempotence modulo N). Thus the combined two-orientation mask family has Omega(m) false positives despite the sparse genuine collisions. It cannot be justified as a sparse collision-selective syndrome or intrinsic kernel projector.

This does NOT assert that the mask fails on the canonical normalization alone for every row. Fixing one normalization could accidentally succeed; that would need its own arithmetic theorem. The obstruction rejects a claimed universal or reversal-stable power-indicator interface, not every projector, exponent or factor-only algorithm.

## Exact reversal phase

Let z_j=gamma^(-E_j), E_j=N+delta_j, d=m^2, q=gamma^d, and

a_j=P_L(z_j;q),
b_j=P_L(z_j^(-1)q^(1-L);q).

The standard division-free finite reversal gives

a_j=w_j b_j,
w_j=(-z_j)^L q^(L(L-1)/2)=(-1)^L gamma^(h_j),
h_j=-L E_j+d L(L-1)/2.                               (1)

Only supplied units are inverted in defining the reversed argument. Thus a_j is zero in a hidden field iff b_j is; both are units modulo N on each of the inherited m-o(m) complete unit rows. No collision denominator is canceled.

For any two tags,

h_j-h_k=-L(delta_j-delta_k),
|h_j-h_k|<=4Lm^2<=16m^4<D.                            (2)

The actual low-digit quadratic makes each INTEGER delta occur at most twice. Hence the values gamma^(h_j) have multiplicity at most two globally modulo N: equality lifts (2) to integer equality, and L>0 then gives delta_j=delta_k. This is a global-order argument, not a local orbit-disjointness claim.

If w_j^kappa=1, equation (1) gives

(-1)^(L kappa) gamma^(kappa h_j)=1.

If L kappa is odd, this is impossible because -1 is outside the odd gamma subgroup. If it is even, gcd(kappa,D)=1 forces D dividing h_j. By (2), at most one integer delta class can do this, with at most two tags. Therefore at most two tags satisfy w_j^kappa=1.

On a unit row, if BOTH a_j^kappa=1 and b_j^kappa=1, then w_j^kappa=1. All other unit rows therefore have at least one orientation whose mask is nonzero in some hidden field. Since its powered argument is a unit, that mask is not one in that field either. It lies outside {0,1}, hence is not idempotent there or modulo N. This proves the result, without any distribution hypothesis on the unit row values themselves. The bad field/orientation may vary between rows; no fieldwise dense-error assertion is made.

## Actual public exponent families with gcd(kappa,D)=1

The criterion is not an assumed order oracle. It holds directly for the staged public exponent family

kappa=C_m (N-1)>0,

where C_m is any positive m-SMOOTH integer (all prime divisors <=m), including (m!)^r with arbitrary nonnegative integer r. On the inherited order-qualified prime-pair source, the cross-period exclusions ensure R_P does not divide Q-1 and R_Q does not divide P-1. Since N=Q modulo R_P and N=P modulo R_Q, neither local prime order divides N-1. Both exceed m, so neither divides C_m. Thus kappa is coprime to D on the SAME retained family, with no new deletion. Succinctly staging the m-smooth multiplier does not change this arithmetic failure; no bit-size lower bound is being asserted.

A broader prescribed polynomial family also works after a small explicit deletion. For each possible m prescribe a primitive integer polynomial f_m(T), with coefficients fixed as N varies at that m and degree at most D_*. Let

kappa=C_m f_m(N)>0,

with C_m any positive m-smooth multiplier. The multiplier may even be selected using N; it still has no large prime factor R_P or R_Q. Only f_m must be prescribed independently at fixed m. Primitive means its integer coefficients have gcd one, so it is nonzero modulo EVERY prime R.

Fix an actual admissible P and one possible m. If R_P divides kappa, then R_P divides f_m(N), equivalently f_m(Q), because P=1 modulo R_P. Over F_(R_P), a nonzero polynomial of degree at most D_* has at most D_* roots. In the entire fixed Q bin of length O(M^3), these classes contain at most

O(D_*(M^3/R_P+1))=O(D_*M^.969)

integer Q values. This count needs no selector-strip or short-progression prime-density assumption. There are O(M^3) possible actual P and O(M) possible m in the total candidate range m=Theta(M), so the total input-exception count for ANY candidate is

O((D_*+1)M^4.969).                                    (3)

Switching hidden fields only doubles this bound. It is legitimate to count all m in the range rather than only the first-K selector menu; that stronger union is still small. No extra cofactor sum is needed because R_P is fixed for each actual P. Coefficients of f_m may be large, but primitivity prevents them all vanishing modulo R_P; their acquisition/bit costs are NOT claimed by (3).

For D_*=O(M^.004), equation (3) is O(M^4.973), far below the frozen soft M^5.994 losses. Direct union on the same original qualified supply therefore leaves the majority family where gcd(kappa,D)=1 at every candidate. The unit-row theorem is inherited on that same family. At the constant-degree or polylogarithmic-degree public exponents normally proposed, the deletion is smaller still. Degenerate exponent values zero are not zero-indicator inputs and are outside the positive-exponent contract; they also lie in the counted divisibility exceptions.

This result is not about arbitrary algorithms that compute a complicated N-dependent exponent outside the prescribed polynomial-times-smooth class. It also does not say that knowing an annihilating exponent must have large bit size. The earlier exact-LCM acquisition obstruction is separate and is not reused as proof here.

## Quotient-projector interpretation and remaining positive target

After deduplicating equal source offsets, let H=prod(X-z_j) and g=P_L(X) mod H. The natural finite reversal is multiplication of g by a known unit of R[X]/H, namely the inverse of (-X)^L q^(L(L-1)/2); X is a unit since all source roots are units. The kernel/collision components of multiplication by g do not change under this unit scaling.

If a proposed intrinsic kernel projector is obtained simply as 1-g^kappa, it would need to retain that interpretation under this exact normalization change. The preceding theorem says that, for the stated public kappa families, one of the two orientations fails on almost every unit row. Calling this polynomial a projector, or its trace a collision-only syndrome, is therefore not licensed by public powering and the gamma-order certificate alone.

A projector that normalizes each component by a separately acquired inverse, uses a known full field exponent, applies another polynomial/rational functional, or acquires selective traces directly is not excluded. Such approaches must pay their row/inverse/exponent or implicit-state acquisition. No soft O(m) collision-selective observable was constructed here. This is a concrete arithmetic obstruction to a natural public power-mask route, rather than a generic degree bound for field zero-test polynomials or a claimed impossibility of sparse recovery.
