# Collective Cauchy specialization: an acquired value and a transverse residue jet

26 October 2026. Scratch paper execution on the actual unique-cover rows. Read frozen clock-phase/{README,knot-phase,symmetric-character}.md and the earlier packed-residue Ward/cavity and torus-query gated-jet reports. **Outcome:** a Hall–Littlewood-type collective product really telescopes across ALL row roots with paid boundary normalization. Its transverse marked first jet retains exactly the desired signed residue (or canonical tag moment). An explicit two-geometric-product execution acquires that jet at the old soft(J+sqrt(Jh)) cost. The cheap specialized value does not determine this transverse jet; the precise surviving term is displayed below. No improved exponent or general lower bound is claimed.

## 1. Finite identity on actual row roots

Let rho=q^-1, x_(j,i)=T_j*rho^i, 0<=i<h, J<=K/3, and introduce the PHYSICAL additive regularizer delta. Write a=1+delta. Define the rational function

    K_delta(t)=product_(j,i) (a-t*x_(j,i))/(a-x_(j,i)).       (1)

For t=q the numerator at i is the denominator at i-1, so the entire double product reduces EXACTLY to

    K_delta(q)=product_j (a-q*T_j)/(a-T_j*rho^(h-1)).       (2)

No division by an unclassified numerical leaf is used: (1)–(2) hold first as rational identities with delta indeterminate and then as cleared polynomial identities. The actual row roots, normalization and finite endpoints all remain present. This is not the infinite Cauchy expansion evaluated illegally at units.

Primary context: [Warnaar, Hall–Littlewood functions and the A2 Rogers–Ramanujan identities, §2 equations (2.5)–(2.8)](https://people.smp.uq.edu.au/OleWarnaar/pubs/A2-Hall-Littlewood.pdf) states the Hall–Littlewood Cauchy product and its principal specializations. Here the finite alphabet is X_j=T_j/a, Y_i=rho^i, and the symmetric-function parameter is t. Its formal partition sum need not terminate in total partition size even with finite alphabets. Only the elementary finite product (1) and its directly proved specialization (2) are used as finite-ring algorithms.

Before numerical use, screen all 2J endpoints 1-qT_j and 1-T_j*rho^(h-1). Proper gcds factor; saturated actual labelled leaves use the existing mixed-relation decoder or supplied root/tag consumer. The added -1 clock endpoint has short nonzero native labels and its own decoder; it is not silently certified from coverage. On continuation all endpoint values are global units. This costs soft K once. At the correct field the surviving unique original hit therefore has 0<=I<=h-2. Set kappa=K_0(q); (2) acquires kappa and its inverse in soft K. K_delta(q) is regular and a unit at delta=0 in every component.

Thus ALL-row unmarked normalization has genuinely been acquired, rather than retained as a symbolic norm.

## 2. A marked transverse jet retains the collision

Mark the numerator at index i by

    t_i=q+epsilon*s_i,
    s_i=(-1)^(i-1).

Use these t_i in (1), calling the result K_delta(epsilon). Every source coefficient is explicit. Differentiation of the rational identity BEFORE any specialization gives

    (partial_epsilon K_delta)(0)
      =-K_delta(q) * sum_(j,i) s_i*x_(j,i)/(a-q*x_(j,i)).   (3)

At the good hit the only singular term on the right is i=I+1, since q*x_(j,I+1)=1. Its numerator is q^-1 and s_(I+1)=(-1)^I. Consequently the exact componentwise Laurent identity is

    Res_delta (partial_epsilon K_delta)(0)
          =-kappa*q^-1*(-1)^I.                          (4)

The acquired unit -kappa/q removes the entire long common cofactor. This normalization is explicit, independent of the unknown hit, and has been endpoint-gated. No conversion of a multiple pole or assumption about a delta-inverse in the base ring is made. Wrong bins still require norm/coordinate validation and bounded continuation.

For a canonical ROW mark use instead t_(j,i)=q+epsilon*u_j. The same calculation gives

    Res_delta (partial_epsilon K_delta)(0)
          =-kappa*q^-1*u_hit.                           (5)

Thus this collective specialization supports either the signed-clock target or the tag-moment target; it does not confuse them. Equations (3)–(5) are an explicit specialization of the already credited Ward/marked-product principle, not a new general residue theorem. Their useful extra feature here is that the unmarked value kappa is an acquired boundary product across every row.

## 3. Execute the transverse jet, with all remaining inputs charged

For the signed mark, even i have t_i=q-epsilon and odd i have t_i=q+epsilon. Split the numerator into precisely TWO finite geometric products with base rho²:

    i=2s:   a-(q-epsilon)*T_j*(rho²)^s,
    i=2s+1: a-(q+epsilon)*T_j*rho*(rho²)^s.               (6)

Their lengths are ceil(h/2) and floor(h/2); these are literal finite ranges, not extended products with a discarded tail. The denominator similarly splits into the corresponding unmarked products. All starts, epsilon-linear marks, row polynomials and endpoints are acquired in soft J. Delta and epsilon are formal deformation variables; denominator inversion is performed only in the componentwise Laurent calculation, not by declaring every original leaf a numerical unit.

An executable WEAK-readout baseline is to acquire each parity group's physical product and its first additive jets by the inherited block engine. Gate the product value first: a global unit skips an empty group, a proper norm gcd factors, and a saturated value permits its first-jet denominator gate. In the correct bin the unique-hit group has a nonzero good first derivative, so its actual norm gate factors or licenses the constant-sign ratio. The other group either factors or skips on a no-factor continuation. This acquires the signed readout in (4), and the row-marked variant acquires (5) projectively after its own first-jet gate. It does NOT claim that a quotient of two singular truncated jets computes every component's exact Laurent coefficient. The fixed jet dimension and degree-O(J) polynomial input give

    soft(J+sqrt(Jh)) plus once-only soft K recovery.      (7)

The row-tag version uses the same engine with explicit u_j source coefficients. Multiplication by the acquired unit in (4) or (5) converts the useful good-component readout to the displayed normalization. This is an initialized sufficient-output algorithm with bounded wrong-bin validation, not a claim that a singular quotient is numerically inverted without classification. At native J=O(K),h=O(K^1.5), its worst-case cost remains soft(K^1.25).

The key failed shortcut is now precise: differentiating the ACQUIRED principal-specialization value (2) follows the tangent t=q with the clock ratio tied to it. It computes a different derivative and cancels the interior source. The transverse deformation in (3) holds the native clock fixed. Its surviving data are

    sum_(j,i) s_i*T_j*rho^i/(1+delta-q*T_j*rho^i),       (8)

or its u_j-marked counterpart. No formula in the cited principal specialization supplies (8). Even for a single common t, a known specialized value is not a supplied partial derivative with respect to t. With alternating or row-dependent t_i it is not the ordinary one-parameter Hall–Littlewood Cauchy kernel at all.

Clearing denominators gives a completely finite polynomial version: partial_epsilon product_(j,i)(a-t_i*x_(j,i)) is a marked leave-one-out sum. The degree in an unrestricted common t can be Jh; this observation describes this implementation's data, not a lower bound on selected derivatives. Finite-alphabet Schur/Hall–Littlewood expansions do not make a partition list or its marked normal derivative free. The previously audited root-system and Schur-boundary packets retain their prior credit.

## Conclusion

This candidate passes a stronger cancellation test than an identity that becomes 0=0 at every collision: its unmarked specialization is acquired from certified unit boundaries, and its marked normal jet provably retains the original residue with a known unit amplitude. Its remaining acquisition is the explicit finite transverse sum (8). The current two-GP/constant-jet execution does not improve the rate. A genuinely faster algorithm for this normal jet, rather than the already cheap specialized value or an uninitialized partition sum, would give the desired shortcut.

## Addendum: execute the small tangent-difference system

There is a genuinely short coefficient q-difference system for the Cauchy product as a function of the COMMON numerator parameter t. Direct finite cancellation gives

    K_delta(qt)/K_delta(t)
       = product_j(a-t*q*T_j)/(a-t*T_j*q^(1-h)).       (9)

Thus its rational coefficient has degree J and is acquired in soft J. The value K_delta(q) is the known boundary expression (2). Differentiating (9) yields a scalar first-order q-difference equation for U(t)=partial_t log K_delta(t), with an acquired degree-O(J) rational forcing. It relates q*U(qt)-U(t); a known VALUE of K at q is not an initial value of U there. In particular it does not produce the transverse alternating derivative in (3). The common-parameter derivative's good residue is merely -q^-1, independent of I; its cheap collision information is the count, not the alternating phase.

The distinction can be executed more sharply for h=2m, using the actual polynomial

    E_delta(t)=product_(j,s=0..m-1)(a-t*T_j*q^(-2s)).

Then the numerator of K_delta(q) is E_delta(q)*E_delta(1), whereas the alternating marked numerator is E_delta(q-epsilon)*E_delta(1+epsilon/q). For V(t)=E_delta'(t)/E_delta(t), the desired normalized first derivative is

    -V(q)+q^-1 V(1).                                (10)

Both the common-parameter sum and the desired difference have their correct chain-rule factors. Finite cancellation also supplies

    E_delta(q²t)/E_delta(t)
      =product_j(a-t*q²*T_j)/(a-t*T_j*q^(-2(m-1))),

and hence an acquired-forcing equation for q²V(q²t)-V(t). These are O(J)-coefficient equations, not an acquired O(J)-cost solution. Their missing initial datum is the relative logarithmic derivative between t=1 and t=q in (10). The already acquired product E(q)E(1) does not give either derivative; after differentiation its tangent supplies a sum, while (10) needs the difference. The numerator factors are actual degree-Jm polynomials and their endpoint data are supplied, but no short initial condition evaluating (10) follows from these equations.

For odd h, splitting off the last even-clock factor adds one acquired degree-J value and logarithmic derivative after its endpoint gate; the same two half-clock functions and the same relative-derivative requirement remain. Second mixed derivatives do not remove the requirement automatically: before any singular specialization, product differentiation introduces V(1)V(q) and their derivatives. At the unique good pole the two first-residue amplitudes have sum fixed by the count and product zero because only one parity hits; selecting which of the two is nonzero is exactly the absent phase. This is a statement about the information supplied by this particular tangent system, not a counterexample to algorithms using all native roots.

Therefore this finite tangent construction has paid coefficient data and a paid scalar VALUE seed, but not the logarithmic-derivative seed needed for the normal jet. Executing the half-clock products by the inherited engine pays that seed at soft(J+sqrt(Jh)), as in §3. A new algorithm solving (9)–(10) at those selected points from the short coefficient data could still improve acquisition; the present calculation neither initializes such an algorithm nor rules one out.

## Final finite test: Macdonald row shifts with the clock side collapsed

A stronger collective action really is acquired. Take the finite type-II kernel

    Psi(X,Y)=product_(j,i)(X_j-Y_i),
    X_j=T_j, Y_i=q^i, 0<=i<h.

For the first Macdonald operator with BOTH parameters q, put

    c_j=product_(k!=j)(qT_j-T_k)/(T_j-T_k)
       =D(qT_j)/((q-1)T_j D'(T_j)).

Gate row differences before using this expression: D'(T_j) values are acquired by MPE, and a nonunit localizes to actual row aliases; after literal duplicate labels are removed, those aliases have nonzero mixed labels and use the existing decoder. All required T_j, q-1 are units. This gives c_j in soft K on continuation. It is not permissible to invert D'(T_j) just because the final good hit is simple; other row collisions must actually be gated.

The row-shift ratio at the geometric clock has only two endpoints:

    Psi(T_1,...,qT_j,...;Y)/Psi(T;Y)
       =q^h*(T_j-q^-1)/(T_j-q^(h-1)).                (11)

The endpoint gates above therefore acquire every ratio in soft K. In particular the full collective relative action S_X=sum_j c_j times (11) is paid soft K, despite the unacquired kernel value.

The finite kernel identity supplies a useful independent simplification. On the Y alphabet, every Macdonald coefficient except its last vanishes, because its numerator contains qY_i-Y_(i+1). The surviving coefficient is [h]_q=(q^h-1)/(q-1). Consequently the exact rational identity is

    S_X + [h]_q*D(q^h)/D(q^(h-1)) = [J+h]_q.        (12)

It follows by dividing the polynomial type-II identity

    (q-1)(D_X+D_Y)Psi=(q^(J+h)-1)Psi

on its regular universal locus and clearing before specialization. The only newly evaluated point is D(q^h); denominators still use the screened last endpoint. q^h and [h]_q themselves are acquired by exponentiation, not by emitting h terms. Formula (12) can also be derived by partial fractions from the supplied D. Thus this is an ACTUAL soft-K all-row correlated operator action, with a finite kernel and no partition list.

Primary source: [Noumi, Kernel functions for Koornwinder’s q-difference operators, page 2](https://www.maths.gla.ac.uk/island/island3/talks/noumi.pdf) states the first Macdonald operator and the finite type-II kernel identity; its finite product is separate from its infinite type-I kernel. The current derivation uses only that polynomial identity and explicitly gated rational specializations. The older finite-root-system/Macdonald audits retain prior credit; the new test here is the fully acquired GP-clock collapse (12) against the requested normal jet.

The requested transverse derivative still does not follow from this acquired relative action. At an interior hit, shifting ONE row by q leaves its clock hit inside the interval (the hit index increments by one); all relevant endpoint factors are units. Hence (11) is regular at that collision: the operator action multiplies the unresolved zero by acquired scalars. For uniform moving-root deformation, c_j are scale invariant, and differentiating the already finite identity gives

    (D_X Psi_t)'|_1 = S_X(1)*Psi_t'|_1

at the good zero; the known derivative of S_X is multiplied by Psi_1=0. The nonzero cofactor Psi_t' remains unknown, so this tangent yields a known multiplier, not a seed.

For the alternating source, the issue is explicit rather than merely dimensional. A row shift sends the internal clock mark (-1)^i to its opposite after reindexing; its endpoint corrections are acquired, but it flips the active-row normal contribution. The differentiated row sum therefore contains the selected diagonal term c_(j*) times the corresponding unit endpoint ratio, multiplied by the still-unacquired cofactor/normal amplitude. Differentiating the dual clock operator does not avoid it: previously zero interior coefficients acquire first derivatives, and their clock-shifted kernels are precisely the leave-one-out factors at the possible hit. They are not the unshifted zero kernel, nor paid boundary values. This is the uncancelled object of this candidate.

Thus (12) is a concrete jointly acquired operation, stronger than an unspecified operator descriptor. Its differentiated version has not supplied a normal initial condition or phase. No general statement that all Macdonald insertions fail is inferred; a source-specific finite identity acquiring those selected leave-one-out amplitudes would be a genuine next improvement.
