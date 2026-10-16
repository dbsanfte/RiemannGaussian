# Can public-index q-binomial duality acquire the actual row products?

2026-10-15. Fresh primary inspection and elementary exact identities. No repository edits/builds, no new fast evaluator and no scalar complexity lower bound.

## Result and a necessary distinction

The selected-index primitive computes terms of ONE common coefficient recurrence at soft O(sqrt(K)+J), where K bounds the queried indices. The q-binomial/Heine/q-Krawtchouk transformations inspected here do not turn the actual arbitrary phases into such public indices for free.

A precise actual-source obstruction excludes the most direct proposal: all coefficients c_0,...,c_L of P_L(Z;q) are UNITS on the qualified long branch, whereas the canonical row query necessarily contains a NONUNIT row value. Therefore a transformation P_L(z_j;q)=v_j c_(k_j) with supplied unit v_j and k_j in [0,L] cannot hold for every actual row. This is an algebraic support obstruction, not discrete-log hardness or a lower bound for arbitrary transforms.

There is an important escape NOT ruled out by that observation: the common coefficient stream may have a huge public top parameter T, while requested indices remain small. The selected-prefix algorithm still has cost controlled by requested horizon K, not T, apart from O(log|T|) powering. Such coefficients can be nonunits. No applicable fixed-T identity of that type was found, and it must not be dismissed by incorrectly charging sqrt(T).

## Exact finite identities and composite-safe domain

Write P_L(Z;q)=prod_(i<L)(1-Z q^i)=sum_(k=0)^L c_k Z^k. Then

    (1-q^(k+1))c_(k+1)=(q^L-q^k)c_k.

For k<=L the denominator prefix is prod_(r=1)^k(1-q^r), and the numerator prefix uses q^L-q^i only for 0<=i<k<=L. Since the actual local q orders exceed L, every factor is a unit, so each c_k is a unit. A known-unit scalar times one such coefficient, or a product/quotient of any number of them and known units, stays a unit. Native forced row coverage rules out computing the full ANY query solely by this multiplicative unit-coefficient selection interface.

The terminating basic hypergeometric representation is exactly

    P_L(z;q)=sum_(k=0)^L (q^(-L);q)_k/(q;q)_k * (z q^L)^k.   (1)

It is just the finite q-binomial theorem. All displayed denominators are units on the long branch, so it is valid over Z/N there, without analytic convergence. It remains a sum of L+1 terms. Multiplying coefficients by z^k changes the whole coefficient stream; reading one coefficient of the resulting polynomial gives c_k z^k, not the sum (1).

For an integer x>=L,

    P_L(q^(-x);q)
      =(-1)^L q^(-x L+L(L-1)/2) (q;q)_L [x choose L]_q.    (2)

This follows by reversing the L numerator factors. The denominator of the Gaussian binomial has only L factors, so (2) can be interpreted via its polynomial definition or the unit denominator (q;q)_L even if x is much larger than the local order. It is wrong to use a ratio of full q-factorials up to x and cancel saturated 0/0 values. Equation(2) yields a coefficient with TOP x and INDEX L; different x_j normally give different streams, not J indices of one fixed stream.

The small requested horizon also works for a huge common top T: define U_k=prod_(i<k)(q^T-q^i), V_k=prod_(i<k)(1-q^(i+1)). For k<=K below every local order, U_k/V_k are exactly the first K q-binomial coefficients of P_T when T>=K. The shared block/refinement algorithm from selected-qbinomial-primitive.md applies with q^L replaced by q^T, costs soft O(sqrt(K)+J+log T), and inverts only V values. U values may vanish, which is permitted. Constructing a fixed public T and public requested indices that encode the actual P_L(z_j) remains the unresolved algebraic step.

## What the q-Krawtchouk duality actually exchanges

Fresh primary: Genest–Post–Vinet–Yu–Zhedanov, *q-Rotations and Krawtchouk polynomials*, arXiv:1408.5292v2, Ramanujan Journal40 (2016),335–357:
https://arxiv.org/abs/1408.5292
PDF/text saved as qrotations-2014.*. Equation22 defines quantum q-Krawtchouk by a terminating 2phi1 at the DISCRETE grid variable q^(-x); equation29 swaps matrix labels n,x after reversal. Equation59 relates quantum and affine families, retaining parameters and normalization factors.

For instance, the exact embedding obtained by taking its degree/grid bound both L is

    K_L^Qtm(q^(-L);p,L;q)=P_L(pq;q).

Thus setting p=z_j/q represents the desired row product, but moves the varying target into a ROW-DEPENDENT PARAMETER p. Degree/index duality does not make that parameter common. Using instead the variable-grid duality requires an actual integer label x_j with z_j=q^(-x_j). No formula in the paper produces that label from an arbitrary supplied field element. The unitary matrix normalizations also include square roots and parameter-dependent q-Pochhammer ratios; unnormalized cleared polynomial identities may specialize, but those normalizations cannot be treated as free known-unit constants over Z/N.

Fresh primary: Genest–Post–Vinet, *An algebraic interpretation of the multivariate q-Krawtchouk polynomials*, arXiv:1508.07770v2:
https://arxiv.org/abs/1508.07770
PDF/text saved as multivariate-qkrawtchouk-2015.*. It derives multivariate polynomial dualities from matrix elements and retains discrete occupation/grid indices. It does not state a soft O(J+sqrt L) sparse finite-ring evaluator or an algorithm constructing unknown q-grid labels. These papers supply identities, not the missing acquisition theorem.

## Actual public phases versus an index label

For z_j=gamma^(-E_j), E_j=N+delta_j and q=gamma^d, the grid-label condition is EXACTLY

    d x_j=E_j mod D,

where D is the actual global gamma order; separately the same congruence holds modulo each hidden order. Since d is coprime to those orders, labels exist, but they are not the ordinary integer quotients floor(E_j/d). The order is not numerically known, and no justified public modular inverse of d modulo D has been supplied. This statement is a missing input contract, not a proof that such labels cannot be found by another method.

For the literal integer equality d x_j=E_j, the actual low-digit formula is

    E_j=N(1-j^(-1))² mod m.

It is zero only at j=1, so ALL other tags fail even divisibility by m, hence cannot admit that literal quotient label. At j=1 the full source lift does make E_1 divisible by d, but x_1=E_1/d is about m^4. This is only one row and does not provide a family-wide common-stream mapping. Large TOP parameters alone are not an obstruction, as noted above; the unresolved part is the common-parameter/public-index identity.

Switching base from q to gamma supplies public integer labels E_j, but changes the step. Completing the missing d residue classes gives

    (z;gamma)_(dL)=prod_(r=0)^(d-1)(z gamma^r;gamma^d)_L.   (3)

This is a product over d~m² rows, not coefficient selection for the original sparse J~m rows. Worse, on the retained source dL~m^4 exceeds both local gamma orders, each at most P-1 or Q-1=O(m³). Since every z_j lies in the gamma subgroup, the full completed gamma progression has a zero in EACH field and hence is globally saturated. Thus blindly replacing the sparse query by (3)'s completed progression loses its collision-localization semantics. This is a concrete failure of that completion, not a lower bound for an implicit sparse multisection formula.

## Other transformations and remaining target

The finite q-binomial theorem and terminating Heine identities are polynomial/rational identities once denominators are cleared; their usual q-grid specializations can be safe when all acquired denominators are units. None inspected here replaces arbitrary source phases by public low indices of one common stream. A Heine transformation that leaves a new terminating sum of length L, or changes a row-dependent parameter, has not improved the clock merely by renaming the sum.

The desired positive advance is an explicit identity with ONE common recurrence, public requested indices of polynomial bit length, cheaply acquired coefficients/unit normalizations, and exact nonunit semantics at every canonical target. The identity must remain valid for target subsets and contiguous interval restrictions. The selected-index primitive already pays that recurrence evaluation if such a bridge is found. No such bridge or nearlinear long-query algorithm was obtained in this investigation.
