# Formal weighted q-binomial query: two explicit holonomic interfaces and their cost

2026-10-15. No faster evaluator was obtained. The substantive results are (i) an actual-family regular-start order bound for common arbitrary-weight recurrences, (ii) a concrete quadratic-size obstruction to materializing the natural scalar closure operator, and (iii) an exact residue-sector analysis of a 2026 polynomial-reduction route. These do not exclude structured implicit high-order propagation or horizon-specific algorithms. No repository edits/builds.

Write P_n(z)=prod_(t<n)(1-z q^t), F_n(w)=sum_j w_j P_n(z_j). The requested weighted inner product at n=L equals F_L, because the finite q-binomial expansion gives P_L(z)=sum_k c_k z^k. All identities below preserve weights formally, not merely numerically.

## 1. Actual-family lower bound on common recurrence order

Fix either hidden field on the retained source supply. Let D be the number of distinct z_j=gamma^(-N-delta_j). The native offset bound is -3m²<=delta_j<=m² and the local order R>16m². Therefore distinct INTEGER offsets yield distinct field targets: their difference has magnitude at most 4m²<R.

The original slope is a_j=N j^(-2) modulo m, and delta_j=a_j+m b_j-2a_j j. Thus a low digit c=delta_j mod m satisfies

    c j²+2Nj-N=0 mod m.

This polynomial is nonzero, even when c=0, because N is a unit modulo the odd prime m. Each low digit, hence each integer offset and each distinct target, has at most two tags. Consequently D>=ceil((m-1)/2) IN EACH hidden field.

Suppose a WEIGHT-INDEPENDENT scalar recurrence

    sum_(k=0)^r A_k(n) F_(n+k)(w)=0

is an identity in the formal weights, and is regular at n=0 with coefficient vector (A_0(0),...,A_r(0)) not identically zero in the chosen field. Comparing each weight coefficient at n=0 gives

    Q(z_j)=0,
    Q(Z)=sum_(k=0)^r A_k(0) prod_(t<k)(1-q^t Z).

The Newton polynomials have distinct degrees and unit leading coefficients, so Q is nonzero of degree at most r. It has D distinct roots, hence r>=D=Omega(m). More generally at a regular n, dividing the active rows by nonzero P_n(z_j) gives the same argument for the number of active distinct targets, with q replaced in the initial scale by q^n.

SINGULAR STARTS MATTER: multiplying an operator by a factor vanishing at n=0 can make every coefficient zero there; no bound is claimed from that point. Nor does this apply to operators whose coefficients depend on the formal weights, or to nonlinear/state-space/horizon-only methods. This is not the previous generic constant-state obstruction: it is a fieldwise statement on the actual targets for a specified common scalar-recurrence interface.

## 2. Exact order-J recurrence with unit leading coefficient

Let H(Z)=prod_j(Z-z_j)=sum_(i=0)^J h_i Z^i, h_J=1, and define B_k(Y)=prod_(t<k)(1-q^t Y). Expand

    Y^i=sum_(k=0)^i beta_(i,k) B_k(Y).

This basis conversion uses only powers of the known unit q: from

    Y B_k(Y)=q^(-k)(B_k(Y)-B_(k+1)(Y))

one obtains the beta coefficients without dividing by differences or residuals. Put

    a_k(x)=sum_(i=k)^J h_i beta_(i,k) x^(J-i).

Then, division-free over any commutative ring with q a unit,

    x^J H(Z)=sum_(k=0)^J a_k(x) B_k(xZ).

Substituting x=q^n,Z=z_j, multiplying by w_jP_n(z_j), and summing gives

    sum_(k=0)^J a_k(q^n) F_(n+k)(w)=0.         (1)

Here deg a_k<=J-k and a_J=(-1)^J q^(-J(J-1)/2), a known unit. Thus this common recurrence has no collision-residual inversion in its leading step. The beta table and coefficient arrays can be constructed directly in O(J²) ring operations and O(J²) stored residues using the displayed triangular recurrence. This is a real ring-safe interface, but is not yet a fast long-horizon algorithm.

The natural dense coefficient table has

    sum_(k=0)^J (J-k+1)=(J+1)(J+2)/2

slots. These are generically all nonzero. More specifically,

    beta_(i,k)=(-1)^k q^(-k(k-1)/2)
              h_(i-k)(1,q^(-1),...,q^(-k)),

where the last h denotes a COMPLETE homogeneous symmetric polynomial, not a coefficient of H. This is nonzero over characteristic zero. For the actual exponent-grid SYMBOLIC model q=gamma^(m²), z_j=gamma^(-N-delta_j), gamma indeterminate, each coefficient h_i of H is a signed positive Laurent polynomial in gamma. The beta factor also has one fixed sign and positive Laurent coefficients. Thus every displayed x coefficient is nonzero in that symbolic model too.

Therefore a method that FIRST materializes this natural scalar closure operator as explicit coefficient arrays pays Omega(J²) residue slots/time, already beyond soft O(m). Conventional fixed-width modular storage costs Omega(J² log N) bits for those arrays; ring-operation upper bounds multiply by the corresponding O(log N)-bit modular-arithmetic cost. This is an output-contract obstruction, not a lower bound on implicit recurrence construction/evaluation: the table has a short implicit description through H and the q-Newton transform, and numerical modular cancellations may occur. A different minimal operator representation could also be more compact.

Using a generic dense order-J matrix-factorial algorithm additionally pays the growing matrix dimension, rather than treating fixed-order headlines as uniform in J. Initial values and coefficient acquisition must also be included; the claim here is not that either necessarily requires a quadratic algorithm if kept implicit.

## 3. Direct Hadamard-stream closure also has growing order/degree

For fixed horizon L, the q-binomial coefficients obey

    (1-q^(k+1)) c_(k+1)=(q^L-q^k)c_k.          (2)

This is the denominator-cleared polynomial identity. It does not divide by c_k, which can vanish. Let s_k=sum_j w_j z_j^k and t_k=c_k s_k. With x=q^k and H as above, a direct closure recurrence is

    sum_(r=0)^J h_r
      [prod_(u<r)(1-q^(u+1)x)]
      [prod_(r<=u<J)(q^L-q^u x)] t_(k+r)=0.   (3)

It follows by multiplying the constant-coefficient moment recurrence by the common q-hypergeometric denominators; as a polynomial q-binomial identity it survives exceptional coefficient zeros. Each coefficient in (3) has degree at most J in x, and the natural explicit array again has quadratic size. Cumulative partial sums add a shift factor/order and do not make this dimension free.

For a scalar propagation implemented by dividing by the leading product in (3), the inverses are 1-q^(k+r). On the retained large-order branch these are units in the relevant searched range, but that must be checked/routed in an all-semiprime algorithm. A proper nonunit gcd solves factoring; equality to zero modulo N is not automatic success. The order-J construction (1) avoids these particular denominators but still needs implicit high-order propagation.

Straight binary splitting of L scalar/matrix transitions still has L leaves over a fixed-size residue ring; its numerical high-precision bit advantages do not remove that leaf count. q-BSGS groups transitions, but its advertised fast costs must retain degree and matrix dimensions. No new bound below soft O(J+sqrt(JL)) follows from the closure statements alone.

## 4. A concrete 2026 reduction test: the base change exposes residue sectors

Wang–Yang–Zhong (2026) reduce Laurent-polynomial multipliers of q-holonomic sequences using an adjoint operator. To apply that idea to source nodes, use base gamma rather than q=gamma^d, d=m². Set

    u=gamma^(-N-3d), e_j=3d-delta_j in [2d,6d],
    E(x)=sum_j w_j x^(e_j), f_k=u^k c_k.

Then the weighted query is sum_(k=0)^L E(gamma^k) f_k. The sequence f has first-order operator

    L_op=(1-q x^d) sigma-u(q^L-x^d),
    sigma(x)=gamma x.

Its adjoint acts exactly on every integer monomial exponent e as

    L_op^*(x^e)
      =(gamma^(-e)-u q^L)x^e
       +(u-gamma^(-e))x^(e+d).                (4)

Thus the reduction preserves exponent classes modulo d. It cannot mix arbitrary sparse source sectors into a common endpoint primitive merely because its order is one; its coefficient degree in base gamma is d=m².

A precise SYMBOLIC obstruction follows over Q(gamma), with gamma indeterminate. The first coefficient in (4) vanishes only at e_A=N+3d-dL, and the second only at e_B=N+3d. Both lie in one exceptional residue class e=N mod d. In every other class both coefficients are nonzero for all integer e. If a finite Laurent polynomial p in such a class has lowest/highest occupied exponents e_min,e_max, its image has a nonzero lowest term at e_min and a nonzero highest term at e_max+d. Hence its image cannot be a SINGLE monomial. Each nonexceptional monomial represents a nonzero class modulo the adjoint image.

The source e_j occupy at least ceil((m-1)/2) residue sectors, by the same low-digit two-fiber bound. Removing the one exceptional sector still leaves Omega(m) nonexceptional occupied sectors. Formal independent weights prevent cancellation of these individual nonzero classes. Thus an endpoint-only polynomial-adjoint reduction cannot eliminate the entire weighted remainder, and a dense remainder representation of degree d would itself pay m². A sparse sector-preserving reduction can avoid that dense cost, but retains the unknown sector sums; no cost bound for acquiring those sums is supplied.

This is NOT a finite-field nonsummability theorem. Numerical finite-order gamma can create additional coefficient zeros and long certificates in all integer residue sectors. Nor does the symbolic argument rule out rational certificates outside the cited Laurent reduction, noncyclic special functions, or a different implicit evaluator. Transfer to the actual ring would require a separately proved identity and paid unit/denominator handling.

## 5. Narrow primary checks

* Kauers–Koutschan, *A Mathematica package for q-holonomic sequences and power series*, section 3.2/Theorem 2, proves Hadamard closure with order at most the product of factor orders by linear dependence over a rational-function field. It establishes closure, not a uniform nearlinear modular evaluation clock with growing order. Primary PDF: https://www.risc.jku.at/publications/download/risc_3437/main.pdf .
* Wang–Yang–Zhong, *Polynomial reduction for q-holonomic sequences*, arXiv:2606.07061v1, 5 June 2026, section 2.1, explicitly works over a characteristic-zero field with q indeterminate. Lemma 2.2 gives the adjoint Lagrange identity; Theorem 2.4 requires shifted leading/trailing coprimality for the Laurent characterization; subsequent reduction uses leading-coefficient cancellation. These are useful exact symbolic statements, not a composite-ring or bit-complexity theorem for our weighted sum. Primary: https://arxiv.org/html/2606.07061v1 and saved PDF.

## Result

No soft O(J+sqrt L) weighted SLP was found. The useful new results are the actual regular-start Omega(m) order requirement and explicit recurrence constructions/cost contracts, plus the sector obstruction for a directly relevant 2026 adjoint-reduction method. A positive route remains: keep the order-J operator implicit and propagate it with genuinely sub-square-root-in-J aggregate cost, or evaluate all remaining sector sums through a new formal weighted inner-product identity. The existing reverse-AD bridge would then recover all values at the same asymptotic cost. No backend implementation or generic constant-state no-go was substituted for that missing theorem.
