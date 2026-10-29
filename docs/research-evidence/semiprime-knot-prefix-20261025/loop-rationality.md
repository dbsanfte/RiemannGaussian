# Loop rationality and a logarithmic-residue prefix candidate

2026-10-25. Constructive audit for the actual acquired Alexander polynomial, degree parameter J=soft O(k), prefix m<=M=Theta(k^(3/2)), unknown semiprime N=PQ, and long local q-orders. No fast prefix algorithm or exponent improvement is proved. This report does not revisit the earlier Padé exclusions.

## 1. Exact candidate: replace a multiplicative norm by a pole residue

Write the acquired normalized Laurent polynomial as

    Delta(T)=prod_(j=1..J)(T²-z_j*T+1)/(T^J*G(2)),
    z_j=x_j+x_j^-1,

with all x_j and x_j-1 units. Its rational logarithmic derivative

    r(T)=T*Delta'(T)/Delta(T)
        =sum_j [T/(T-x_j)+T/(T-x_j^-1)]-J               (1)

is acquired as a degree-O(J) numerator/denominator pair in soft O(J) ring operations: use the already acquired numerator S(T)=T^J G(T+T^-1) and r=T*S'/S-J. Formula (1) is an exact rational identity; it need not be evaluated at a pole.

Introduce an indeterminate s and define

    B_m(s)=prod_(i=1..m) Delta(s*q^i),
    R_m(s)=sum_(i=1..m) r(s*q^i)=s*B_m'(s)/B_m(s).       (2)

At each local prime p, let nu_p be the multiplicity of the zero s=1 of B_m(s). Then

    Res_(s=1) [R_m(s) ds/s] = nu_p mod p.               (3)

Equivalently this is the coefficient of (s-1)^-1 in R_m(s), since s=1 there. Unlike merely evaluating 1/Delta(q^i), equation (3) *retains* precisely the local poles and does not ask to divide their zero values.

**Bound that prevents characteristic cancellation:** each of the 2J roots x_j and x_j^-1 of the numerator S can equal q^i for at most one i in [1,m], because ord_p(q)>m. Thus

    0<=nu_p<=2J.

For sufficiently large native inputs, 2J<p, since J=soft O(k) while p>ord_p(q)>16k². Hence (3) is zero iff there is no local hit, with no multiplicity cancellation modulo p. This explicitly uses the native size regime; it is not valid without a multiplicity bound below p.

Suppose an algorithm returns a residue rho in Z/NZ whose two local components equal (3). Then:

- gcd(rho,N)=1 means both local counts are positive, so the original prefix A_m=B_m(1) is zero modulo N;
- gcd(rho,N)=N means both counts are zero, so A_m is a unit;
- a proper gcd immediately factors N.

Thus a **pole-residue prefix algorithm** returning rho, or a proper factor, in soft O(J+sqrt m) would implement the already reviewed zero-only prefix consumer. Logarithmically many such queries plus the existing signed row scan recover a factor. No full product, polynomial remainder of degree m, shifted-window primitive, or local order is needed by this consumer.

This is an explicit alternative computational target. It is not yet an algorithm with the required cost: directly forming R_m has up to 2Jm poles before cancellation; even computing only its residue at s=1 must determine which shifted poles arrive there. A symbolic representation of the sum alone does not pay that selection cost.

## 2. An actual telescoping algorithm, and a precise failure for this r

The most direct proposed computation is rational q-summation. Find a rational g(T) and scalar c such that

    r(T)=g(q*T)-g(T)+c.                                (4)

If found with degree soft O(J) and acquired in that budget, then

    R_m(s)=g(s*q^(m+1))-g(s*q)+m*c.                     (5)

One would compute the two endpoint residues, handling nonunit leading coefficients by gcd rather than dividing them. Endpoint q-powers cost only polylogarithmic work; degree-O(J) endpoint Taylor expansion and residue extraction would cost soft O(J), unless a nonunit coefficient already supplies a proper factor. This would meet the target.

**However, (4) is impossible for the native r at every scalar prime component for sufficiently large inputs, at any rational degree.** This is a narrow falsification of the one-rational-antidifference candidate, not a lower bound for pole-residue summation or prefix decisions.

Proof: regard r(T)dT/T as a rational differential over the local field's algebraic closure. At every nonzero root alpha of S, its residue is the positive integer multiplicity of that root in S. For each finite multiplicative q-orbit O of nonzero points, let the orbit residue be the sum of the differential's residues at O. If a differential has the form

    [g(qT)-g(T)] dT/T,

its orbit residue is zero: substitution T->qT permutes O and preserves dT/T, so the two residue sums cancel. A constant c contributes c*dT/T, with poles only at zero/infinity, and cannot change this nonzero-orbit condition. This argument is valid for finite q-order as well as infinite order; no characteristic-zero summability theorem is being imported into the local field.

For the native r, every orbit containing roots of S has orbit residue equal to the number of those roots counted with multiplicity. It lies in [1,2J], which is strictly below p. Thus it is nonzero modulo p. At least one such orbit exists because J>0. This contradicts (4). Pole signs are all positive: reciprocity pairs roots but does not produce the negative divisor multiplicities that a rational q-difference needs.

A q-invariant correction h(T^r), with r=ord_p(q), can absorb full-cycle orbit residues, but it introduces the unacquired local order and a complete cyclic spectrum. It is not an available small correction term here. More general telescopers, projections that discard most pole data, or use of native arithmetic are not ruled out by this test.

## 3. What knot loop rationality actually supplies

**Primary theorem source:** Lev Rozansky, *The Universal R-Matrix, Burau Representation and the Melvin–Morton Expansion of the Colored Jones Polynomial*, Advances in Mathematics 134 (1998), 1–31, DOI 10.1006/aima.1997.1661, [arXiv:q-alg/9604005](https://arxiv.org/abs/q-alg/9604005), v2 dated 1996-05-17. It proves rationality of higher lines of the colored-Jones expansion, whose denominators are powers of the Alexander polynomial. The zero-loop term is the inverse Alexander polynomial under normalized conventions.

**Precise convention reference:** Stavros Garoufalidis, *Difference and differential equations for the colored Jones function*, author version dated 2005-07-25, [author PDF](https://people.mpim-bonn.mpg.de/stavros/publications/difference.pdf), §1.1. It writes

    J_rat(Q,u)=sum_(l>=0) P_l(u)/Delta(u)^(2l+1)*(Q-1)^l,
    [n]*J_rat(Q,Q^n)=J_n(Q),

as a formal power-series identity around Q=1, with rational coefficients regular at u=1. Here Q denotes the knot's quantum expansion parameter, deliberately distinguished from the supplied arithmetic orbit base q.

**Adaptation:** the lowest-loop rational function 1/Delta(T) is already available from the acquired Delta in soft O(J); extracting it from an unacquired colored-Jones presentation would only add work. Its polar divisor is exactly the sought collision divisor. Higher loop terms have larger powers of that same denominator, so their rationality does not cancel the pole-selection requirement. The knot realization alone does not acquire those higher numerators P_l, a colored-Jones recurrence, or a small ordinary diagram.

The formal expansion variable Q-1 is not a nilpotent error at the supplied q in Z/NZ. In fact q-1 is a unit under the long-order promise. Thus no finite loop truncation becomes an exact modular evaluator merely by substituting Q=q. Normalization at T=1 does allow exact truncated Taylor arithmetic there, but evaluating a finite Taylor truncation at T=q^i requires an additional error theorem or algebraic reduction; it is not implied by formal rationality.

**Analytic theorem source:** Garoufalidis–Lê, *An analytic version of the Melvin–Morton–Rozansky Conjecture*, [arXiv:math/0503641](https://arxiv.org/abs/math/0503641), [author PDF](https://people.mpim-bonn.mpg.de/stavros/publications/analyticMMR.pdf), identifies colored-Jones asymptotics to all loop orders for small complex angle. Its complex small-angle regime supplies no exact finite-ring remainder bound for these long-order q-powers.

## 4. Relation to rational summation literature

Shaoshi Chen and Michael F. Singer, *Residues and Telescopers for Rational Functions*, [arXiv:1203.4200](https://arxiv.org/abs/1203.4200), introduces q-discrete residue criteria for rational summability. It motivates candidate (4), but its usual non-root-of-unity/characteristic-zero hypotheses are not assumed for the local modular execution. The orbit-residue proof in §2 is supplied independently for the exact finite-order scalar setting.

Their existence/obstruction criteria are not algorithms for selecting a pole at one supplied point among a long finite orbit segment in soft O(J+sqrt m). Applying a general rational-summation routine over Q(q) would also have to acquire its symbolic input and certify its specialization at the unknown local fields; this is not free preprocessing.

## 5. Composite-ring implementation requirements and remaining concrete question

Equations (1)–(3) are rational identities, and rho is well defined by CRT, but computing local Laurent expansions directly is not automatically executable over R. If the two primes have different valuations at s=1, the first nonzero coefficient of a denominator may be nonunit. Its gcd can reveal a proper factor; otherwise a globally zero coefficient must be skipped rather than inverted. A positive residue algorithm must include this valuation-aware work and prove it avoids scanning a degree-Theta(Jm) denominator.

The remaining concrete question is therefore:

    Given acquired Delta and q, compute only the residue at s=1 of
      sum_(i=1..m) [q^i Delta'(s q^i)/Delta(s q^i)] ds,
    as a scalar modulo N, or return a proper factor,
    in soft O(J+sqrt m), without expanding the rational sum.

This expression is the same as R_m(s)ds/s. Its local residue is a bounded collision count, and the proof above gives a complete zero-prefix consumer including saturation and mixed CRT behavior. The direct rational-antidifference shortcut is excluded, while computing this single pole projection by a new structured summation or native-arithmetic method remains open.

No new claim is made about an achieved 1/6 exponent, general algorithmic lower bounds, or a replacement for the inherited controller/extractor.
