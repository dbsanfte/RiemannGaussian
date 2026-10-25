# Fresh arithmetic localization audit

24 October 2026. No soft-k localization algorithm was obtained. This exact symmetry compression was derived and costed; it does not close the gap. No shared or frozen file was edited.

## Exact signed compression

Use unshifted x=q^i, -M<=i<=M, and U=beta^(a+bN+lambda). The opposite row has lambda'=(-lambda mod H), kappa=(lambda+lambda')/H in {0,1}, and exponent -E+kappa H. Its target is q^kappa/U. After retaining complete sign/swap orbits (coverage safe for the guaranteed witness), each signed pair contributes

    (x-U)(x-q^kappa/U)
      = x [t_kappa(x)-c_U],
    t_kappa(x)=x+q^kappa/x,
    c_U=U+q^kappa/U.

One may split the catalogue by kappa and replace signed scalar pairs by acquired c_U in soft k arithmetic. The transformed clock satisfies

    t_kappa(q^i)-t_kappa(q^j)
      =(q^i-q^j)(1-q^(kappa-i-j)).

Over each local prime, the supplied q orders exceed the whole index-difference range. Consequently only i=j or i+j=kappa identifies clock points. The symmetric index interval compresses by a factor two (with one endpoint adjustment for kappa=1). Its length remains Theta(h). This follows directly from the order promise, rather than a generic lower-bound claim.

Swap yields two transformed targets c_U,c_V. The mixed-root promise survives: at the witness index the transformed clock agrees with c_U modulo one prime and c_V modulo the other. If c_U-c_V is nonunit, a gcd or original-leaf handling may finish. On a continuing branch it remains an unknown mixed hit among soft k targets over Theta(h) clock positions. This supplies a smaller polynomial but no asymptotically shorter clock and no acquired useful index.

## Why the tempting q-product recurrence is not a completion

For R_h(X)=prod_(0<=s<h)(X-q^s),

    R_h(qX)=q^h R_h(X) (X-q^(-1))/(X-q^(h-1)).

This is a polynomial identity after clearing denominators. It transports a value only along its actual q orbit, and division at a zero denominator requires a separate branch. Swapped targets have

    A/B=beta^((a-b)(1-N)).

The catalogue supplies no short integer d with A/B=q^d. Integer divisibility H | (a-b)(1-N) is not a hypothesis; even if it holds, that quotient can greatly exceed h. Distinct lambda representatives also do not generally yield q shifts. Computing one q-product therefore does not acquire all paired query values through this recurrence.

Likewise,

    R_(2m)(X)=R_m(X) q^(m*m) R_m(q^(-m)X)

requires a scaled argument. Knowing R_m modulo F does not give R_m(q^(-m)X) modulo the same F: a discarded multiple F(X) becomes a multiple of F(q^(-m)X), whose remainder modulo F need not vanish. No fast-modular-composition claim was used to evade this changing quotient.

## Certificate perturbation does not yet help

A formal additive perturbation C(epsilon)=prod_i F(q^i+epsilon) has local epsilon valuation at most J: each original target can hit at most one clock index modulo each prime. Unequal local valuations expose a factor from a coefficient. Equal valuations remain possible under the signed/swap promise. The promises do not acquire initial coefficients in soft k: the known block query still pays soft sqrt(Jh), while direct clock construction pays h. This is a prospective representation, not an algorithm or a new obstruction theorem.

Conclusion: no candidate with both a proof and soft-k cost was found. Explicit signed arithmetic removes constant redundancy. The gap remains acquisition of a nonzero certificate, useful pair, or index; the already-known aggregate zero is not the requested output.
