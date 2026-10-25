# Higher cancellation in the literal lifted-root family

22 October 2026. Bounded symbolic investigation; no implementation, examples, tests, repository edits, or universal rate claim.

Let M=m^3. The acquired canonical descriptors satisfy exactly

    v_j^2-M z_j=4a_j N.

On the no-factor branch screen gcd(v_j,N)=1; then m,a_j,z_j are units as well under the native hypotheses. The map j -> a_j=N j^(-2) mod m has exactly two-element fibers {j,m-j}, and its distinct values are the integer representatives of N times the nonzero-square coset. This is a residue coset, not a set of rational-square-related integers.

## Exact antipodal norm folding

For an antipodal pair, v'=-v-Mu and z'=z+2uv+Mu^2 with u in {0,1,2}. Direct multiplication gives

    z z'=(z+uv)^2-4aN u^2.                       (1)

Thus antipodal multiplication has an exact quadratic-norm composition with public trace z+uv and multiplier a u^2. It stays in the same rational quadratic squareclass aN; it does not yield an integer square automatically. For u=0 it is the identical-z relation, whose normalized roots are globally opposite and whose square-congruence gcd is trivial. For u nonzero, equation (1) supplies another explicitly known norm value. Its right side is not an acquired square or a second distinguished square root. Iterating a norm composition would still require a cancellation of the nonsquare norm factors.

Different a values generally belong to different rational quadratic fields. The finite-field coset property does not identify these fields. Even a product of all a values that happens to be an integer square does not imply that the product of the z values is a square: the z values are norms of different elements, not copies of a common rational factor a.

## Exact criterion for a literal high-digit-independent product identity

Fix m and a residue N0 modulo M with gcd(N0,m)=1. Along X=N0+M t, all canonical a,b,kappa,v are fixed: a,b depend on N modulo m^2, and Delta changes by -4am t, leaving kappa modulo m unchanged. Hence the exact norm functions are linear:

    z_j(X)=(v_j^2-4a_j X)/M,
    z_j(N0+M t)=z_j(N0)-4a_j t.                (2)

For any fixed subset S, the desired square relation is the rational polynomial

    F_S(X)=M^|S| product_(j in S) z_j(X)
          =product_(j in S)(v_j^2-4a_j X).      (3)

A necessary and sufficient condition for F_S to be a square in Q[X] is that each distinct root v_j^2/(4a_j) occurs an even number of times. Sufficiency includes the leading scalar: within each equal-root group, the product of the constant terms v_j^2 is itself a rational square, so an even power of the common normalized linear factor is a square. Necessity is the even valuation of every linear factor. Repeated integer exponents reduce to their parity; rational product/quotient identities have the same even-root-valuation criterion.

These universally symbolic square identities are automatically trivial as factor relations. Indeed write an equal-root group using

    v_j^2-4a_j X=v_j^2*(1-X/r), r=v_j^2/(4a_j).

Its square root is a signed product of the v_j times (1-X/r) to half the group size. On the no-factor branch the denominators r have inverses modulo N because their numerators contain only screened v_j and their denominators contain 4a_j. At X=N, every factor (1-N/r) is 1 modulo N. Thus every rational-polynomial square root W supplied by such an identity satisfies

    W(N)=+product v_j or -product v_j modulo N

GLOBALLY, and both congruence-of-squares gcd attempts are trivial. Any nonunit denominator encountered instead already gives a proper factor through its explicit gcd guard.

This is a scoped exact classification: literal subset identities valid for every higher input digit, with indices chosen from the fixed N modulo M data, cannot supply a nontrivial square-root sign discrepancy. It does not exclude a subset chosen adaptively from the actual integer norm values, an identity using additional acquired objects, or a different evaluator.

## Precise constructive remainder

Equation (1) is a real acquired norm-composition identity. Equations (2)-(3) identify exactly what a further telescoping/divisor argument must add. It must construct, from the actual X=N, a parity dependency not merely a repeated-root polynomial identity, and must prove that its normalized square roots differ in sign at exactly one hidden prime. An accidental integer-square specialization of a nonsquare polynomial could do this, but its existence and acquisition are not consequences of the antipodal or residue-coset formulas above. Neither sparse-nullspace solvability, smoothness nor random sign independence is assumed.

No deterministic higher dependency satisfying these conditions was found in this bounded pass. The paid all-pairs consumer remains available; the exact missing condition is a nontrivial higher squareclass dependency of the specialized norm values with a certified local sign discrepancy, acquired in total soft O(m) work.
