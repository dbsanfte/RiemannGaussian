# Arithmetic selection and exact row translations

23 October 2026. **No whole-family soft-O(r) detector or improved
factoring exponent was obtained in this round.** Here
r=Theta(N^(1/6)). The preceding all-input source theorem remains in
force; the unresolved step is finding a useful member of that source
within the required budget.

The constructive work produced an exact common-clock representation,
fully factored small coefficient data, and a coupled integer equation
with direct factor recovery. These specify useful inputs and targets;
none yet supplies the missing selection algorithm.

## Exact common clocks, with the carries retained

For a source exponent

    K=a*c^2+B_C*c+C*N-r^4*sigma,

the [integral gauge](reports/quadratic-carry-gauge.md) constructs public
integers t_C,k_C and a common quadratic q_(a,b) such that

    K=q_(a,b)(c+t_C)-r^4*(sigma+k_C).

This is an equality of individual leaves, preserving every possible
collision and the exact endpoints. The balanced a=1 case uses only two
quadratic clocks. The varying information is now in the two translated
intervals attached to each row.

The [independent review](reviews/gauge-independent-review.md) proves
that these intervals do not overlap in the way needed for immediate
telescoping. In one clock branch, different horizontal starts differ
by nonzero multiples of r, and their centers satisfy

    |Delta k|+|Delta t|/2 >= N*r/r^4 >256r.

Thus nearby horizontal blocks have widely separated seed intervals.
A finite r-cycle also fails for the prepared base: the clock's boundary
ratio depends on its starting index. These exclude the two tested
contractions, not a general fast norm algorithm.

## The paired arithmetic target

The [paired-label derivation](reports/paired-label-selection.md) uses
the actual coupling of the unknown factors P,Q. Its additive pairing
convolution is acquired in soft r, and a linear partner row supplies a
short seed even when Q exceeds sqrt(N). The exact equation is

    g(c*tau-ell)=sigma*(H*tau-b_t*d), H=r^2,
    |sigma|<3.5r, |tau|<1.5r.

Any integer solution whose candidate X=H*tau-b_t*d lies in the genuine
factor window gives a proper gcd with N. This is proved for false as
well as true candidates. Finding such a solution jointly still retains
the row and multiplier labels; evaluating each pair separately costs
soft r^2.

The [coefficient continuation](reports/factored-coefficients-continuation.md)
also computes both global roots of the monicized row polynomial. Its
shared small-lift search has the inherited soft r^(3/2) bound. For a=1,
one root family exactly reindexes the old long arithmetic progression.
It does not thin the search. Rational reconstruction would be cheap
given the true ratio image modulo r^4, but that image is not acquired.

## Factored norms and the SQUFOF boundary

All a,C factorizations are acquired in soft r: batch division by primes
through r removes their small factors, and |C|<r^2 makes every remaining
cofactor prime. The [ideal report](reports/ideal-short-cofactor.md)
uses this to acquire a public factored-norm ideal relation. The true
short sigma describes a separate hidden-prime relation whose
recognition remains open.

There is a uniform obstruction to the proposed SQUFOF transfer for
**every negative-C descriptor**. Its required oriented norm generator
would satisfy

    u^2+4a|C|N*v^2=r^4.

Nonzero v is impossible by size; v=0 has the wrong ideal orientation.
For positive C, an exact replay of one inherited true witness disproves
automatic principality from a small sigma. It does not disprove that
some other positive-C row could work. All-row existence, usefulness,
and total recognition/return cost remain unproved.

The [reciprocal/Bézout audit](reports/reciprocal-bezout-kernel.md)
separately checks the actual carried source against two rank-two
reciprocal determinant identities. Their hypotheses fail after a paid
row-difference screen. The exact Bézout representation needs the full
product residue as an input; acquiring it is the original open step.

## Validation and continuation

The [root review](reviews/root-review.md) checks the integer identities,
proper-gcd recovery, coefficient factoring cost, negative-C proof and
scope of the obstructions. The [ideal review](reviews/ideal-review.md)
checks the quadratic-order conventions and fixed class-cycle replay.
The replay is retained in
[implementation/replay_principal_square_premise.py](implementation/replay_principal_square_premise.py),
with its actual output in [replay-results.json](replay-results.json).
It tests one claimed implication, not asymptotic coverage or speed.

[Source pins](source-pins.json), [copy provenance](archive-provenance.json)
and [validation](validation.json) preserve the evidence. Previous frozen
packets are unchanged. No Lean theorem, broad build, commit or push was
performed.

The next useful advance remains a method that evaluates the separated
translated-window product, or acquires one bounded integer witness,
in soft r over the entire family. The 1/6 goal remains open, and full
executable/Lean bit-cost integration is still required afterward.
