# Root mathematical audit, 2026-10-24

PASS for the scoped statements below. This is a mathematical review of
initialized operations and failed attempts, not a sixth-rate certificate.

Reviewed exact bytes:

- euclidean-carry-attempt.md: 674d6478cf0bc4925871f1ce22555e32911f4afd279e8969c6a9a2b88be56be1
- endpoint-qdifference-extension.md: e2265505be7b22db845c8f3c5f454a02f2bedc844dbe4978da011833e5763f63
- floor-product-literature.md: afeaf86a0d713f41793db5ac7c25aeeeeeea7b45d09ae50618f8c25c961f4ab9

The Euclidean gap identity is exact: uniquely write a gap as Mi-aj,
1<=i<a, 1<=j<=floor(Mi/a). For M=qa+b, j<=qi gives the triangular
factor; j=qi+t gives bi-at, exactly the gaps of (b,a). Its scalar evaluator
actually acquires every full-block and tail node. The tail decomposition
costs soft(B+a), the full blocks soft(B+D/B), and Euclidean stage costs
sum to soft sqrt(aM). All inverses are of public integers below the
prepared factor cutoff. The correction norm permits gcd localization.
Even if a period block extends past the original K-menu endpoint, every
correction leaf still has absolute value below 3m^3+(5/2)m^2<N on the
hard branch, and nonzero residue -a_j*j modulo m. Thus localization
cannot end at zero or an N-multiple. The literal all-row algorithm emits
Theta(m^2) targets: a_j has fibers of size at most two, leaving a positive
fraction of a_j at least m/4. This is an implementation count only.

The floor-product report's key modular claims are independently proved:
carry residues are precisely the positive semigroup gaps; the displayed
cross-multiplied gap-polynomial identity follows by partitioning residues;
one rectangle is acquired by degree-m polynomial construction and a-point
monic MPE, with no evaluation-value inverses. Its division branch requires
the stated acquired-unit test. No external Barnes or lattice generating
function theorem is used to justify a modular operation here. Bibliographic
search conclusions are not claimed exhaustive or proof of impossibility.

The endpoint relation follows by cancelling overlapping factors as a
polynomial identity. q-shift does not act on the quotient at t=1 because
q-1 is a unit. A supplied orbit jet can be transported when the relevant
denominator is a unit; the normalized value at zero supplies no such jet.
This checks the particular algorithm, not all ways of evaluating the
normalized q-difference solution. The native denominator refinement was
derived independently by root: one target supplies h distinct poles and
each multiplicity is between 1 and J<p. Their residues cannot vanish,
so reduced denominator degree is at least h. This excludes exact short
rational reconstruction, not a fast endpoint functional.

No whole-query exponent improvement is established. Earlier algebraic
q-shift quotient failures already explain the endpoint-chart issue; do
not reclassify that change of chart as a new acquisition result.
