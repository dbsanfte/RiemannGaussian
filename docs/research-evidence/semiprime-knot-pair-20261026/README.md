# Native twist-knot input and the adjacent-pair scalar test

26 October 2026. **A complete deformed polynomial family is now acquired cheaply; the original collision query is not.** The guaranteed sixth-exponent factoring goal remains open. The current native query still costs soft O(k^(5/4)), with the previously established wheel saving; k=Theta(N^(1/6)).

## Constructive result

[Kohli's twist-knot formulas](https://doi.org/10.1080/10586458.2016.1255860) allow us to specify an actual knot C as a connected sum of binary-encoded negative twist knots. Its ordinary Alexander polynomial modulo N is exactly the acquired native polynomial K. This choice requires O(L log N) bits, where L=soft O(k), and no expanded crossing diagram.

The [twist construction](twist-lift.md), independently [reviewed](twist-review.md), acquires one degree-at-most-2L polynomial F in soft O(L) bit cost, including all binary twist powering and coefficient multiplication. For every adjacent reciprocal native pair,

    a_i=eta^(2i+1), b_i=eta^(-2i-3), u=a_i*b_i=q^-1,
    LG(C;a_i,b_i)=F(B_i), B_i=(a_i-1)(b_i-1).

The common u is what makes the complete coefficient representation cheap. This is acquisition of the deformed scalar family, not acquisition of all its values or of their long product. Original and deformed row quadratics differ by an explicit correction; dropping it is unjustified.

## What the other investigations establish

| Result | Evidence | Consequence |
| --- | --- | --- |
| Complete lawful four-state Nichols map | [Construction](nichols-rank-four.md), [review](nichols-review.md) | All Yang–Baxter, inverse, rotated-inverse and curl identities are exact over the native ring. Only known units are inverted. |
| Universal zero-preserving substitution fails | [Scalar audit](scalar-audit.md), [review](scalar-review.md) | For the figure-eight knot, an Alexander zero can coexist with a unit deformed scalar; the exact resultant is 25. This is not an attained native-catalogue counterexample. |
| Original geometric block is fully initialized | [Block formula](block-contraction.md), [review](block-review.md) | A length-b block costs soft O(L+b), with all normalization factors retained. Repeating these blocks does not improve the existing whole-query exponent. |

The explicit positive-trefoil scalar of our R convention matches Kohli's printed trefoil after simultaneous variable inversion. A universal identification of those raw matrices at identical parameters is not asserted. The published polynomial-invariant dictionary and the inversion-symmetric figure-eight calculation are audited separately. The twist-family algorithm uses Kohli's own polynomial convention directly.

Pairing halves the number of positions and doubles the degree, leaving the degree-times-clock scale unchanged. Consequently even a new native collision-preservation theorem for F would need an additional fast contraction before giving an exponent gain. The exact target remains a complete collision query with soft O(L+sqrt(m)) acquisition, including recovery of an original collision leaf, rather than the current soft O(L+sqrt(Lm)).

## Reproduction and next target

The standard-library scripts [check_nichols_symbolic.py](check_nichols_symbolic.py) and [check_pair_symbolic.py](check_pair_symbolic.py) verify universal Laurent-polynomial identities and the integer resultant. The independent [matrix checker](check_nichols_review.py) uses SymPy and also checks all three determinants and the inverse-variable negative trefoil. These are exact algebraic certificates, not a numerical coverage campaign or Lean proof.

The next substantive step should use the explicit correction and actual semiprime arithmetic to obtain a collision-preserving contraction, or accelerate the simultaneous shifted block evaluations. Another small representation or more successful examples would not establish that step. Primary references and scratch source fingerprints are in [sources.json](sources.json); validation and preservation scope are in [review.json](review.json), with packet hashes in [manifest.json](manifest.json).
