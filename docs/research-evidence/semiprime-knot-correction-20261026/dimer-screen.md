# Dimer/cluster source check

26 October 2026. This source was inspected during the correction search;
no new native contraction algorithm was obtained from it.

Mészáros–Musiker–Sherman-Bennett–Vidinas,
[*Dimer face polynomials in knot theory and cluster algebras*](https://link.springer.com/article/10.1007/s00029-026-01146-w),
Selecta Mathematica (2026), Theorems 4.11, 6.8 and 6.17, gives an
Alexander specialization, a cluster F-polynomial realization and
explicit graph reduction/mutation rules. The square-move substitutions
in Proposition 6.16 involve both a face weight y and factors 1+y.
Theorem 6.19 treats bigon removal. These are exact algebraic identities;
they do not assert a cost bound for a binary-described native clock.

Here is the direct finite-ring check relevant to our input. A weighted
bigon with two edge weights 1 and -t/v has partition function 1-t/v.
Its edge weights are units, but its partition function is a collision
factor. In face coordinates y=-t/v, this is precisely 1+y. At t=v,
the square-move expression containing (1+y)^(-1) is undefined. A
symbolically cleared identity remains valid, but the collision factor
must be retained. This is a local test, not a theorem against all graph
reductions or all choices of coordinates.

The Laurent property concerns the original cluster variables; it does
not certify a nonzero value for every intermediate cluster variable or
for a coefficient factor 1+y after specialization. A division-free
Laurent or dimer expression can retain the target zero. The remaining
question is its acquisition cost on the actual compact native input.
No construction was found here that groups the long clock, acquires its
cleared scalar correction, and meets soft O(L+sqrt(m)). Thus this paper
is retained as a possible exact rewrite tool, not counted as an
acquisition advance.
