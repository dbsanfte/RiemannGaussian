# Alexander polynomials, coloring and cyclic resultants

25 October 2026. Secondary literature routes, with scope limited to the
current whole-family acquisition problem. No new factoring bound.

## Fox coloring is a real divisibility detector

Kilic, Nijsten, Pellikaan and Ravagnani, *Knot Theory and Error-Correcting
Codes*, [arXiv:2307.14882v2](https://arxiv.org/abs/2307.14882v2), published
2025, [journal DOI](https://doi.org/10.1007/s10623-025-01615-x).
The published Proposition 3.16 identifies nontrivial Fox (Z/dZ,t)-colorability,
for t coprime to d, with gcd(d,Delta_K(t)) not equal to 1. The coloring
relations are sparse linear equations. The paper also supplies knot-derived
codes and decoding methods, with their stated field hypotheses.

Application analysis: for d=N a proper nonunit Alexander value gives a
factor by gcd. Saturation gcd=N is possible, so existence of a coloring
is not automatically a proper factor. A coloring whose difference from a
constant color vanishes at exactly one prime would reveal a factor, but
finding that coloring must be charged. Efficient decoding of a supplied
codeword over a known field is not that acquisition algorithm.

A constructive research target would realize the native collision system
as a sparsely presented tangle-coloring module and eliminate its interior
without expanding the long seed sequence. The paper does not supply this
realization, a whole-input covering knot family, or the required cost.
This route is lower priority than the exact Habiro-kernel match.

## Cyclic resultants clarify which long products already compress

Hillar and Levine, *Polynomial recurrences and cyclic resultants*,
[arXiv:math/0411414v4](https://arxiv.org/abs/math/0411414v4), Proceedings
of the AMS. Over an algebraically closed field of characteristic zero,
they study r_m=Res(F,X^m-1), give polynomial recurrences of length deg(F)+1,
and reconstruction results. A polynomial recurrence is not necessarily
a nonsingular linear recurrence or an initialized fast advancement rule.

The topological connection is visible in Silver and Williams,
*Twisted Alexander Polynomials Detect All Knots*: their Section 2 recalls
that orders of first homology of cyclic branched covers are absolute
cyclic resultants of the Alexander polynomial. The
[author manuscript](https://citeseerx.ist.psu.edu/document?doi=f4b2b51d9bfd9ab948c37ecd43ca623ee5a42411&repid=rep1&type=pdf)
also develops twisted versions. Only this full-cycle connection was used
in the present comparison.

Application analysis: X^m modulo a degree-J monic F is acquired by binary
powering in soft O(J log m) ring operations. This makes a full-cycle
resultant a naturally compressed query, with resultant elimination and
nonunit handling still to be specified over Z/NZ. Our query instead uses
the partial geometric product prod_(i<h)(X-q^i). The native order promise
is much larger than h, so its roots are not the complete root set of
X^h-1. No valid replacement by that cyclic resultant has been derived.

The useful question is whether a collision-preserving completion to a
cheap full-cycle query exists with a paid complementary factor. Supplying
the unknown local period, or its short annihilator, would change the
input contract. Neither source supplies it. This observation distinguishes
the two algebraic products; it is not a general impossibility theorem.
