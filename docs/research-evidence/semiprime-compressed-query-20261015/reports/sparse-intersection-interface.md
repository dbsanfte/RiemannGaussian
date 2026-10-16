# Collision sparsity and sparse GCD: the syndrome must select zeros first

2026-10-15. Fresh primary search and exact actual-source interface analysis. No deterministic soft O(m) factor-or-query algorithm was found. The result below refutes a concrete low-rank moment proposal; it is NOT a lower bound on computing the long query.

## The useful sparsity and its limitation

Let a_j=P_L(z_j;q). On the retained family, m-o(m) complete row values a_j are units modulo N, while at least one canonical row hits a hidden field. Thus the zero support can be sparse. This is not a sparsity bound on the represented polynomial P_L, its coefficient array, the vector of nonzero row values, or arbitrary rational functions built from them.

The existing collision-sparsity theorem is a retained-family statement, not a certificate that every qualified semiprime has few hits. A proposed algorithm parameterized by hit count must retain its worst-case dense-hit branch and all factor/recovery costs. Even a hypothetical cost soft O(J+sqrt(hL)) would not reach soft O(m) from the current h<=M^.997 bound; sublinear h=o(m) is not a polylogarithmic h bound. This numerical observation does not exclude a better additive-h algorithm.

## A concrete Prony/Padé proposal fails on the actual source

Consider ordinary row-value moments

s_k=sum_(j=1)^J a_j z_j^k,
S(T)=sum_(k>=0)s_k T^k=sum_j a_j/(1-z_j T).

It would be incorrect to give this stream recurrence order equal to the number of COLLIDING rows. It has poles at the NONZERO rows instead.

Here is an exact actual-source statement. In either hidden field, publicly equal integer offsets give equal z_j, while different integer offsets in [-3m^2,m^2] give distinct targets because their differences are smaller than the actual local order R>16m^2. Each offset occurs at most twice by the native low-digit quadratic. At an offset with a_j!=0, combining its repeated terms gives residue coefficient n_j a_j, with n_j=1 or 2, nonzero in the actual odd-characteristic field. Therefore no such pole cancels. The reduced denominator of S is exactly

prod_(distinct z with P_L(z)!=0)(1-z T).

If U rows are units modulo N, this denominator has at least ceil(U/2) distinct poles in EACH field, hence degree Omega(m) on the retained family U=m-o(m). This is an exact denominator/rank assertion, not an arithmetic cost bound.

Equivalently, for the distinct nonzero rows let their nodes be xi_l and weights c_l!=0, l=1,...,D. The D-by-D Hankel matrix (s_(r+t)) factors as V diag(c_l) V^T with V_(r,l)=xi_l^r. Its determinant is nonzero by distinct-node Vandermonde and nonzero c_l. Thus its rank is D, not the sparse collision count. Ordinary Berlekamp--Massey/Prony on these moments cannot be justified with h-term linear complexity. Formal independent weights give the same pole retention without relying on numerical sum signs.

This does not exclude a new functional whose weights vanish at ALL unit rows. It identifies the missing operation: construct collision-selective syndromes, rather than run a sparse decoder on unfiltered row values.

## What a genuinely collision-selective syndrome would require

If a hidden prime p and all a_j were already supplied, the field indicator

e_j=1-a_j^(p-1)

is one on zero rows and zero on nonzero rows. Its moments have only hit poles and are legitimate sparse-recovery input. But p is not algorithm input here, and the a_j are precisely the unknown long products. Replacing p-1 by an arbitrary public exponent is not justified for these row values; they need not lie in the gamma subgroup.

The quotient-algebra version makes the same dependency explicit. After deduplicating roots, let H=prod(X-z_j), A=F_p[X]/H and g=P_L(X) mod H. Then e=1-g^(p-1) is an idempotent projector onto the collision components, and trace_A(X^k e) gives their power sums. This is a useful conditional specification, but acquiring g and the exponent information is not free. It does not become cheap merely because the projector rank is small. A different way to acquire these traces directly could be a real advance and is not ruled out here.

Over Z/N, inversion of an acquired row value would itself detect a proper gcd or require saturated-zero recovery. A sparse-intersection proposal cannot assume those unit certificates before acquiring the values or an equivalent factor-aware functional. The known bisection controller solves refinement GIVEN a restriction-stable query oracle; collision sparsity alone does not instantiate that oracle.

## Fresh primary literature: contracts retained

1. Huang--Gao, Sparse Polynomial GCD Algorithms Asymptotically Linear in All Fundamental Parameters, arXiv:2609.08074v1. Theorem 3 is randomized over a field with its stated characteristic premise, and its displayed bounds retain a total-degree D factor and explicit input term counts. Even a small GCD is not a theorem for a succinct length-L q-product at sqrt(L) cost. Its abstract's simplified soft O(nTD) headline must not be read as logarithmic in D. Primary: https://arxiv.org/html/2609.08074v1 . Saved PDF/text and hashes are adjacent.

2. Qiu--Cao--Huang--Feng--Gao, Output-sensitive Sparse Polynomial GCD over Finite Fields is NP-hard, arXiv:2606.12144v1. Theorem 3 gives a BPP-reduction hardness statement for GENERAL sparse univariate inputs, with complexity polynomial in term bounds and logarithmic degree/field size. This is not a hardness reduction for canonical semiprime offsets or a geometric-root q-Pochhammer. No such reduction is claimed. Primary: https://arxiv.org/html/2606.12144v1 .

3. Van der Hoeven--Lecerf, On sparse interpolation of rational functions and gcds. The method assumes charged blackbox evaluation of the input polynomials and randomized field primitives. Applying it here would require a valid evaluation/access contract for the implicit q-product; treating those evaluations or its already reduced remainder as supplied is circular. Primary author text: https://www.texmacs.org/joris/sparserat/sparserat.html .

These inspected contracts did not yield a deterministic composite-safe soft O(J+sqrt L) factor-or-query theorem. They also do not prove one impossible. The searches were focused, not literature-complete.

## Precise positive target

A useful new primitive would acquire a collision-selective projector trace or an equivalent small-gcd witness for explicit H and implicit geometric-root G_L, with all preprocessing, field/composite pivots, source promises and proper-factor/global-leaf recovery charged. Its guarantee must work on all qualified inputs, or explain a separately paid dense-hit branch. A promise only about output GCD degree is not an evaluation oracle.

No new algorithm meets that contract in this investigation. The exact pole/Hankel calculation above only blocks the specific proposal to use ordinary long-row-value moments as low-rank sparse-collision syndromes. The actual unit-row density is not interpreted as a computational lower bound.
