# A new varying-field analytic input from openai/math family 029

24 October 2026. Source audit and a conditional derived class-group-generator contract. This is not an integer-factoring algorithm, LP relation-hitting theorem, or faster native recurrence query.

## Explicit mathematical assumption for every derived claim

ASSUMPTION: family 029 Theorem 1.2 is correct with its stated common zero-free strip. Every quadratic Hecke-strip and class-group-generator claim derived below is CONDITIONAL ON this assumption. The present audit checked the source statement, its scope, the final Mellin argument's asserted use of field-dependent onsets, and the base-change deduction. It did not independently verify all representation-theoretic, local, coefficient-reflection, or other intermediate lemmas on which Theorem 1.2 depends.

The repository README explicitly says the collection contains results at different verification stages and that some unformalized results could have issues. Family 029 has no Lean link in CONTENTS.md. The new source deserves separate credit from the previously audited fixed-field QRH manuscript, but its appearance in the collection does not discharge the assumption above.

## Pins and exact source scope

Repository: https://github.com/openai/math . Main commit fetched during this audit: 1581d4cbdd69a0faf34b2089614fe2a814316a6a.

Family 029, Primitive roots for every admissible integer base, October 4, 2026:
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/01-introduction.tex

Theorem 1.2 states that every finite-order Hecke L-function over EVERY cyclotomic number field F containing mu_12 is zero-free in Re(s)>1-10^-6. The principal character is included, with its pole at 1 allowed; there is no conductor or height cutoff. The numerical width is common to all fields and characters. The source explicitly allows auxiliary constants and onsets to depend on the fixed F and character. The conclusion is nonetheless a common zero-free half-plane, not merely a family-dependent error estimate.

The full Section 6 proof is cached as primitive-zero-free.tex. Its final Mellin transform is holomorphic for Re(s)>1-1/20000, so the smaller claimed width 10^-6 follows. The concluding paragraph explicitly explains why field-dependent onsets affect only a finite portion of the Mellin integral and do not change this half-plane. This audit verifies the statement, scope and proof dependency, not every representation-theoretic/local calculation in the proof.

The introduction expressly distinguishes this new arbitrary-cyclotomic-field construction from the September 30 Quasi-Riemann Hypothesis paper over Q(sqrt(-3)). Thus the earlier fixed-field scope rejection does not apply to this separate theorem.

## Exact descent to every quadratic field

Let K be a quadratic number field of fundamental discriminant d_K, and let chi be any finite-order Hecke character of K. By the quadratic Kronecker-Weber embedding, K lies in F=Q(zeta_M), M=lcm(12,abs(d_K)). The extension F/K is abelian. Pull chi back by the idele norm F/K, giving eta=chi composed with Norm.

Abelian Artin/Hecke factorization gives the identity of full L-functions

    L_F(s,eta) = product_(psi in Gal(F/K)^dual) L_K(s,chi*psi),

where psi is interpreted as the finite-order Hecke character of K supplied by class field theory. This is base change of a one-dimensional character, or equivalently induction of the norm-pullback character. Primitive conductors must be used consistently, rather than dropping arbitrary local Euler factors.

The factor psi=1 is L_K(s,chi). Away from s=1, every factor on the right is holomorphic: finite-order Hecke L-functions have no other poles. A zero of this factor in Re(s)>1-10^-6 would therefore make the left side zero. Family 029 excludes this. At s=1, the standard nonvanishing theorem for nonprincipal finite-order Hecke L-functions handles the possible pole issue. Consequently, CONDITIONAL ON family 029 Theorem 1.2, the same common strip holds for every such K and chi. The abelian base-change implication itself is the verified deduction here.

The potentially enormous degree of F is used ONLY to transfer zero exclusion. It is not charged as a computational construction and must not enter subsequent uniform constants. Prime-ideal estimates must be obtained from the original quadratic K, or from controlled unramified extensions, using their own degrees/discriminants.

## Derived small prime-ideal generators, with no relation claim

For imaginary quadratic K of discriminant d, the source's uniform smoothed Dedekind-zeta estimate (family 142 Section 10, cached factorization-analytic.tex) can be combined with the preceding strip. For one fixed nonnegative smooth function phi supported in (1,2), it gives

    Psi_M(x) = x*Phi(1) + O_phi(x^(1-delta)*(log D_M + [M:Q])),
    delta=10^-6,

with an absolute field-independent implied constant, whenever zeta_M has the common strip.

Suppose the prime-ideal classes of norm <=2x generate a proper subgroup of Cl(K). There is a nontrivial character of a cyclic quotient, corresponding to a cyclic unramified extension M/K of degree m>=2. Factorization of zeta_M over K and the preceding quadratic Hecke strip give the same strip for zeta_M. Moreover

    log D_M = m*log abs(d),    [M:Q]=2m.

Subtract the two smoothed explicit formulas, normalizing by m:

    Psi_K(x) - Psi_M(x)/m
      = (1-1/m)*x*Phi(1)
        + O_phi(x^(1-delta)*(log abs(d)+2)).

All prime ideals of K of norm <=2x split completely in M by the assumed subgroup. Every prime-power contribution in the support then cancels EXACTLY in the left side, so it is zero. This contradicts the displayed formula once x^delta exceeds an absolute constant times log abs(d)+2.

Thus, CONDITIONAL ON family 029 Theorem 1.2 and using the uniform smoothed explicit-formula input stated above, all prime ideals of norm at most C*(log abs(d)+2)^(1/delta) generate Cl(K), for an absolute effective C. The absolute constant can be made effective using explicit zero counts and a fixed computable test function; it is not numerically evaluated in this audit. No field-dependent constant from the huge cyclotomic F appears in the argument.

For d of O(log N) binary length, enumerating these rational primes, finding their quadratic roots by brute force modulo each small prime, constructing their prime ideals/reduced forms and retaining split or ramified ideals costs a fixed polynomial in log N. For K=Q(sqrt(-N)) with squarefree odd N, use its fundamental discriminant d=-N or -4N as appropriate; any proper gcd with a small enumerated prime already factors N. This is asymptotically within soft N^(1/6). A finite fully numerical implementation would pin the absolute cutoff constant, rather than silently use a field-dependent onset.

This only acquires a generating list. It supplies neither relations, smooth principal ideals, a class-group navigation oracle, nor deterministic LP smoothness/hitting. It does not instantiate a complete factoring algorithm.

## What family 142 actually adds, and its computational limits

Family 142, Deterministic Polynomial Factorization over Prime Fields (October 4), is cached in factorization-00-introduction.tex through factorization-09-complexity.tex and factorization-analytic.tex. Its proved input is a KNOWN prime p and a DENSE polynomial over F_p. Its top-line bit bound is ((n+1)*ceil(log_2 p))^(10^12), not soft-linear in n.

Dependency chain: family 029 Theorem 1.2 -> uniform smoothed prime-ideal estimate -> auxiliary primes ell_q <= c0*B^20000000 with p a non-qth-power modulo ell_q -> explicit cyclotomic invariant algebras and full small-prime primary generators -> root extraction in reduced finite algebras over the known finite field -> function-field norm/divisor arithmetic and odd-degree splitter (or the even-degree tournament splitter) -> Berlekamp algebra and the degree-lowering driver. Here B=20+(n+1)*(ceil(log_2 p)+1). Auxiliary-prime search uses numerical ell_q sizes; all those costs are included in the huge polynomial exponent.

The concrete recognizable separator in the Berlekamp driver tries b(t)=sum_j t^j*b_j for 0<=t<=r^3, testing square-freeness of its characteristic polynomial. The proof assumes an already acquired r-dimensional algebra over KNOWN F_p and distinct coordinate functionals; its cost is polynomial in that explicit dimension. It is not a hitting set for finding relations in an implicit number-field class group.

The dynamic-evaluation lemmas split unknown ROOT COMPONENTS of k[T]/F over one explicit finite field k. They use known cardinalities Q, powers Q^d, valuations of Q^d-1, supplied full primary generators, and Frobenius linear equations. Replacing p or Q by composite N does not preserve these proofs or exponents. A nonunit pivot could incidentally factor N, but no theorem promises that one appears or supplies a correct continuing trace.

The norm solver is over k(X), with explicit finite-field superelliptic curves and vector-bundle/linear-algebra constructions on the projective line. It is not a number-field class-group norm/relation algorithm. Nor does a polynomial splitter that may return known roots A or B select the mixed CRT root of the native paired quadratic. No such mixed-root selection contract is stated or derived here.

## Exact outcome

New source and conditional consequence: common zero exclusion for finite-order Hecke characters of varying quadratic fields follows from the separate October 4 family 029 Theorem 1.2 by exact abelian base change, CONDITIONAL ON that theorem's correctness. The corresponding conditional affordable object is a polylogarithmic small-prime-ideal generating list, also subject to pinning its absolute numerical cutoff. This audit has not independently established the family 029 theorem. No whole-family native acquisition, LP derandomization, or complete deterministic sixth-exponent factorization follows in this audit. No shared/frozen file was edited.
