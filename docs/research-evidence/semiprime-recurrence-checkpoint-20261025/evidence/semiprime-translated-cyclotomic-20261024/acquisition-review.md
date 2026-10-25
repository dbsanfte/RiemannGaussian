# Independent projected acquisition audit

2026-10-24. Verdict: **PASS**. No required fixes. Reviewed exact `/tmp/semiprime-translated-cyclotomic-20261024/acquisition-attempt.md`, SHA256 `8c70eb75861922ea5f06b9a515b8a05e330d472a860b4dfae8ad597895f1669a`.

The preserved README's actual hash is `992e31ea5ece408e448dba91771a1616228b4629668552960c15311c9aafad6e`, agreeing with the report. No repository or source edits were made. This verdict concerns initialized algebraic operations and their cost, not a covered observable or factoring-rate improvement.

## Unit acquisition

For odd m the displayed telescoping inverse numerator multiplies beta+zeta to beta^m+1. Odd local order of beta makes beta^m have odd order, whereas -1 has order two in each odd residue characteristic; hence beta^m+1 is a unit. The same proves gamma=beta+1 is a unit. Thus signed powers used in the row definition are lawful, and one full length-m algebra element, its inverse and known-exponent powers are acquired in soft m residue arithmetic with the stated logarithmic exponent/bit overhead. This is not a bound for m separately materialized full row vectors.

## Augmentation, idempotent and weighted trace

Augmentation commutes with sigma_k, so epsilon(T_j)=gamma^(ell_j+a_j+N) exactly. With the inherited delta_j=ell_j+a_j, the changed-base target list is correct. One common gamma^N and O(m) scalar signed powers give genuinely acquired soft-m scalar output.

The vector e0=(1/m)sum zeta^r is well defined, idempotent and fixed by every sigma_j. Multiplication by any a in A satisfies e0*a=e0*epsilon(a), since every cyclic shift fixes e0. Therefore e0*T_j has all coefficients epsilon(T_j)/m. Representing the output as one vector e0 plus O(m) scalars is a lawful compact representation; writing all O(m²) coefficients is explicitly excluded from the claimed clock.

The multiplication matrix of e0*T_j is (epsilon(T_j)/m) times the all-ones matrix. Its trace is epsilon(T_j), and its image is the free rank-one summand R e0. In contrast the regular multiplication trace of T_j itself is m times its constant coefficient, because only the identity cyclic shift contributes to the diagonal. The report carefully distinguishes these two traces. The action on supplied v is e0 epsilon(T_j)epsilon(v), requiring one O(m) augmentation of v and O(m) scalar row actions. It is not an acquired action on the complementary summand.

In the quotient by Phi_m, sum zeta^r=0, so e0 vanishes. The augmentation projection cannot be transferred there as a nonzero observable; this scope distinction is correct.

## Selected coefficient kernel and phase identity

Writing sigma_k(f)=sum_t f_t zeta^(kt) gives the displayed coefficient contraction exactly. For a genuinely common L the nonzero t terms form a multiplicative convolution/correlation on F_m^*. A public primitive-root indexing and ordinary cyclic polynomial convolution achieve its soft-m bound without Fourier roots in R. Factoring m-1 by trial division and even exhaustive primitive-root testing fit the conservative soft-m metadata allowance. The native L_j are not common, so this conditional convolution does not initialize the native kernel.

For the constant coefficient, sigma_j preserves coefficient zero and sigma_j sigma_k(f)=f. This proves the second exact expression. Factoring out zeta from each translated term gives monomial exponent j ell_j+j² a_j. The native congruence ell_j=-2a_j j modm and a_j j²=N modm makes this exponent -N modm, exactly as displayed. Negative powers are permitted because the translated factors are units. The remaining translated factors retain their native j-dependence; no universal common kernel follows.

## Actual all-row baseline

For each j, signed cyclic powering acquires u^ell_j in soft m. The polynomial (beta+zeta^j)^a_j has a_j+1 distinct cyclic positions because 0<=t<=a_j<m and j is invertible modulo the prime m. Its coefficients can be acquired using the inherited certified small-integer units; alternatively the stated binary-power branch avoids factorial divisions entirely. One cyclic multiplication plus a dot product costs soft m per row for a fixed number of requested coordinates. Streaming over m-1 rows therefore costs soft m² with soft m active coefficient storage and O(m) scalar output. Multiplying by m supplies the original unweighted regular traces.

The claimed Theta(m²) explicit-binomial-support count also follows: the equation a_j=A has at most two j-solutions, so a positive fraction of tags have a_j>=m/4. This is a count for the displayed implementation, not a lower bound on selected-output algorithms. The report makes that limitation explicit.

## Recovery and coverage assumptions remain separate

The soft-m projection computes a scalar list under base gamma=beta+1. A unit gamma does not imply any required local order bound for gamma^(m²). Nor does knowing q_cyc as a unit establish the scalar beta decoder or its restrictions in the degree-m algebra. The report imports none of those implications: it explicitly leaves long-interval membership, new scalar order certification, original selected-coefficient coverage and factor recovery open. The native own-tag equality may be projected by a ring homomorphism, but this does not make the projected observation a known successful selector.

Accordingly the positive result is exactly paid augmentation/idempotent projection, while generic original coordinates and regular traces have only the displayed soft-m² streaming algorithm. No covered query, q_cyc order promise, group-algebra recovery oracle or new sixth-rate bound is asserted.
