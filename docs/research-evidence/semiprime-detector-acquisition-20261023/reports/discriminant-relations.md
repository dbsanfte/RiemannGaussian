# Structured discriminants: exact cubic identity and relation cost

23 October 2026. Scratch continuation of `count-acquisition.md`, after reading the inherited normalized-discriminant/conic material and the current structured-catalog proof. No frozen entries or repository files changed. This report does not acquire a detector or a new factoring exponent.

**Result.** The cubic Hensel lift has an exact Gaussian-norm identity, but the square-root orientation it supplies is globally the already known one. Retaining the canonical integer carry prevents replacement of the actual discriminants by those Gaussian norms. Integer-square and repeated-discriminant screens are affordable sufficient tests; no proof forces either to succeed. The smooth-parts parity route still lacks both a relation-existence theorem and a nontrivial-orientation theorem, with its matrix cost charged below.

## 1. Exact common-a identity, with the lift carry retained

Write H=r^2 and M=r^4. For a nonzero-a AP/Gauss row,

    B^2-4aCN=M D0,     CN=a (mod r),     B=-2a (mod r).

All integers a have |a|<r<P,Q; thus a is invertible modulo r and N. Put

    U=CN-a,
    L=-16a^3-8a^2 U+2aU^2-U^3,
    F=(CN-3a)^2+16a^2=(U-2a)^2+16a^2.

There is an exact polynomial identity

    L^2-U^4 F=256a^5 CN.                                 (1)

Because r divides U, the rational integer-local expression

    L/(8a^2)=-2a-U+U^2/(4a)-U^3/(8a^2)

is a square root of 4aCN modulo M, with residue -2a modulo r. Simplicity of that root proves it is the same Hensel branch as B. This statement uses inverses modulo M; it does not assume 8a^2 divides L as an integer. There is therefore an integer t with

    L=8a^2 B+M t.

Substituting into (1) gives the exact carried identity

    64a^4 D0+16a^2 B t+M t^2=(U/r)^4 F.                  (2)

This is the required correction to a putative replacement of the small signed D0 by the Gaussian norm F. Both cross terms in (2) remain; setting them to zero would change the supplied integer discriminant.

More decisively, (1) provides no independent root orientation even for F. Modulo N,

    U=-a,     L=-5a^3,     F=25a^2,
    L/U^2=-5a.

So the root of F obtained from the norm identity is precisely the obvious global root -5a. Comparing it with the other public root 5a yields only gcds 1 and N (a proper gcd with 10a is already an elementary small-factor exit). No independent P/Q sign is forced. Products or quotients using this same explicit root retain that orientation. This diagnoses this particular norm simplification; it is not a lower bound against another arithmetic relation algorithm.

The pure-integer adjacent replay checks (1) symbolically by homogeneous polynomial coefficients and (2) on the already recorded single row. It performs no row search, smoothness sample, or coverage campaign. Every quantity above has O(log N) bits up to an absolute constant, so these identities and all t values are acquired in soft r work for O(r) rows.

## 2. Pair and singleton relations that really would factor

The supplied bounds are |B|<3M and |D0|<5M for the Gauss source; the structured catalog has the tighter |B|<=M/2 and |D0|<17M/4. Since P,Q>16H, N>256M.

* If a nonzero-a D0 is an integer square v^2, then

      (B-Hv)(B+Hv)=4aCN.

  Both factors are nonzero because aC!=0, and each has absolute value <(3+sqrt(5))M<N. Since N divides their product, a gcd supplies a proper factor. Exact integer-square tests on all rows cost soft r. Linear a=0 Gauss rows have D0=b^2 but one displayed factor is zero: their square relation is trivial and must not be counted as this success case.

* If two rows have the same D0, then

      (B_i-B_j)(B_i+B_j)=4N(a_i C_i-a_j C_j).

  If B_i!=+/-B_j, both factors are nonzero and have absolute value <6M<N; a gcd again factors N. If B_i=+/-B_j, then a_i C_i=a_j C_j and the two supplied roots have the same global orientation. Sorting detects the useful exact duplicates in soft r.

  For the structured positive-a catalog, **any duplicate D0 among distinct descriptors in one window factors N**, even when a differs. Indeed |B_i+/-B_j|<=M<N makes global equality or opposition of roots an exact integer equality B_i=+/-B_j. Since B_i=-2a_i modulo r and 1<=a_i<=A with 2A<r, equality forces a_i=a_j, and equality of D0 then forces C_i=C_j. Opposition would force r|(a_i+a_j), which is impossible. Thus distinct descriptors cannot produce the global-sign exception. This sharpening proves the duplicate screen is sufficient whenever a duplicate exists; it does not force a duplicate.

There are only O(r) row discriminants in an interval of length O(r^4). Neither a duplicate nor an integer square follows by pigeonhole. These are positive exact screens, not acquired all-input relations.

Even proportional rows expose the carry issue. If (a',C')=(ka,kC) and B'=kB-Mh, then

    D0'=k^2D0-2kBh+Mh^2.                                (3)

Ignoring h would manufacture a square-class relation whose supplied roots have the same global orientation anyway. Keeping h yields the actual, generally different integer square class.

## 3. Parity matrix: what is paid and what is missing

The inherited soft-r smooth-parts computation applies to all O(r) signed D0, for any y<=r. Their prime-exponent parities up to y can also be recovered with prime-product gcd trees and repeated division in soft r bit work; each O(log N)-bit integer has only O(log N) prime factors with multiplicity. Sign is an additional parity coordinate. None of this factors the remaining y-rough cofactors.

For rows proved completely y-smooth, let m_s be their number and t=pi(y)+1. Their parity matrix has m_s rows and t columns. Its explicitly supplied sparse input has soft-r size. A dependence is forced if m_s>t, but the catalog proves no such lower bound for m_s. Treating rough cofactors as 1 is invalid; incorporating them needs their exact prime parities or certified square-class identifications.

A conventional dense elimination on t+1 selected rows costs O(t^3) bit operations and O(t^2) bits of state. Thus y approximately r is not a soft-r matrix charge. Choosing y<=r^(1/3) makes this particular elimination affordable in soft r, but does not force t+1 completely smooth discriminants. Faster or sparse elimination must be charged with an actual bound, rather than inferred from input sparsity.

Finally, even a nonzero parity nullvector only proves that the corresponding signed product of D0 is an integer square V^2. One can compute that exact product and V, and U0=product(B/H) modulo N, in soft r. The final test is gcd(U0-V,N) or gcd(U0+V,N). A proper gcd requires an orientation split between P and Q. Rank deficiency by itself does not prove this; the already trivial square rows illustrate the distinction. The structured catalog's exclusion of a=0 does not establish the missing sign split.

## 4. Common-a composition scope

The C progression fixes a, not D0: the actual B has the canonical cubic lift and its carry, and D0=(B^2-4aCN)/M changes with C. Ordinary binary-quadratic-form/class-group composition takes forms in the same quadratic order, so it cannot compose these varying discriminants merely because a is shared. Where the discriminants do coincide, the exact duplicate screen above already gives the valid factor-or-global-orientation alternative for general rows, and always factors for distinct structured descriptors in one window. A different common-order construction could still be useful, but must supply that construction and a relation with a proved independent orientation, within its acquisition cost.

The concrete unresolved arithmetic target is therefore a source-specific theorem forcing a useful integer-square relation (with charged parity computation), or an exact carried norm/composition that produces a second root orientation. Equations (1)-(3), smooth parts, and matrix nullity alone do not supply it. No smoothness heuristic, class-number assumption, or independence assumption was used.
