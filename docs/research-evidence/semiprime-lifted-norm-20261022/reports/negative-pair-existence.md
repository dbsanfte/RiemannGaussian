# Negative lifted norms: sharpened consumer and exact existence target

22 October 2026. Focused continuation after the root's negative-norm lemma. The lemma removes an important nontriviality condition from the consumer. No universal existence theorem or cheap square-class alignment transformation was found. No examples, implementation, tests, repository edits or frozen-report changes.

## The sharpened target really is arithmetic, with no hidden root labels

Put M=m³ and restrict to acquired negative norms z_j=-D_j s_j². For two rows in the same positive integer square class D,

    v_i²+MD s_i²=4a_iN,
    v_j²+MD s_j²=4a_jN.

Cauchy on (v_i,sqrt(MD)s_i) and (sqrt(MD)s_j,±v_j) gives

    |v_i s_j ± v_j s_i|≤4N sqrt(a_i a_j/(MD))
                         <4N/sqrt(m)<N, m≥17.

The product of the two displayed integers is divisible by N, since v_i² s_j²-v_j² s_i²=4N(a_i s_j²-a_j s_i²). Neither integer is zero precisely when v_i²/a_i differs from v_j²/a_j: equality of v_i²/s_i² and v_j²/s_j² is equivalent to equality of those invariants by the two positive norm equations. Thus, if these invariants differ, both displayed integers are nonzero and smaller than N in magnitude. Their product is divisible by squarefree N, so their gcds with N are proper. This requires no hidden choice of local square-root signs.

Consequently a strengthened paid screen groups the acquired negative norms by the previously reviewed exact coprime-base square-class signatures, then compares the rational invariant v_j²/a_j to one representative in each group by cross multiplication. A differing value immediately supplies the two gcd inputs above. If every group has constant invariant, there is no nonproportional negative pair in the acquired family. All integer descriptors have O(log N) bits, and grouping/comparison/recovery retain soft O(m) total work for an O(m) family.

This is stronger than an unspecified 'useful pair' premise. The remaining EXISTENCE statement is now explicit and entirely public:

    Among the acquired pairs (a_j,v_j), do two positive integers
        B_j=(4a_jN-v_j²)/m³
    have square product, while a_i v_j²≠a_j v_i²?

For a polylogarithmic bounded public twist family, replace v_j by v_j+t m³ and retain B_j>0. The same consumer and inequality apply without change. The exceptional small m<17 can be handled by fixed finite methods; it does not affect the asymptotic issue.

## Why the most direct forcing attempts do not yet prove existence

There are O(m) acquired B_j, but their sizes are O(m⁴). The square-class grouping is exact and cheap; there is no established bound of o(m) on its possible occupied classes for this special native sequence. A count of roots modulo m³ does not give such a bound on INTEGER square classes. This observation is not a lower bound or a counterfamily theorem.

The relation M B_j=4a_jN-v_j² does give explicit quadratic-residue restrictions at selected auxiliary primes. Product/quadratic reciprocity turns these into constraints on certain characters of B_j, but equality of finitely many such character values is not an identity saying B_i B_j is an integer square. An actual bound on the square-class rank, or an exact relation among the full valuations, is still needed. No such native bound was proved here. The earlier coprime-base preprocessing records the valuations relative to its acquired pairwise-coprime basis without factoring, but does not supply a bound on that basis rank.

For fixed a, taking the opposite Hensel representative -v leaves B unchanged and v²/a unchanged, so the new lemma correctly identifies that pair as proportional. Varying v by tM may change its square class and invariant; no constant or polylogarithmic choice of t is currently proved to force a repeated class. Enumerating every lift in the real negative interval has about sqrt(aN)/M candidates for that a. In the N~m⁶,a~m scale this is about sqrt(m) per row, hence potentially m^(3/2) candidates, already beyond the desired uniformly soft-m family. Even that enumeration count alone supplies no repeated-class theorem.

## A constructive norm-composition attempt, with its exact size issue

One can preserve the SAME square class D using the norm identity in Q(sqrt(-MD)). Starting from (v,s,a), choose public c,d and form

    v'=cv-MD ds,
    s'=dv+cs,
    a'=a(c²+MD d²).

Then v'²+MD s'²=4a'N exactly. For integer d≠0, a'≥a MD≥m³, so this does not remain in the native small-multiplier range 1≤a'<m. For d=0 it is the trivial proportional scaling excluded by the invariant test. Rational c,d can in principle make the norm multiplier small; integrality of v',s', small integer a', and an admissible lifted representative must then be acquired. Solving those exact denominator/integrality conditions is a norm representation problem, not supplied by the composition identity.

More generally, aligning a NEW row with an existing D asks for integers (v',s',a') satisfying

    v'²+MD s'²=4a'N,
    1≤a'<m,
    v' in the selected bounded set of cubic-root representatives.

A second nonproportional solution is sufficient by the lemma and is the clearest next constructive target. A rational parametrization through the first solution does not provide it: with unit denominators the earlier conic calculation yields a globally proportional modular root. Any proper nonunit encountered in that parametrization already factors N, but no short public parameter menu is proved to force such a denominator. The size inequality now shows why nonproportional INTEGRAL solutions would be enough; it does not acquire them.

## Relevance of known consumers and the exact missing theorem

The previously inspected Lehman/Harvey approximation theorem supplies a small-multiplier representation when searching over a larger trace/multiplier space; it does not state that these fixed cubic-root representatives contain two representations with a common D. SQUFOF consumes proper square-form infrastructure events in a fixed discriminant; the present a-dependent norm fields/discriminants are not one supplied common class group. Coprime-base refinement gives the exact cheap pair consumer, not the relation-existence theorem. Smoothness heuristics or generic lattice independence assumptions are not substituted for that theorem.

The strongest positive next statement would therefore be either:

* a deterministic soft-m constructor of a SECOND nonproportional bounded integral solution of the displayed positive norm equation for one acquired D; or
* a theorem that an explicit O(m polylog N)-size native/twist family must contain the displayed repeated-square-class/different-invariant pair.

Neither was established in this bounded pass. The negative-norm lemma materially strengthens the available consumer and makes its sufficiency fully public. Universal square-class recurrence remains the precise open premise; no general impossibility or improved factoring rate is asserted.
