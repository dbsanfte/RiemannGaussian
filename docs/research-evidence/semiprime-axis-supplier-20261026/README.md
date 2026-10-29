# Smaller factor-information target and paid phase preparation

26 October 2026. This continues the native string-boundary and projective
investigation, with the user's string-theory proposal retained unchanged.

**Progress: a weaker, fully costed input requirement for the arithmetic
consumer. No cheaper whole-family acquisition or complete sixth-exponent
factorization has been established.** The useful new combination is the
native large-order preparation with a restricted Harvey–Hittmeir lattice
search. Residue and interval information can be combined in that search.
The retrospective also proves a uniformly covered two-coefficient target
by combining the old torus arithmetic with complementary monic families.
The proposed knot/string phase selectors have not yet acquired those
coefficients within the target budget.

The retained native query bound is
`soft O(J+sqrt(Jh))=soft O(k^(5/4))`, with the old once-only terminating
extractor where needed. This is a bound for that route, not a general
factoring record. The all-semiprime `soft O(N^(1/6))` goal remains open.

## 1. One correct residue now needs a smaller modulus

Work on the existing prepared branch

    N=P Q, P<Q, N<=k^6, k=2*3^e ~ N^(1/6), H=k^2,
    q=beta^H, ord_P(q),ord_Q(q)>16H.

For an acquired unit-residue palette of size S modulo a public n dividing k,
containing P mod n, a restriction of Harvey–Hittmeir Algorithm 4.3 costs

    soft O(S*r + sqrt(N)/(n*r)^(3/2) + S + 1),

where r is its integer interval parameter. The palette's acquisition is
additional. The source lattice is constructed for every retained residue
and centre; neither coefficients nor starts are implicit inputs.

If `n >= S*k^(1/3)`, choose `r=ceil(16k/S)`. There are soft O(k)
actual giant steps and fewer than k baby steps. Their base is
`alpha=beta^(n^2)`. Since `q=alpha^(H/n^2)`, both local alpha orders
exceed 16H; no new order finder or roughness assumption is required.
All lists, modular powers, sorting, polynomial coefficients, evaluations
and recovery fit soft O(k) BIT operations.

Consequences, with constant factors absorbed in the parameter choice:

* One correct residue modulo `n~k^(1/3)~N^(1/18)` suffices.
* At `n=k`, a covering palette of `O(k^(2/3))` residues suffices.
* A palette for either factor may be complemented by `N/sigma mod n`.

Global matches are processed with their integer labels and exact quadratic
factor recovery before deletion. A true giant cannot be deleted at a wrong
baby index because of the local order bound. After deletion, a saturated
polynomial evaluation contains a difference with proper gcd: no remaining
giant is globally equal to a baby. This consumer therefore does not need
the generic short-annihilator extractor. Zero coefficients in the quadratic
and literal-zero exponent labels are handled explicitly. An incorrect
palette returns a verified factor or bounded failure, never a primality
claim.

This is a specialization of an existing algorithm, not a claim of a new
general factoring theorem. See [the construction](parameterized-controller.md)
and [independent review](review-restricted-residue.md), based on
[Harvey–Hittmeir, Proposition 3.3 and Algorithm 4.3](https://arxiv.org/html/2105.11105).

## 2. A genuine hybrid: coarse residue plus narrow interval

Suppose an acquired list has A rectangles `(sigma mod n, [L,U])`, with
integer `2<=L<=U<=floor(sqrt N)` and `U<=2L`. At least one rectangle
contains the true smaller factor with the stated residue. Handle point
intervals by checking the candidate divisor. For the others put

    Delta=sum_rectangles (U-L)/L.

Running the same lattice centre loop inside each supplied interval gives
`O(A+r*Delta)` starts, sharing one baby alphabet. Its cost is

    soft O(A + r*Delta + sqrt(N)/(n*r)^(3/2) + 1).

In particular `A=O(k)` and `Delta/n <= k^(-1/3)` suffice for soft O(k).
Dyadic upper weights for Delta make parameter selection exact with
O(log N)-bit arithmetic; there is no expensive accumulation of rational
denominators. The initialized proof and its order guard are in
[the joint-information review](joint-information-review.md).

Thus a residue modulus of order `k^(1/6)` combined with a supplied interval
of relative width of order `k^(-1/6)` is already enough. Neither input
alone reaches the target using these parameters. This gives a concrete
way for two representations to contribute complementary information.
It does not assume such a rectangle list is already acquired or covered.
Enumerating every residue and interval restores the old cost.

## 3. A paid order condition at both primes

The factor relation also repairs the phase-filter premise. Test the integer
progressions `1 mod M` and `N mod M` through `floor(sqrt N)`. If P is 1
mod M the first contains it; if Q is 1 mod M the second contains P.
Every queried integer is below Q, so any nonunit product gives proper gcd P.
Both products cost `soft O(1+sqrt(sqrt(N)/M))` in total.

With `M=3^(2e+1)`, unit continuation certifies both q orders coprime to 3
at soft O(sqrt k) cost. With `M=3^(e+1)`, soft O(k) certifies that all
native root clocks `beta^(H/d)`, d dividing k, have the same odd,
3-coprime local orders. This is factor-or-certificate preparation; it does
not force continuation or reveal a factor residue. The new residue consumer
can exclude a few more public ramification classes, but those exclusions
leave Theta(k) possible full-k colours, too many for its permitted palette.

See [the gate and attempted suppliers](order-residue-supplier.md) and
[independent review](review-order-gate.md). The corrected fixed-residue
cyclotomic norm is a faithful filter for that residue; only combining all
channels restores the whole unfiltered predicate.

## 4. What still has to be acquired

There are two different useful outputs. An arbitrary odd-axis collision
supplies its own legal exponent residue and transports to the b=0 kernel.
The new lattice consumer instead requires information about the actual
factor P. An accidental alias is not automatically a P residue, and equal
root-clock orders do not establish that identification.

The exact axis recurrence has certified short pivots, but its state still
contains a vector of long initial products. Acquiring those values costs
`soft O(m+sqrt B)` for an axis cap B. The full universal-kernel refinement
has a different first-query cost, `soft O(N^(1/4))`; the shortened axis
clock must not be confused with that full kernel. See
[the finite recurrence calculation](residue-recursion.md).

The next useful acquisition result is therefore either a covered list of
factor rectangles satisfying the joint density bound, a covered residue
palette meeting Section 1, or a faster collision statistic with its own
valid decoder. Another endpoint identity alone does not provide any of
these. The present findings sharpen those targets without claiming the
user's whole-family acquisition milestone has been met.

## 5. Retrospective: a stronger, uniform handoff

At the user's request, three further investigations audited the old
representations against the new information requirement. The strongest
positive composition is proved in [hybrid-handoff.md](hybrid-handoff.md):

* The old torus construction supplies exact factor provenance at whichever
  prime is nonsplit. Its point and order preparation were already paid.
* Two explicit complementary monic row families guarantee that ONE family
  has a unique hit at that prime, without a smaller-prime orientation
  assumption. They have no axis rows.
* Marking each row by its integer factor colour makes two FIRST-ORDER
  coefficients U,V satisfy U/V=R mod n at that prime. The other prime
  needs no matching promise. Norm/gcd validation and HH recovery cost
  soft O(K), where K is the actual conductor-aware torus scale.

The existing shorter weighted family gives another uniform target:
partition nonaxis rows by their common content g and use modulus K/g.
All hits in one sector share the same coarse factor tag, so two leading
coefficients suffice even with multiple hits. The exact torus axis rows
also carry the full factor tag. Their candidates can be combined into ONE
paid HH palette. This does not apply to arbitrary scalar-axis aliases.

These are different tradeoffs. The monic version requests only first
order but retains a longer clock; its initialized fallback costs soft
K^(3/2). The content-sector version retains the shorter clock but needs
first nonzero slices with their precision costs. Neither acquisition is
yet soft O(K); the existing soft K^(5/4) full-query algorithm remains
the better completed route.

The audit did not find a previously acquired output that already closes
the gap. The old row/Euclidean interval projections retain too much total
width, and the cheap finite boundary cancels the entire marked interior
factor. Those concrete checks and the positive provenance proof are in
[intervals](retrospective-intervals.md), [colours](retrospective-colours.md),
[provenance](retrospective-provenance.md), and
[the independent final review](two-monic-review.md).

The next acquisition attempt can now target just these two first-order
coefficients, using the old three-state reset/quotient-gradient formulation
as an initialized starting point. Its long terminal transfer remains the
operation that must be improved. This is a narrower uniform problem,
not a claim that the coefficients are already cheap.

## Evidence and preservation

The Sol 6.1 investigations, cross-reviews, joint-information review and
primary-agent integration review are paper proofs and cost audits, not
Lean certificates. The new rank-three preprint is compared only
for its stated scale; the positive result uses the older rank-two HH proof.
No numerical campaign, new factoring implementation, Lean or public-asset
change, commit or push was performed. Prior evidence, document prefixes
and concurrent work were preserved. See [review metadata](review.json),
[source pins](sources.json) and [manifest](manifest.json).
