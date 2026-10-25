# Carry-aware native inverse-row pairing

24 October 2026. Scratch only. Read /tmp/semiprime-recurrence-innovation-20261024/euclidean-carry-attempt.md, /tmp/semiprime-differential-query-acquisition-20261023/shared-euclidean-state-attempt.md, and /tmp/semiprime-second-digit-acquisition-20261023/dense-gap-contraction.md. No repository edits, examples or coverage campaign. This derives actual integer transformations and an initialized paired-support branch; it does not obtain a faster whole query.

## Native integer carries

Assume the prepared branch supplies gcd(N,m)=1 and all integers 1,...,m are units modulo N. Let j range over 1,...,m-1, m odd prime, H=m², and let a_j in [1,m-1] represent N/j² modulo m. Define

    v_j=(N-a_j*j²)/m,
    b_j=center_m(-j^(-1)*v_j),
    c_j=m*b_j-a_j*j.

Here j inverse and centering in the definition of b are modulo m. Exact divisibility gives the integer

    t_j=(b_j*j+v_j)/m,
    j*c_j=H*t_j-N.                                  (1)

Nothing drops the carry t_j or replaces this equality by a congruence.

Define the actual residue involution

    j*=[N*j^(-1)]_m in [1,m-1].

Then (j*)*=j and a*=a_(j*) is the representative of a_j inverse modulo m. Set

    rho=(a_j*a*-1)/m,
    nu=(N-j*j*)/m,
    d=(c_j+j*)/m, d*=(c_(j*)+j)/m.

All are exact integers acquired in O(1) arithmetic per j. Equations (1) give

    j*d+nu=m*t_j,
    j* *d*+nu=m*t_(j*),
    j*d-j* *d*=m*(t_j-t_(j*)).                       (2)

Expanding the two c factors gives the further exact identity

    c_j*c_(j*)=2N-j*j*+H*(d*d*-t_j-t_(j*)).         (3)

Thus reciprocal pairing genuinely links the second carries. Equation (3) is not c_j*c_(j*)=N over the integers or modulo N; its H carry must remain.

For the inversion j'=[j^(-1)]_m, one instead has a_(j')=[N²/a_j]_m. It introduces no simpler same-slope identification unless additional congruences of N hold. Composing j->N/j with j->1/j produces the known multiplication-by-N permutation on residues. These are actual native metadata permutations, but permutation alone does not identify row norms.

## Exact leaf transport between inverse rows

Write a=a_j, a*=a_(j*), c=c_j, c*=c_(j*), and native leaves

    L_j(h,k)=c+m*a*h+H*k, 0<=h<m.

Since a* c=c* modulo m, acquire the integer eta=(a* c-c*)/m. Multiplication by the known unit a* gives

    a* L_j(h,k)=c*+m*(h+eta)+H*(rho*h+a* k).

For each h define acquired integer metadata

    h'=[a*(h+eta)]_m,
    sigma(h)=(h+eta-a* h')/m,
    k'=rho*h+a* k+sigma(h).

Then, exactly over Z,

    a* L_j(h,k)=L_(j*)(h',k').                      (4)

The map h->h' is a permutation. For fixed h it carries a contiguous k menu to an arithmetic progression of step a*, not to a contiguous menu of the same length. The constant and h-dependent carry are essential. In particular, even if k ranges over a short O(m) interval, the displayed transformed lift coordinates can range over O(m²). Replacing this sheared arithmetic progression by the partner's old menu loses the exact identity and has no coverage proof.

This identity is stronger than reducing everything to N modulo H, but it is still an index transport. The scalar multiplier a* is a certified unit modulo N, so it preserves local zero support for every transported leaf.

## Actual initialized paired-support algorithm

Given a pair of original finite public domains D_j,D_(j*) (including any restrictions), the following branch is lawful.

1. Acquire (a,a*,rho,c,c*,eta) using exact integer arithmetic. Partition the j permutation into pairs and fixed points in soft m total metadata work.
2. Represent the partner-domain union

       U=D_(j*) union Phi(D_j),

   where Phi is the exact map (h,k)->(h',k') above. Keep two disjoint tagged copies initially. If explicitly acquired equal index leaves occur, keep one copy: multiplicity removal preserves zero support, without division by their values.
3. Acquire the product on U by explicit additive factorial evaluation along each arithmetic k progression. A progression k'=A+a* k gives leaf c*+m*a* h'+H*A+H*a* k, with known-unit step H*a*. Ordinary additive baby/giant factorial arithmetic initializes this product and its interval restrictions, without inverting any leaf. Equivalently evaluate each original row rectangle by its paid gap-corrected factorial constructor. The transported formula (4) changes only a known-unit global multiplier.
4. Take gcd with N. If saturated, subdivide the two tagged components and then their h/k intervals. The already acquired nonzero integer envelopes belong to the ORIGINAL leaves; use those original labels in localization. A transported representative can be larger, so one must not apply the old envelope directly to it. Equation (4) guarantees the same local support, while the original leaf gives the proper-factor certificate.

This is an actual acquired algorithm after the identity. It computes precisely the union support; it neither divides by a potentially nonunit overlap product nor claims that a saturated product itself is a proper factor. Fixed points of j* require no transport and are retained as ordinary single rows.

## Why the tested cancellation is unpaid at soft m

For a supplied h the intersection of a transformed interval and the partner's ordinary k interval is acquired by exact floor/ceiling arithmetic on

    k'=rho*h+a* k+sigma(h).

Thus overlap metadata is computable without evaluating factors. However doing this for every h of every paired row acquires Theta(m²) h-targets in the literal implementation. Combining that metadata with the existing triangular evaluator does not erase those starts; the present Euclidean report identifies exactly that charge. The transformed domain still has its arithmetic progression and h-dependent carry. No identity here turns its full correction product into the inverse of a partner product at a single common shift.

Moreover, cancellation of equal product factors as a rational identity must first test their gcd: those equal factors might contain the only hit. Safe support deduplication is allowed, but deleting factors from both numerator and denominator after a formal quotient is not a hit-preserving rule. The paired algorithm above keeps one copy and therefore stays valid.

## Ledger and outcome

| Operation | Acquired work | Status |
|---|---:|---|
| Native pairing and all integer carries | soft m | paid |
| One supplied h transport/intersection | soft 1 | paid |
| All literal paired h intersections | Theta(m²) targets | exceeds soft m |
| One transported k progression product | soft sqrt(menu length), plus metadata | initialized, division free |
| Original gap-corrected row | soft sqrt(a_j*m) per menu block | existing paid algorithm |
| Whole independent gap family | soft m² for current implementation | unchanged |
| Old sufficient factorial-cover query | soft m^(3/2) | still better available fallback |

The inverse-row relation (4) acquires an exact support-safe permutation with explicit lift shears. Its concrete paired evaluation does not improve the whole-query exponent. The missing operation is shared acquisition of the sheared triangular norm family, or a proved small menu invariant under these carry maps. Neither scalar carry identity (3) nor modulo-H reciprocal pairing supplies that operation.

## Root normalization follow-up: all transported indices enter one class, but the menu expands

Use the root's distinct normalization notation k0* in [0,a*) satisfying b*+m*k0*=0 modulo a*, and z*=(b*+m*k0*)/a*. Then the partner's normalizable class has

    L_(j*)(h',k0*+a* ell)=a* [m(h'+z*)-j*+H*ell].

There is a useful exact strengthening: EVERY transported k' in (4) lies in this one normalizable class modulo a*, regardless of h or k. Indeed

    m*k'=a*(a*h-h')+eta +m*a* k,
    m*(b*+eta)=a*(c+j*),

where every a* in these formulas is the partner coefficient, not multiplication notation. Thus b*+m*k'=0 modulo a*. More unambiguously, writing A=a_j and B=a_(j*), the identities are

    m*k'=B*(A*h-h')+eta+m*B*k,
    m*(b_(j*)+eta)=B*(c_j+j*).

Hence ell=(k'-k0*)/B is an explicitly acquired integer and division of (4) by B gives

    L_j(h,k)=m*(h'+z*)-j*+H*ell.                  (5)

This is a genuine full-row normalization, but NOT into the partner's original short lift menu. The transported k' ranges over O(m²); after division by B the ell menu can still have O(m) length. The original leaf bound can consequently remain O(m³), not O(H). Short-menu unit screening of the original partner k' menu does not apply to these enlarged k' values.

Equation (5) has a transparent direct meaning: since c_j+j*=m*d,

    L_j(h,k)=m*(d+A*h+m*k)-j*.

The Euclidean gap report already studies exactly the missing residues of this rectangle A*h+m*k. Thus reciprocal transport turns all classes into the partner's single normalizable class only by importing the old full rectangle and its carry holes. It does not eliminate the Euclidean correction. At a fixed h, ell advances by one with k, so additive factorial evaluation is paid; across h and all j, acquiring the shared gapped support remains the original unpaid compression.

This resolves the apparent possibility that reciprocal pairing normalizes more classes for free: it does normalize them algebraically, but enlarges the lift range so that the old small-leaf/unit guarantee no longer covers them. No full-menu coverage or exponent gain is inferred.

### Precise interval condition for the unit screen

The phrase short-menu/unit guarantee above is conditional, not a unit claim for the full public k' menu for every B. For k'=k0* (ell=0), or bounded ell with its numerical constant explicitly checked, normalized leaves m(h'+z*)-j*+H*ell have O(H) size and can be screened as units when the bound is strictly below the prepared prime cutoff 16H. For the full original public interval |k'|<=m+2, only ell=O(m/B) follows in general. The normalized magnitude is then O(m³/B), so the interval is not automatically unit-safe for small B. Using the inherited explicit bound |L_(j*)|<=2m³+(5/2)H, the full original menu is unit-safe after division by B when B>=m/4: the bound becomes <=8H+10m<16H for odd m>=3. These normalized integers are nonzero modulo m, so a strict absolute bound below the prime cutoff proves they are units. In contrast the enlarged reciprocal image can have k'=O(m²), ell=O(m), so even B>=m/4 need not shorten its normalized leaves below O(m³). No screening of this enlarged domain has been established.
