# Native-family grouping: exact deletion simplification

24 October 2026. Scratch only. No new localization exponent is claimed.

## Nonaxis root cosets are never broken by public zero deletion

Use the exact scalar-catalogue parameters. The hard branch gives N>256k^4 and k>16. Since D=ceil sqrt(kN), M=ceil(4D/H)+2, H=k^2,

    HM <= 4 sqrt(kN)+3H+4.

For b!=0 and any acquired row,

    |E|=|a+bN+lambda| >= N-H-k > HM.

The final strict inequality follows already from N>256k^4,k>16: the 4sqrt(kN) term is <N/(4k^(3/2)), and the remaining 4H+k+4 is <6k^2, far smaller than N. Thus E/H cannot lie in [-M,M]. In particular NO nonzero-product row is publicly deleted; every acquired modular root coset for ab!=0 remains complete.

For b=0 the only pairs are (k,0),(-k,0), and lambda=kt with 0<=t<k. Exactly two rows have E divisible by H:

    (k,0,H-k): E=H,
    (-k,0,k): E=0.

Both indices are inside the search window. The a=0,b=+-k axes have b!=0 and no deleted rows. Complete-swap pruning removes exactly their two partners (0,k,H-k),(0,-k,k). Therefore all four affected rows are axes. Sign closure is compatible with these deletions. This is an exact global statement, not an asymptotic exceptional-row estimate.

Consequently a native-family sharing construction may use complete root cosets throughout the entire nonzero-product catalogue. It need not model arbitrary missing phases there. The four axis cosets alone need explicit missing-row handling.

## Grouping attempts and actual costs

After complete swaps, choose representatives with |b|<=|a|, so |b|<sqrt k. The fixed-b population is soft(k/|b|), apart from the already accounted ramified root multiplicities. Separate ordinary queries cost more than the shared degree-J evaluator; their square-root costs do not combine into a new improvement. Grouping by the smooth discriminant valuation yields the existing exact root-coset tiling, whose paid sum remains soft sqrt(kh).

A distinct representation is p-adic analytic phase grouping: restrict a=a0+L t within a fixed valuation stratum, with L supported on 2,3. A square-root branch has a finite Taylor polynomial modulo H once sufficiently many powers of L vanish modulo H. Choosing L approximately k^epsilon gives bounded degree depending on epsilon. For unit a,b and after swap, the number of residue groups is O(L sqrt k), before logarithmic valuation/branch factors; each group's total expanded points is still charged to the acquired soft-k catalogue.

This is an exponent-space polynomial phase, not an algebraic low-degree curve of ring-valued target points. Replacing the modular root representative by a polynomial lift Lambda(t) changes the actual target by q^(-floor(Lambda(t)/H)). The shared finite clock interval then acquires a t-dependent shift. No contraction of these polynomial-phase targets with their varying clock shifts was established. The phase representation is not claimed as an executable faster query.

The deletion simplification above is constructive new bookkeeping. It may remove a distraction in later native grouping work, but no new sharing mechanism with an improved query exponent was found here.
