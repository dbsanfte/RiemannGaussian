# Native support-cost thinning: laminar phase classes, exact optimization and balanced price

26 October 2026. Paper-only arithmetic construction; no frozen repository edits, code, tests or numerical campaign. **Positive algorithm:** the full native ellipse supports an exact soft-K minimum-window-cost unique-hit selection, via a newly proved laminar refinement of its phase classes. Its conditional query cost is soft(K+sqrt(S_opt)). **Scoped price:** covering ALL unit colours with these rows and their full-bin integer interval windows still has S_opt=Omega(K^(5/2)) in balanced bins at the sixth-root scale. No uniform exponent gain or general acquisition lower bound is claimed.

Sources actually read: frozen unique-weighted `unique-cover.md` and `completed-source.md`, the unique-pole scalar E recurrence and prior variable-window interface. The old engine soft(J+sqrt(sum h_j)), exact row extrema, virtual weighted-Gauss cover and the maximal-content eligible-domain nesting are prior credit. The new native ingredient here is nesting of the FINER phase-support classes, which permits exact cost optimization rather than arbitrary representative choice.

## 1. Supplied native row supports and public costs

Per bin B<=R<2B use the completed coefficient ellipse and its filtered shortest axes. The full acquired coloured incidence count is <23K. For a row v=(a,b,j), its hypothetical support is the public set of unit residues r modulo K satisfying f_j(r)=0 modulo H, f_j(X)=aX²+ell_j X+bN. The incidence theorem identifies this with the equal-canonical-phase class among eligible colours for this fixed coefficient pair. The correct bin's actual nonsplit factor belongs to exactly one support in any support PARTITION; that row has exactly one good-field clock hit. All other selected rows miss.

For each candidate row compute the exact range over the CLOSED real bin [B,2B] of

    g_v(x)=(a*x+b*N/x+ell_j)/H.

Endpoints and, when ab>0, x=sqrt(bN/a) if it lies in the bin suffice. Critical values are (2*sign(a)*sqrt(abN)+ell_j)/H. Integer/radical comparisons give exact rounding in polylog N time. Set l_v=ceil(min g_v), u_v=floor(max g_v), and h_v=max(0,u_v-l_v+1). This is the old exact-window operation. Every actual integer hit for an R in the bin is retained; the window lies within the original safe short horizon. All candidates' metadata cost soft K.

Zero-width/empty windows retain their support metadata but cost zero and need no numerical query. A support covered by such a row cannot contain the ACTUAL R of a correct bin: its required integer hit would have to lie in that empty range. No factor residue is asserted from this logical elimination.

## 2. New refinement: fine phase supports are laminar within a direction

Opposite coefficient/phase rows have the same hypothetical support: their polynomials differ by overall minus sign and an H-multiple. Their index functions differ by sign plus an acquired INTEGER carry, so their exact rounded window lengths are identical. Thus discard one sign orientation without increasing the optimum, while retaining its actual representative metadata. Fix a primitive integer direction v0=(a0,b0), with canonical a0>0, and admitted positive multiples d*v0. Both a0,b0 are 3-units, as proved in unique-cover: otherwise stationarity would require v3(d)>=e, contradicting the ellipse product bound. Put v=v3(d). The eligible domain is

    D_v={odd unit r: a0*r²=b0*N modulo 3^(e-v)},

with the independent parity eligibility condition already satisfied by an admitted d. These D_v increase with v.

For EVERY odd unit r modulo H define the same unwrapped function

    L0(r)=−a0*r−b0*N*r^-1.

The actual phase of d*v0 is d*L0(r) modulo H. Its 2-part is constant on the eligible odd colours. Indeed r^-1=r modulo 4, hence d*L0(r)=−d*(a0+b0N)*r modulo 4. Admissibility gives d*(a0+b0N) even; multiplication by two different odd r therefore changes this by a multiple of 4. This proof covers both-odd cores and the opposite-parity case where d must be even.

Consequently phase equality for this d is EXACTLY

    L0(r)=L0(j) modulo 3^(2e-v).                 (1)

The 3-unit part of d does not affect that equivalence relation. Equal-v rows have the same phase partition on the same domain. If v1<=v2, the first threshold in (1) is finer and D_v1 is contained in D_v2. Any intersecting support class at v1 is therefore contained in the v2 class. This proves LAMINARITY of all these finer supports within the direction; no assumption that canonical carry integers themselves agree is used.

Different HIGH directions (maximal available v>=1) have disjoint eligible domains, by the existing determinant/ellipse theorem. All v=0 nonaxis supports and all axes are singletons. Thus the entire candidate support collection, after identical sets are identified, is a laminar family globally, with ordinary singleton leaves shared between directions. No new vector outside the paid ellipse is constructed.

## 3. Execute the exact minimum-cost partition

Obtain every support membership list by grouping each completed coefficient fibre by ACTUAL phase. Its total membership size is <23K. Group by primitive direction and content valuation, identify equal sets (retain the cheapest actual row), and build the laminar containment forest. An element-to-current-class map while processing nested levels finds parents; exact sorted membership lists or hashing can verify them. The total sparse input and processing are soft K, not K times the number of directions.

For a support node S, compare:

* its cheapest available actual row, of cost h_v;
* the sum of optimum costs of its maximal proper child supports, PLUS available singleton-row costs for every remaining colour of S not covered by those children.

If any such leftover colour has no available singleton row, the split option is forbidden. Leaves need NOT be singletons; choosing their own actual row is always allowed. This point prevents an invalid children-only cover of a parent with uncovered colours. All sums and choices use O(log N)-bit integers. Duplicate support descriptions are compared by cost before the recursion.

The maximal high-domain roots are disjoint. Outside those roots, the original own-colour Gauss fallback is a singleton by unique-cover, so the remaining colours have actual singleton candidates. The dynamic program therefore returns a support PARTITION of all unit colours. It is EXACTLY minimum S=sum h_v among all partitions using this supplied row collection and full-bin windows: laminarity makes any partition either choose a node or partition it among proper descendants/remaining singleton leaves.

Every output is an ACTUAL row, phase and window. The proof of exactly one good hit in the whole correct bin therefore survives unchanged, with J_new<=phi(K). Unit amplitudes or the existing first-jet/subresultant consumers remain available. With the OLD unequal-window engine the completion costs

    soft(K+sqrt(S_opt)).                         (2)

Acquire this metadata/DP for ALL bins first, then try only S_opt<=K² (or a fixed polylogarithmic extension) bins before expensive fallback. If the correct bin qualifies, this really gives a complete soft-K factoring branch. Otherwise later bins retain the old soft K^(5/4) fallback. No earlier expensive wrong bin is allowed to invalidate the conditional cost. This algorithm does not claim that the qualifying condition always occurs.

## 4. A balanced-bin price for this precise thinning route

Here is a stronger native price than merely counting J. It concerns ALL-colour partitions from this completed ellipse with the full-bin interval windows above, not selective arithmetic factor search, adaptive subbins or implicit scalar algorithms.

### Most colours cannot belong to a large phase class

For each maximal high direction, its coarsest phase partition is one of the OLD complete quadratic fibres. In each parity-adjusted branch its parameter runs through all m=3^v residues, with a 3-unit quadratic coefficient after completing the square. Exactly 2/3 of those parameters are units after the square translation; their square value has exactly TWO preimages. Thus at least 2/3 of the colours in that whole domain lie in coarsest classes of size two.

The opposite square-root branches cannot mix phases: after division by 3^v, the phase modulo 3 is −2*(d/3^v)*a0*r, a nonzero value that changes sign between branches. This also covers even d via the parity-adjusted m. The old chirp truncation applies because g²<=K/sqrt3.

By (1), all other available supports in that direction refine the coarsest classes. Other high directions are disjoint; low-content and axis supports are singletons. Colours outside high domains also only have singleton supports. Therefore at least (2/3)*phi(K)=2K/9 unit colours belong ONLY to available supports of size at most TWO. This is a property of this complete native family, not an assertion that every phase fibre is small.

### Cheap coefficients cover few such colours

Let L_v=max(|a|,|b|). For a real threshold T<K, all nonaxis pairs with L_v<=T and content g number at most 4*floor(T/g)^2. Each has at most 2g eligible colours, so the total number of colours covered by ANY such rows is less than

    8T²*sum_(g|K)1/g <18T².                    (3)

Axes have L=K and are excluded at this threshold. Set T=sqrt(K)/32. Removing the colours in (3) leaves more than K/5 colours that (i) require L_v>=T and (ii) can only be covered by supports of size at most two. Every support partition therefore chooses at least K/10 rows for these colours and obeys

    sum_(chosen rows)L_v >=K^(3/2)/320.          (4)

No enumeration of unknown R or generic-position assumption occurs.

### Full-bin window length prices those coefficients

Assume B/sqrt(N) lies in [1/2,2]; any other fixed balanced range only changes constants. Let W_v=max g_v−min g_v. Put U=aB,V=bN/B. Differences at B,3B/2,2B give

    H*(g(2B)−g(B))=U−V/2,
    H*(g(3B/2)−g(B))=U/2−V/3.

Solving gives |V|<=18H W_v and |U|<=10H W_v. Since max(|U|,|V|)>=sqrt(N)*L_v/2,

    h_v >=W_v−1 >=sqrt(N)*L_v/(36H)−1.         (5)

The centered phase only translates g and does not change its range. Summing (5), using (4) and at most phi(K) chosen rows, yields

    S_opt >=sqrt(N)*K^(3/2)/(11520H)−K/3.

At the actual sixth-root scale N=Theta(K^6), this is Omega(K^(5/2)). Thus THIS exact optimum remains far above K² in balanced bins asymptotically. The old square-root evaluator on such a partition retains its K^(5/4) exponent. Empty windows or choosing different unit multiples in a direction do not evade (5).

## 5. Scope and next constructive direction

The laminar theorem gives a real native selection algorithm and optimizes the OLD variable-window engine rather than merely relabelling a generic polynomial. It can exploit instancewise cheap supports and gives the explicitly scheduled conditional soft-K branch (2). It does not yield a uniform exponent gain.

The price proof is deliberately narrower than a factoring lower bound: it requires an all-unit-colour partition from these ellipse rows and queries every integer of each row's full real-bin range. It does NOT apply to a cheaper selective colour predicate, a genuinely sparse arithmetic clock mask, a different covered family, or a direct scalar contraction avoiding those interval costs. Those are precisely the remaining ways native arithmetic could improve the algorithm. No field samples or examples are used as a coverage theorem.
