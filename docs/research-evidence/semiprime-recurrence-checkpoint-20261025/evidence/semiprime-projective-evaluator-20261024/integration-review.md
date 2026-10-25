# Independent integration review

24 October 2026. **PASS**, no draft corrections requested. The primary-literature independent PASS was received before this review was frozen. No draft, frozen source or shared repository file was edited by this reviewer.

Exact reviewed drafts:

- journal-append.md: `58f49b573cd41573b18aee464c28a21d02e371929ca50803d9791566d9d6cbbc`.
- agents-append.md: `dab884b4353ede1654fa49e8169dbced03836aa6d5de81446ea38c8609260a7e`.

Source and independent review:

- literature.md: `83184aa38af9e438ffa27207cef4eeda6bfc347e8b8fa2fa00eaa505e475c1a3`.
- literature-review.md: `7e3265cc6578d9c3b800188eb4b7c5e919258cd5e17dd581696ad7068b5d1824`.

The actual compact circuit is faithfully integrated. With d_s the acquired coefficients of the short q-Pochhammer polynomial, B_b(T;X)=sum d_s X^(b-s)T^s is EXACTLY prod_(r<b)(X-q^rT). Its evaluations at the fixed nodes q^(ba) cover disjoint full blocks, and the explicitly acquired shorter tail covers the remaining factors. Powering X only through b, the fixed-node monic product/remainder circuit, t output products and the tail all fit soft(b+t) arithmetic gates and paid constants. There is no X-dependent inversion or hidden degree-L input vector. This really compiles a uniform one-point circuit, including at zero values; it does not improve the already known one-point complexity. Executing it over the rank-J quotient or separately at J points carries the stated J factor and remains worse than the shared-block baseline.

The drafts distinguish the 1987 output-CIRCUIT-length theorem from a uniformly fast construction. Their field-size and coprimality qualifications and missing selected factor-image data match the independent primary audit. A short linear answer circuit may contain the unknown root as a field scalar; its existence does not acquire that scalar. The 1988 constructive GCD comparison is separately supported by the checked cached primary and independent review: its Algorithm Polynomial GCD operates on coefficient vectors through the INPUT degree bound and Theorem 6.1 charges that unary degree. It does not require a supplied root, and the drafts correctly avoid attributing the 1987 initialization limitation to the 1988 algorithm. Neither is promoted to a deterministic unknown-composite collision selector.

The few-point MPE and spiroid statements retain the correct supplied coefficient arrays, degree terms and finite-ring scope. In particular the spiroid theorem really covers arbitrary scalar residue rings deterministically; it is not rejected on a nonexistent known-prime premise. The subpolynomial overhead is not called polylogarithmic. The degree-J call would need the missing outer remainder, and the lawful degree-L+1 padding charges the dense outer input and k^(2+o(1)) execution. A quadratic-algebra reduction and a short-circuit-input version are not silently granted. The source date/version distinctions are preserved by the pinned report and its review.

The pruning paragraph faithfully summarizes this reviewer's bounded attempt. A block has the exact map (Z,A,B)->(PZ,PA+S0 Z,PB+Sw Z). A genuinely certified unit block contributes only regular terms before a later local reset; after the reset a common nonzero factor preserves the local ratio. The missing certificate is exactly that block's original scalar product query. Using the actual existing oracle in one-child bisection gives a geometric sum of sqrt(JL/2^d), still soft sqrt(JL). The short residue/cyclic boundary data were not a certificate of those products. No new formal report or acquisition theorem was created from that duplicate gate.

The short Padé identity is correct in the stated Taylor expansion at ZERO. For any supplied UNIT alpha, 1/(X-alpha)=-sum_(n>=0)X^n alpha^(-n-1), so

    [X^L] G_L(X)/(X-alpha)
           =-alpha^(-L-1)sum_(r=0)^L g_r alpha^r
           =-alpha^(-L-1)G_L(alpha).

No evaluation denominator is inverted at a hit: alpha itself is a supplied unit. If alpha=V_j, F=(X-alpha)Q_alpha and Q_alpha*(G_L/F)=G_L/(X-alpha) is an exact rational-series identity at every finite precision, independently of hit status. Therefore that particular early-window condition cannot select alpha; its first polynomiality-discriminating coefficient is exactly the original endpoint test. The infinity polynomial part does not become a supplied short vector. This is a scoped test of the stated shortcut, not an impossibility claim for all implicit GCD algorithms.

The antipodal duplicate summary is accurate. On the actual canonical parity repair, raw b_(k-j)=center(-b_j+2a) has the same parity as b_j, so a'_j=a'_(k-j)=A exactly. With tau=(2A-b'_j-b'_(k-j))/k in {0,...,4}, ell_j+ell_(k-j)=-H tau and V_jV_(k-j)=beta^[2(N+A)]q^(-tau). These geometrically varying centres and their normalized varying starts are precisely the already tested full-colour construction in frozen colour-fusion.md, with a changed constant carry menu. All rows and original product support are retained; no new fixed-degree terminal sharing follows. The decision not to generate a duplicate report or claim a new geometric-centre algorithm is faithful to the work performed.

Both drafts lead and conclude with the unchanged acquired soft sqrt(JL)=soft k^(3/2) whole-family cost. They present the compiled circuit as genuine input for future selection work, not as a completed selector or an achieved sixth-rate factorizer. No supplied factor seed, local prime/order oracle, polynomial-size circuit existence result, finite example campaign or backend implementation is substituted for acquisition.

This review covers mathematical/source integration only. Exact repository append, prefix preservation, frozen-evidence counts and concurrent-file preservation remain the responsibility of root's separate validator. The review does not assert that a new append or post-append preservation check has already run.
