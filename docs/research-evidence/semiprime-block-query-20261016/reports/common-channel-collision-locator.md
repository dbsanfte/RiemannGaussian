# The common divisor of the Cartier channels is exactly the collision locator

2026-10-16. Exact field-side positive interface suggested by the new paid arbitrary-point channel vector. This does not acquire its polynomial common divisor in nearlinear time.

Work in either actual hidden field K. Let q and all distinct supplied z_j lie in one odd-order subgroup G, let q have order R>L, and let B>=2 be dyadic. Define F(t)=P_L(t;q), D(t)=product_j(1-t/z_j), E_B=D_B(t^B)/D(t), and

    F(t)E_B(t)=sum_(r=0)^(B-1)t^r N_r(t^B).

Let H be the monic greatest common divisor of all N_r in K[Y]. Then

    H(Y)=product_(j:F(z_j)=0)(Y-z_j^B).             (1)

The node powers are distinct. In particular this is the powered collision locator, rather than a polynomial whose roots are the unit rows. On the retained actual source it has o(m) degree in each hidden field; that degree statement is inherited from the reviewed unit-row-density count.

Proof. Pass to an algebraic closure solely to analyze roots. The F roots q^(-i), 0<=i<L, are distinct and lie in G. The E_B roots are exactly omega^a z_j for each j and 1<=a<B, with omega a primitive B-th root of unity. They are all simple and mutually distinct: an equality between two such roots equates an odd-order node ratio to a dyadic root, forcing the same node and the same phase. None lies in G, so these roots are also disjoint from F. Thus FE_B is squarefree and has nonzero constant coefficient.

A polynomial A(Y) divides every N_r(Y) if and only if A(t^B) divides FE_B(t), since reduction modulo the monic A(t^B) leaves the independent residue classes t^r. Consequently a nonzero xi is a common channel root if and only if the full B-element fiber {t:t^B=xi} occurs among the roots of FE_B. A fiber contains at most one point in G. If that point is not a supplied z_j, the mask supplies none of the nontrivial dyadic phases, and F supplies only the single odd-subgroup point, so the fiber is incomplete. If it is z_j, the mask supplies all B-1 other phases, and the fiber is complete precisely when F(z_j)=0. Fibers with no G point cannot be complete: every E_B root has a supplied G node in its own fiber, and F has no root in such a fiber. Zero is not a channel-common root because FE_B(0)=1.

Every complete fiber is simple in FE_B; therefore its corresponding common root has multiplicity exactly one. This proves (1), including empty collision sets. The argument is a proof-side extension-field factorization, with no extension construction assumed free algorithmically.

## Why this is a potentially useful target, and what is unpaid

The independently reviewed block-transform primitive computes the entire length-B vector (N_r(X))_r at ONE arbitrary supplied scalar X in soft O(J+B+L/B+sqrt L) work, including X values at powered targets. With B=Theta(L/J) in the balanced regime J~sqrt L, it therefore gives a paid evaluation oracle for a family of degree-O(J) polynomials whose COMMON factor selects exactly the rare collision rows. This differs from ordinary row-value moments, which retain poles at the many unit rows.

The common factor itself is not supplied by these point evaluations. Its small degree does not establish an output-sensitive common-gcd algorithm from this oracle, and does not imply sparse coefficients or free collision syndromes. Repeating scalar evaluation/interpolation at Theta(J) points is quadratic in the balanced regime, not the desired clock. Polynomial gcd computation over Z/N also needs a factor-aware leading-coefficient/pivot contract; the hidden field statement (1) is not a licensed field-gcd black box over the composite ring.

This leaves a concrete positive research question: can the structured channel family and its paid arbitrary-point vector oracle acquire the common divisor, or a factor-selective consequence of it, without first acquiring all degree-O(J) channel polynomials or all J target values? No such algorithm is proved here. This identity is not a general acquisition lower bound or a new full factorization theorem.

Prerequisites: block_transform/report.md SHA-256 825aaaa7d10637eddcf38a7b8e8f2241a70984c4b94c506372e922b845b2fe70; decimation/report.md SHA-256 65a5c827a64b5c035d3d0a7bed445c6970910f9f92749309878d1e1520e5c4fd. Their source manifests provide the inherited actual local-order and row-density premises. No repository changes or builds were made.
