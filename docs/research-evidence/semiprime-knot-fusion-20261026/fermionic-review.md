# Independent review: fermionic/domain-wall fusion

2026-10-26. Read `fermionic-fusion.md` and checked the relevant primary equations in Caradoc–Foda–Wheeler–Zuparic arXiv:math-ph/0702012v2 (1),(33), Zhao–Yang–Zhang arXiv:hep-th/0506070v4 (II.1)–(II.2), and Foda–Wheeler arXiv:1205.4400v2 (47). No experiment campaign or repo edits.

**Verdict:** the displayed polynomial DW identity, unit prefactors, R-matrix algebra and two-channel determinant calculation are correct, conditional on passing the actual roots of the chosen K. Two scope/notation corrections should be retained in later citations: the root list must include the half-center recentering, and the collision specialization is a conditional algebraic test, not a documented attained native catalogue example or a no-go theorem for every graphical fusion.

## Source-to-polynomial DW gauge

At u=v=0, beta_j=0 the primary source gives a_1=a_2=1, b_1=alpha_r, b_2=-alpha_r and c_1=c_2=sqrt(1-alpha_r²). Its equation (33) specializes to

    Z=prod_r sqrt(1-alpha_r²) * prod_(r<s)(1-alpha_r alpha_s).

A diagonal basis gauge on each horizontal line multiplies its two c-types by reciprocal factors. Choose the orientation with c_2 normalized to 1 and c_1=1-alpha_r² (or swap the labels with the corresponding boundary convention). The fixed DW horizontal boundary states make the net c-type imbalance one on each row. Internal gauge factors cancel and the row boundary contributes 1/sqrt(1-alpha_r²), giving exactly D_n=prod_(r<s)(1-alpha_r alpha_s). Reversing the gauge gives the additional product prod_r(1-alpha_r²), as reported. Deriving this in a formal square-root localization and recognizing that the resulting gauged partition function is polynomial proves the identity in Z[alpha], so it can be specialized without constructing square roots.

For alpha=(iota*t_i,-iota/x_j), the within-clock products are -(t_i t_h), within-root products are -(x_j x_l)^-1, and cross products are t_i/x_j. Thus equation (2)'s signs are correct. The auxiliary quadratic algebra is finite free and étale for odd N; it is not assumed to be a field. Odd-order group elements cannot equal -1, proving every within-block and gauge factor unit. No clock/target collision denominator is inverted. The final product contains only iota², so it lies in R.

## Root and scalar convention requiring precision

Equation (3) is correct for d=2L: the sign from prod_j(x_j-t_i) is +1, and K(t)=c t^-L prod_j(t-x_j) gives precisely the displayed c^-m, root-product and clock-power factors. The clock exponent m(m+2) is correct.

However, for the *new ordinary half-center knot* K, these roots are v=x/eta and v^-1=eta/x for representatives of the original opposite pairs x,q/x. Equivalently they are the entire remaining original row list divided by eta. They are not the unrescaled original x_j and their inverses. The report's explicit factorization of K can be taken as the defining convention for its x_j, in which case all calculations are valid, but its opening phrase “original native scalar rows and their explicit inverses” should be clarified before integration. The correct root list is directly acquired in soft O(L); no unknown polynomial factorization is needed.

## Crossing and rank-one channel correction

Algebraizing the primary R-matrix with x=e^(2(u_1-u_2)), t=e^(2gamma), h²=t gives exactly the entries in (4). The central determinant is (x-t)/(tx-1), so the full ordinary matrix determinant is its square. At t=-1, all native odd-order ratios have 1+x unit and the crossing is invertible. At t=x=q, the central block is (q+1)^-1[[eta,q],[1,eta]], a rank-one block with unit amplitude 2eta/(q+1), and the complete R has rank two.

The projectors Pi=vw/(2eta), Q=I-Pi and basis B=(v,u), v=(eta,1), u=(-eta,1), are valid over R with determinant 2eta. Conjugating D=diag(f,g) gives [[s,d],[d,s]] exactly. The Schur formula fg=s(s-d²/s) is valid only when s is a unit. At the conditional specialization x=a^-1, f=0, g=1-q and s=d=(1-q)/2 is a unit; the Schur correction is therefore zero. At x=b^-1 the same argument has d=-s. These calculations correctly show that this particular projected scalar s loses a genuine zero of the two-factor transfer even when its pivot and local fusion amplitude are units.

**Scope:** the construction does not exhibit a specific semiprime/controller/catalogue/root satisfying x=a^-1 for a fixed selected pair. It proves an identity *whenever that collision occurs*, and the condition is compatible with the odd-order/unit assumptions. Existing full-prefix coverage may guarantee some local collision somewhere, but supplies neither a fixed attained example here nor identification of every Alexander tangle with D. Hence this is a test of the stated diagonal two-line determinant/projection ansatz; it is not a certified counterexample to every exact Yang–Baxter fusion identity. A full graphical rule may retain a different amplitude or channel sum, which must still be acquired and shown to preserve the cross product. The report's explicit disclaimer about D should remain attached to this conclusion.

## Rectangular identity and cost

The quoted small partial-DW determinant entries and exponential prefactor match primary equation (47). Its vertical product ratio can telescope formally, but the canceled interior factors are exactly the potentially nonunit factors. Clearing denominators restores an orbit-length interior product (up to endpoint factors), so no zero-safe shortcut follows by evaluating only the rational endpoint ratio. This is an audit of that explicit specialization, not a general obstruction to polynomial rectangular formulas.

The report consistently charges n=m+2L line labels, expanded lattice/determinant sizes, and the remaining long scalar amplitude. Unit certificates avoid unnecessary evaluation of the two within-block products but do not compute the cross norm. No soft O(L+sqrt m) algorithm is established, and no correction from the reviewed calculation is both known-unit and sufficient to remove the native collision factors.
