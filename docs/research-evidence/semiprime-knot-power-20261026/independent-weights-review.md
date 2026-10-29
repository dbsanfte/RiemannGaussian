# Independent review: independent weights

26 October 2026. Primary-source/algebra review; no experiments or repository edits.

**Final disposition: corrected PASS.** The author has withdrawn the generic-p inference and explicitly states the separate naturality condition and native failure. The original discovery and its proof are retained below as review history. The separately normalized p=1 product and Seifert determinant pass.

## 1. Total multigrading does not establish the required ambient morphism

The color-count argument correctly proves all displayed algebra/coalgebra equalities and

    (phi_T tensor phi_T) tau = tau (phi_T tensor phi_T).

The product, coproduct and antipode in Kashaev–Mangazeev Theorem 2, equations (11)–(13), make the multigrading immediate. Their exchange equation (26) also preserves each color's TOTAL multiplicity. Thus the asserted simultaneous equivariance is sound.

However, the inference that this automatically makes phi_T an admissible automorphism for Garoufalidis–Kashaev's Hopf f-object/Yetter–Drinfeld construction has a genuine missing condition. GK Section 3.1 starts with a braided monoidal category C and requires phi to be an automorphism IN C. Naturality of its braiding implies separate sliding:

    tau (phi tensor id) = (id tensor phi) tau,
    tau (id tensor phi) = (phi tensor id) tau.

These are stronger than simultaneous equivariance. They fail for a generic independent diagonal phi_T in KM's deformed braiding. Indeed KM equation (4), for i>j, gives

    tau(e_i tensor e_j) = -(1-p)e_i tensor e_j - e_j tensor e_i.

The coefficient of e_i tensor e_j in the first separate-sliding difference is

    -(1-p)(t_i-t_j).

Over the universal independent-parameter ring this is nonzero. The source's scalar automorphism t_i=t for all i avoids this issue. At p=1 it also disappears. Therefore generic-p Section 1 may retain the multigraded algebra/coalgebra automorphism and simultaneous-equivariance observations, but cannot claim that GK's categorical construction already produces the independent-weight Yang–Baxter operator from them. A different construction or direct proof of YBE/rigidity would be needed. This review does not claim no other deformed independent-weight model exists.

Primary checks: KM arXiv:2505.15569v1, equations (4), (11)–(13), (26); GK arXiv:2311.11528, Section 3.1 (Remark 3.1, Definition 3.2, Theorems 3.5–3.6), and the local published PDF text. https://arxiv.org/html/2505.15569v1 ; https://arxiv.org/html/2311.11528 .

## 2. The positive p=1 tensor statement survives

At p=1 KM equation (4) is the negative flip on degree-one generators. Equations (11)–(13) are the ordinary super exterior Hopf algebra; its decomposition into one-mode super Hopf tensor factors is valid. Each independent diagonal scaling is now an even morphism and satisfies separate sliding. Tensoring the already normalized one-mode Alexander knot maps, then reordering the factors with the super symmetry, gives

    J_T(K) = product_i K(t_i) Id_(2^m).

This is a valid independent normalized tensor construction. It neither needs a singular generic-p modified-dimension quotient nor proves equality to every generic-p GK/KM normalization. Its state rank and the absence of a new scalar contraction are correctly charged. Specializing t_i=eta^(2i+1) retains the correct arithmetic clock and all collisions.

## 3. Integral determinant and normalization

Under the report's explicitly stated convention K(t)=t^(-L)det(tV-V^T), simultaneous row/column permutation of V tensor D-V^T tensor I decomposes it into the m blocks t_i V-V^T. Hence equation (4) follows exactly. A simultaneous permutation contributes no determinant sign. The prefactor det(D)^(-L) is a known unit, so the equality is valid over any commutative ring with unit t_i, including at K(t_i)=0 and zero divisors. There is no determinant pivot inversion. If another Seifert representative has an overall sign/unit normalization, that convention must be fixed first, as the report already does. The order 2Lm and O(Lm) sparse-entry count are correct; an implicit Kronecker descriptor is not its acquired determinant.

The twisted-torsion discussion is safely subordinate to this exact determinant; no rational denominator is used to justify a singular composite-ring evaluation.

## 4. GK equation (101) versus Table 2

The source distinction is accurately recorded. The HTML Section 7.2 states equation (101), Lambda_1=Delta(t_1)Delta(t_2), without qualification, and Table 2 displays a question mark over that equality. The local published text also contains equation (101) and the question-mark table (printed p.110). Definition 7.1 defines the (1,1)-entry; Conjecture 7.2 separately concerns the whole endomorphism being scalar. The report correctly avoids upgrading this mixed presentation into a proved identification of every normalization. Its independently chosen p=1 tensor construction suffices for the positive product statement.

Conclusion: correct the generic-p Hopf-f/YBE inference in Section 1. The p=1 independent Alexander product, finite-ring Seifert determinant, normalization warnings and unpaid acquisition accounting remain valid. No exponent improvement follows.

## 5. Final corrected-report verification

Reread the corrected independent-weights.md and updated two-mode-deformation.md. Independent-weights now distinguishes simultaneous covariance from an ambient-category morphism, gives the necessary (p-1)(t_2-t_1)=0 condition, explains why native distinct geometric weights force p=1, and preserves the separate diagonal Nichols model. These changes resolve the substantive gap. Its p=1 tensor identity and determinant remain valid and acquisition remains unpaid.

The updated two-mode report explicitly withdraws its generic braid claim and supplies a direct polynomial YB defect. From its table, writing A=1-pb and U=a-1+(p-1)b, the 012-to-003 coefficient difference is

    (1-a)A - [(1-a)A^2-pb(1-b)U]
      = pb[(1-a)A+(1-b)U]
      = p b^2 (p-1)(a-b).

Thus b=pa gives -p^3 a^3(p-1)^2; b=a/p gives a^3(p-1)^2/p^2. Both are units for native p=q in the specified short clock range. On b=1/(pa), the additional factor a-b=(pa^2-1)/(pa) is also a unit when the positive exponent 4i+4 is below both eta orders, as it is for the stated native range. The four-state determinant p^4(ab)^8 remains a unit, correctly separated from YB validity. The corrected report now treats the resulting generic object only as a formal invertible operator.

The full-table determinant factorization checks arithmetically, and the direct defect suffices to reject the particular native Hecke extension; no new test campaign is needed. The lawful p=1 specialization and the separate diagonal-Nichols rank-four calculation survive. No general representation obstruction or scalar-query lower bound is asserted.
