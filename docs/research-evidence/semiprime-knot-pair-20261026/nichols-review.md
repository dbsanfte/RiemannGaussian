# Independent review of the rank-four Nichols packet

26 October 2026. Reviewed `nichols-rank-four.md`. Algebraic checks pass for the displayed R, both rotated inverse solves, determinants, enhancement, and trefoil correction. The required restriction is identification scope: this fixes an explicit local convention, not yet a universal identification with the normalized Links–Gould map used by Ishii/Kohli. The positive trefoil in this convention agrees with the inverse-variable version of Kohli's displayed trefoil.

## Checked local algebra

I independently transcribed the sixteen R images, using column inputs ij and row outputs kl, over Q(a,b). The check script `check_nichols_review.py` constructs the matrices and performs symbolic rational identities; it does not sample residues. Its denominators are powers of a,b, so after clearing those monomials the checks are integral Laurent identities and specialize to every commutative ring where a,b are units. A temporary Python environment `/tmp/nichols-review-venv` contains SymPy; no repository files changed.

The right-action closure has the following useful direct consistency check. For the primitive action u▷x_j=u x_j−t_j chi(u,x_j)x_j u, chi(x1,x2)=−1 and chi(x2,x1)=−z. Thus x1▷x2=x1x2+b x2x1=e3 and x2▷x1=x2x1+az x1x2=e3/b when abz=1. Associativity gives 1▷e3=(1−a)e3+b(1−b)e3/b=(2−a−b)e3. Acting on e3 by x1 gives coefficients b−abz=0 on x1x2x1, and by x2 gives 1−1=0 on x2x1x2. Equal-generator actions vanish from x_i²=0. The coproduct coefficients follow from primitive multiplication with diagonal crossings. This checks that the advertised closure is substantive, and it uses no inverse of 1−a,1−b or a collision polynomial. Extending the source's generic identity is justified by these universal Laurent formulas, provided the claimed generic source module/YB convention is the stated one; I did not replace the parent's planned full64-word YB check with a generic-field assertion.

The independent matrix checks establish:

* det R=det tildeR=(ab)^4 and det tilde(R^-1)=(ab)^−4.
* Both printed solves (6),(7) satisfy T x=y and U x=y in every coordinate, with the report's index rotation ij→kl mapped to (k,i)→(l,j).
* The inverse exists using only monomial unit denominators. The table (4) is consistent with the displayed sparse blocks; the script computes R^-1 independently for the rotated/trace checks.
* With mu=diag(1,−1,−1,1), both weighted partial traces of R and R^-1 equal I. Multidegree conservation also gives the stated mu⊗mu commutation.
* The entire cut positive-trefoil endomorphism, not merely its00entry, equals J(a,b) I with J=1−(a+b)(1−a)(1−b).
* J=ab[(a+a^-1−1)(b+b^-1−1)+1−ab] exactly.

The enhancement identities and the unknot normalization do not independently prove that the cut endomorphism of every knot is scalar. They suffice for the checks actually made here, alongside the rigid-YB construction, and the report correctly avoids invoking the general GK scalarity conjecture for the trefoil calculation.

## Mirror/parameter audit: explicit limitation

I additionally computed the negative-trefoil endomorphism and verified

    tr_2[R^-3(I tensor mu)] = J(a^-1,b^-1) I.

This is an exact inversion statement for these two braids. It must not be generalized to every knot without an intertwiner or variable/orientation audit.

Primary comparison: Kohli, *The Links-Gould invariant as a classical generalization of the Alexander polynomial?*, https://arxiv.org/abs/2505.08296, Definition2.16 and Proposition2.18. In the source's n=1 twist-knot case, the displayed Laurent polynomial is

    1−a^-1−b^-1+a^-2+b^-2+2a^-1b^-1
       −a^-2b^-1−a^-1b^-2 = J(a^-1,b^-1).

(The local PDF extraction writes its inequalities as > and < where the mathematical cases include the indicated endpoints; the explicit trefoil coefficient, rather than that extraction, is the relevant comparison.) Hence one can reconcile this single knot by exchanging positive and negative trefoils, or by inverting both variables. One cannot infer solely from this match that the entire packet's R realizes Kohli's universally normalized invariant at the same a,b. A framing/unit/gauge/orientation identification remains a separate task. Keep `J_trefoil` or “our positive two-braid trefoil scalar” as the formula's name until that audit is proved.

The ordinary symmetric Alexander factor K_3(T)=T+T^-1−1 is unchanged by variable inversion; therefore the report's elementary product comparison remains valid within its stated R convention. At ab=q^-1, its additive correction 1−q^-1 is a unit. With both variables inverted, the corresponding correction is 1−q, also a unit. Neither can be discarded as a multiplicative normalization. This still is not an attained native trefoil collision: its Alexander zeros have even order6 whereas native supplied arguments have odd order. An independently established figure-eight calculation is insensitive to exchanging the two knot mirrors because the figure-eight is achiral; that fact does not by itself identify arbitrary parameter conventions, but avoids the trefoil's chirality ambiguity.

## Status and reproducibility

The review does not establish general Links–Gould identification, arbitrary-knot scalarity, a fast acquired-knot evaluator, or a native collision counterexample. It confirms the local Laurent algebra and precisely delimits the trefoil diagnostic. Run

    /tmp/nichols-review-venv/bin/python check_nichols_review.py

from this directory. Output is stored in `nichols-review-validation.txt`. The parent's full64-word exact Laurent YB verification remains independent and complementary.
