# Independent review: scalar-audit.md

26 October 2026. Verdict: the figure-eight formula, native squared-quantum dictionary, and exact resultant-25 certificate check out. The report correctly limits its conclusion to an arbitrary-knot symbolic diagnostic, not an attained native-catalogue counterexample or a fast oracle. No source report or repository was edited.

## Variable and theorem check

Checked arXiv:2509.10911v3 (17 December 2025), introduction after Conjecture 1.4 and Remark 1.7, equations (10),(13): https://arxiv.org/html/2509.10911v3 . The n=1 identification is explicitly stated as proved by the common skein characterization. Equation (13) gives

    (t0,t1)=(Q^(2alpha),Q^(−2alpha−2)),
    (t,tildeq)=(Q^(2alpha+1),Q²).

Hence tildeq=eta² requires Q=eta, not Q=eta². With t=eta^(−2i−2), the two Ishii variables are eta^(−2i−3),eta^(2i+1), as claimed. If an explicit value of the representation variable Q^alpha is needed, it is s0^(−2i−3), using the already acquired s0²=eta. No fractional exponent or unknown discrete logarithm is required. Swapping the two Ishii variables uses the invariant's stated symmetry. This dictionary is distinct from merely setting a numerical finite exponent alpha at Q=1.

The source notes simultaneous inversion of its representation variables relative to older papers. That convention matters for chiral-knot formulas. The specific figure-eight polynomial below is invariant under each inversion separately, so the report's use of old variables is safe here.

## Figure-eight polynomial

Inspected De Wit's arXiv:math/0004170v3, §4.1's conversion to link-invariant variables and §4.3's LG^2 table: https://arxiv.org/pdf/math/0004170 . For rank two, its P=q_old^(2alpha+1). The printed formula is exactly

    P²+P^(−2)−3(q_old+q_old^(−1))(P+P^(−1))
       +2(q_old²+q_old^(−2))+7.

Substitution P=t or t^(-1), q_old=eta or eta^(-1), yields the report's (4). In particular the q_old in this formula corresponds to Q, while tildeq=Q². The report has not confused the squared quantum parameter. Setting eta=1 gives (t+t^(-1)−3)², matching the normalized ordinary Seifert Alexander polynomial K_4_1(T)=3−T−T^(-1) after squaring. That consistency check is secondary to the primary full formula.

## Exact certificate and ring inference

Read the adjacent standard-library script and executed its exact polynomial/Bareiss arithmetic, without any residue sampling. It returns

    g mod f = [-1,−3,2,3,8,−6]       (ascending powers),
    Res(f,g mod f)=25.

Its monic remainder loop and 11-by-11 Sylvester matrix have the correct degree bounds (6 and 5); pivot swaps retain their determinant sign, and each Bareiss division is checked exact. This establishes the reported r polynomial and resultant. The factor eta^8 clearing the Laurent expression is a unit.

The resultant-adjugate identity gives integer polynomials U,V with U*f+V*r=25. Thus in **any commutative quotient with f(eta)=0 and 5 invertible**, r is a unit, with inverse V/25. This proves the stronger ring statement in the report, including the native squarefree composite ring if that conditional collision relation holds there. On a single hidden residue component it proves the same nonvanishing/unit conclusion there. The prepared factors exceed 16H, so characteristic 5 is already absent. No target value is inverted and no generic-field argument is silently specialized through a pole.

The factor f=eta^6−3eta³+1 is equivalent to K_4_1(eta³)=0 because eta is a unit. Therefore the target pair product is zero whenever f=0, while the coupled scalar is a unit away from 5. The positive real f-root cited in the report has infinite order, so an abstract large-order condition alone cannot restore a universal polynomial implication. This does not construct a finite eta whose orders and primitive native catalogue simultaneously satisfy every growing arithmetic condition.

## Native scope and trefoil convention

The acquired native K has degree growing with k, comes with a specific sparse Seifert realization and original catalogue labels, and is not asserted to be the figure-eight polynomial. Equality of Alexander polynomials would not by itself determine its LG invariant or specify its topology. Therefore the report correctly does not turn this symbolic counterexample into a guaranteed native rejection or a complexity theorem. A native-specific collision relation for the chosen actual knot remains a separate question.

For comparison, the independently derived operator-convention trefoil scalar in `nichols-rank-four.md` is F_plus(a,b)=1−(a+b)(1−a)(1−b). Kohli arXiv:2505.08296 Proposition 2.18 at n=1 prints F_plus(a^(-1),b^(-1)). The former report now includes an explicit qualification: the same canonical trefoil/mirror and parameter dictionary is not claimed proved. Simultaneous inversion changes its correction from 1−(ab) to 1−(ab)^(-1), so it must not be ignored even though both are units on native ab=q^(-1). The figure-eight formula and resultant certificate are unaffected because their source expression has the separate inversion symmetries noted above.

No new factorization exponent or native prefix algorithm follows from this audit.
