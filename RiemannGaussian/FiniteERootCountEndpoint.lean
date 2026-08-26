import RiemannGaussian.FiniteERootCountContinuity
import RiemannGaussian.FiniteZeroVectorSplit

/-!
# Evaluation of the finite root count at the zero endpoint

The positive-parameter root count is already known to be constant, including
through collisions.  This file evaluates that constant.  At a simple real
root `a` of `A`, write `A(z) = (z - a) Q(z)`.  Any nearby root of
`A + I * tau * A'` satisfies

`z - a = -I * tau * (A'(z) / Q(z))`.

The quotient tends to one at `a`, so its real part is positive nearby and the
imaginary part of `z` is negative for `tau > 0`.  Combining this directional
motion with the collision-safe root-moment argument evaluates the count just
to the right of zero and hence at every positive parameter.
-/

open Polynomial Filter Topology

namespace RiemannGaussian

noncomputable section

theorem exists_real_root_downward_radius
    {A : ℝ[X]} (hA : A.Separable) {a : ℝ} (ha : A.eval a = 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {tau : ℝ}, 0 < tau → ∀ {z : ℂ},
        z ∈ (finiteEPolynomial A tau).roots →
        ‖z - (a : ℂ)‖ < delta → z.im < 0 := by
  let gamma : ℂ := (a : ℂ)
  have hgamma : A.eval₂ Complex.ofRealHom gamma = 0 := by
    dsimp [gamma]
    change A.eval₂ Complex.ofRealHom (Complex.ofRealHom a) = 0
    rw [Polynomial.eval₂_at_apply]
    simp [ha]
  let Q : ℂ[X] := finiteZeroQuotientPolynomial A gamma
  have hderiv : A.derivative.eval a ≠ 0 :=
    separable_eval_derivative_ne_zero_real hA ha
  have hderivComplex :
      A.derivative.eval₂ Complex.ofRealHom gamma ≠ 0 := by
    dsimp [gamma]
    change A.derivative.eval₂ Complex.ofRealHom
      (Complex.ofRealHom a) ≠ 0
    rw [Polynomial.eval₂_at_apply]
    exact Complex.ofReal_ne_zero.mpr hderiv
  have hQself : Q.eval gamma =
      A.derivative.eval₂ Complex.ofRealHom gamma :=
    finiteZeroQuotientPolynomial_eval_self A hgamma
  have hQself_ne : Q.eval gamma ≠ 0 := by
    rw [hQself]
    exact hderivComplex
  let ratio : ℂ → ℂ := fun z ↦
    A.derivative.eval₂ Complex.ofRealHom z / Q.eval z
  have hratio_self : ratio gamma = 1 := by
    dsimp [ratio]
    rw [hQself]
    exact div_self hderivComplex
  have hratio_cont : ContinuousAt ratio gamma := by
    dsimp [ratio]
    change ContinuousAt
      ((fun z : ℂ ↦ A.derivative.eval₂ Complex.ofRealHom z) /
        fun z : ℂ ↦ Q.eval z) gamma
    simpa [Polynomial.eval_map] using
      (A.derivative.map Complex.ofRealHom).continuous.continuousAt.div
        Q.continuous.continuousAt hQself_ne
  have hratio_pos : ∀ᶠ z in nhds gamma, 0 < (ratio z).re := by
    have hclose := hratio_cont
      (eventually_norm_sub_lt (ratio gamma) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hclose] with z hz
    rw [hratio_self] at hz
    have hrele : |(ratio z).re - 1| ≤ ‖ratio z - 1‖ := by
      simpa using Complex.abs_re_le_norm (ratio z - 1)
    have hre : |(ratio z).re - 1| < 1 / 2 := hrele.trans_lt hz
    linarith [abs_lt.mp hre]
  rw [Metric.eventually_nhds_iff] at hratio_pos
  obtain ⟨delta, hdelta, hball⟩ := hratio_pos
  refine ⟨delta, hdelta, ?_⟩
  intro tau htau z hz hzclose
  have hratioRe : 0 < (ratio z).re := hball (by
    simpa [Metric.mem_ball, dist_eq_norm, gamma, norm_sub_rev] using hzclose)
  have hQz : Q.eval z ≠ 0 := by
    intro hzero
    have hratioZero : ratio z = 0 := by simp [ratio, hzero]
    rw [hratioZero] at hratioRe
    simp at hratioRe
  have hzEval : (finiteEPolynomial A tau).eval z = 0 :=
    (mem_roots (finiteEPolynomial_ne_zero hA.ne_zero tau)).mp hz
  have hfactor := sub_mul_finiteZeroQuotientPolynomial_eval
    A (gamma := gamma) (z := z) hgamma
  have heq : z - gamma =
      -Complex.I * (tau : ℂ) * ratio z := by
    dsimp [ratio]
    rw [← mul_div_assoc]
    apply (eq_div_iff hQz).mpr
    change (z - gamma) * Q.eval z =
      (-Complex.I * (tau : ℂ)) *
        A.derivative.eval₂ Complex.ofRealHom z
    change (z - gamma) * Q.eval z =
      A.eval₂ Complex.ofRealHom z at hfactor
    rw [hfactor]
    rw [finiteEPolynomial_eval] at hzEval
    linear_combination hzEval
  have him := congrArg Complex.im heq
  dsimp [gamma] at him
  simp only [Complex.ofReal_im, sub_zero,
    Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, mul_zero,
    zero_add, neg_zero, sub_zero] at him
  rw [him]
  nlinarith [mul_pos htau hratioRe]

theorem exists_zero_root_indicator_radius
    {A : ℝ[X]} (hA : A.Separable) {a : ℂ}
    (ha : a ∈ (finiteEPolynomial A 0).roots) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {tau : ℝ}, 0 < tau → ∀ {z : ℂ},
        z ∈ (finiteEPolynomial A tau).roots →
        ‖z - a‖ < delta →
          upperHalfPlaneIndicator z = upperHalfPlaneIndicator a := by
  by_cases haim : a.im = 0
  · have hareal : a = (a.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using haim
    have haevalComplex : A.eval₂ Complex.ofRealHom a = 0 := by
      have heval : (finiteEPolynomial A 0).eval a = 0 :=
        (mem_roots (finiteEPolynomial_ne_zero hA.ne_zero 0)).mp ha
      rw [finiteEPolynomial_eval] at heval
      simpa using heval
    have haeval : A.eval a.re = 0 := by
      rw [hareal] at haevalComplex
      change A.eval₂ Complex.ofRealHom (Complex.ofRealHom a.re) = 0 at haevalComplex
      rw [Polynomial.eval₂_at_apply] at haevalComplex
      exact Complex.ofReal_eq_zero.mp haevalComplex
    obtain ⟨delta, hdelta, hdown⟩ :=
      exists_real_root_downward_radius hA haeval
    refine ⟨delta, hdelta, ?_⟩
    intro tau htau z hz hzclose
    have hzclose' : ‖z - (a.re : ℂ)‖ < delta := by
      rwa [← hareal]
    have hzlower := hdown htau hz hzclose'
    simp [upperHalfPlaneIndicator, haim, not_lt_of_ge hzlower.le]
  · refine ⟨|a.im|, abs_pos.mpr haim, ?_⟩
    intro tau _ z _ hzclose
    have himle : |z.im - a.im| ≤ ‖z - a‖ := by
      simpa using Complex.abs_im_le_norm (z - a)
    have himclose : |z.im - a.im| < |a.im| :=
      himle.trans_lt hzclose
    by_cases haupper : 0 < a.im
    · have hzupper : 0 < z.im := by
        have habs : |z.im - a.im| < a.im := by
          simpa [abs_of_pos haupper] using himclose
        linarith [abs_lt.mp habs]
      simp [upperHalfPlaneIndicator, haupper, hzupper]
    · have halower : a.im < 0 := lt_of_le_of_ne
          (le_of_not_gt haupper) haim
      have hzlower : z.im < 0 := by
        have habs : |z.im - a.im| < -a.im := by
          simpa [abs_of_neg halower] using himclose
        linarith [abs_lt.mp habs]
      simp [upperHalfPlaneIndicator, haupper, not_lt_of_ge hzlower.le]

theorem eventually_finiteEPolynomial_upperRootCount_eq_zero_right
    {A : ℝ[X]} (hA : A.Separable) :
    ∀ᶠ tau in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      upperHalfPlaneRootCount (finiteEPolynomial A tau) =
        upperHalfPlaneRootCount (finiteEPolynomial A 0) := by
  classical
  by_cases hdegree : A.natDegree = 0
  · apply Filter.Eventually.of_forall
    intro tau
    simp only [upperHalfPlaneRootCount]
    have htauRoots : (finiteEPolynomial A tau).roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [IsAlgClosed.card_roots_eq_natDegree,
        finiteEPolynomial_natDegree hA.ne_zero, hdegree]
    have hzeroRoots : (finiteEPolynomial A 0).roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [IsAlgClosed.card_roots_eq_natDegree,
        finiteEPolynomial_natDegree hA.ne_zero, hdegree]
    simp [htauRoots, hzeroRoots]
  · let S : Finset ℂ := (finiteEPolynomial A 0).roots.toFinset
    have hrootsCard : (finiteEPolynomial A 0).roots.card = A.natDegree := by
      rw [IsAlgClosed.card_roots_eq_natDegree,
        finiteEPolynomial_natDegree hA.ne_zero]
    have hS : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hSempty
      have hrootsEmpty : (finiteEPolynomial A 0).roots = 0 :=
        Multiset.toFinset_eq_empty.mp hSempty
      rw [hrootsEmpty] at hrootsCard
      simp at hrootsCard
      exact hdegree hrootsCard.symm
    let q : ℂ[X] := Lagrange.interpolate S id upperHalfPlaneIndicator
    have hid : Set.InjOn (id : ℂ → ℂ) S := by
      intro x _ y _ hxy
      exact hxy
    have hqeval : ∀ a ∈ (finiteEPolynomial A 0).roots,
        q.eval a = upperHalfPlaneIndicator a := by
      intro a ha
      exact Lagrange.eval_interpolate_at_node upperHalfPlaneIndicator hid
        (Multiset.mem_toFinset.mpr ha)
    have hqdegree : q.natDegree ≤ A.natDegree := by
      have hqcard : q.natDegree ≤ S.card :=
        natDegree_le_of_degree_le
          (le_of_lt (Lagrange.degree_interpolate_lt upperHalfPlaneIndicator hid))
      calc
        q.natDegree ≤ S.card := hqcard
        _ ≤ (finiteEPolynomial A 0).roots.card :=
          Multiset.toFinset_card_le (finiteEPolynomial A 0).roots
        _ = A.natDegree := hrootsCard
    let eta : ℝ := 1 / (4 * A.natDegree)
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    choose evalRadius hevalRadius hqclose using fun a : ℂ ↦
      Metric.continuousAt_iff.mp
        (q.continuous.continuousAt :
          ContinuousAt (fun z : ℂ ↦ q.eval z) a)
        eta heta
    have hclassExists (a : S) :=
      exists_zero_root_indicator_radius hA
        (Multiset.mem_toFinset.mp a.property)
    let classRadius : S → ℝ := fun a ↦ Classical.choose (hclassExists a)
    have hclassRadius (a : S) : 0 < classRadius a :=
      (Classical.choose_spec (hclassExists a)).1
    have hclassify (a : S) :
        ∀ {tau : ℝ}, 0 < tau → ∀ {z : ℂ},
          z ∈ (finiteEPolynomial A tau).roots →
          ‖z - (a : ℂ)‖ < classRadius a →
            upperHalfPlaneIndicator z = upperHalfPlaneIndicator a :=
      (Classical.choose_spec (hclassExists a)).2
    let localRadius : S → ℝ := fun a ↦
      min (evalRadius a) (classRadius a)
    have hlocalRadius (a : S) : 0 < localRadius a :=
      lt_min (hevalRadius a) (hclassRadius a)
    let hnonempty : Nonempty S := hS.to_subtype
    let delta : ℝ := Finset.univ.inf'
      (@Finset.univ_nonempty S _ hnonempty) localRadius
    have hdelta : 0 < delta := by
      apply (Finset.lt_inf'_iff (@Finset.univ_nonempty S _ hnonempty)).2
      intro a _
      exact hlocalRadius a
    have hnear : ∀ᶠ tau in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ∀ b ∈ (finiteEPolynomial A tau).roots,
          ∃ a ∈ (finiteEPolynomial A 0).roots, ‖b - a‖ < delta :=
      (eventually_forall_finiteEPolynomial_root_exists_base_root_in_norm_ball
        hA.ne_zero 0 hdelta).filter_mono inf_le_left
    have hmoment : ∀ᶠ tau in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ‖finiteERootEvalSum A tau q - finiteERootEvalSum A 0 q‖ <
          (1 / 4 : ℝ) := by
      have hambient : ∀ᶠ tau in nhds (0 : ℝ),
          ‖finiteERootEvalSum A tau q - finiteERootEvalSum A 0 q‖ <
            (1 / 4 : ℝ) :=
        (continuous_finiteERootEvalSum hA.ne_zero q hqdegree).continuousAt
          (eventually_norm_sub_lt (finiteERootEvalSum A 0 q) (by norm_num))
      exact hambient.filter_mono inf_le_left
    filter_upwards [hnear, hmoment, self_mem_nhdsWithin]
      with tau hnearTau hmomentTau htau
    have htauPos : 0 < tau := htau
    have hpoint : ∀ b ∈ (finiteEPolynomial A tau).roots,
        ‖q.eval b - upperHalfPlaneIndicator b‖ < eta := by
      intro b hb
      obtain ⟨a, ha, hba⟩ := hnearTau b hb
      let aS : S := ⟨a, Multiset.mem_toFinset.mpr ha⟩
      have hdeltaLocal : delta ≤ localRadius aS :=
        Finset.inf'_le localRadius (Finset.mem_univ aS)
      have hdeltaEval : delta ≤ evalRadius a :=
        hdeltaLocal.trans (min_le_left _ _)
      have hdeltaClass : delta ≤ classRadius aS :=
        hdeltaLocal.trans (min_le_right _ _)
      have hqnear : ‖q.eval b - q.eval a‖ < eta := by
        simpa [dist_eq_norm] using hqclose a (x := b)
          (by simpa [dist_eq_norm] using hba.trans_le hdeltaEval)
      have hindicator :
          upperHalfPlaneIndicator b = upperHalfPlaneIndicator a :=
        hclassify aS htauPos hb (hba.trans_le hdeltaClass)
      rw [hindicator, ← hqeval a ha]
      exact hqnear
    have htarget :
        ‖finiteERootEvalSum A tau q -
          (upperHalfPlaneRootCount (finiteEPolynomial A tau) : ℂ)‖ ≤
            (1 / 4 : ℝ) := by
      rw [← sum_upperHalfPlaneIndicator]
      change ‖((finiteEPolynomial A tau).roots.map q.eval).sum -
        ((finiteEPolynomial A tau).roots.map upperHalfPlaneIndicator).sum‖ ≤ _
      rw [← Multiset.sum_map_sub]
      calc
        ‖((finiteEPolynomial A tau).roots.map fun z ↦
            q.eval z - upperHalfPlaneIndicator z).sum‖ ≤
            (((finiteEPolynomial A tau).roots.map fun z ↦
              q.eval z - upperHalfPlaneIndicator z).map norm).sum :=
          norm_multiset_sum_le _
        _ ≤ (finiteEPolynomial A tau).roots.card • eta := by
          have hle := Multiset.sum_le_card_nsmul
            (((finiteEPolynomial A tau).roots.map fun z ↦
              q.eval z - upperHalfPlaneIndicator z).map norm) eta (by
                intro x hx
                rw [Multiset.mem_map] at hx
                obtain ⟨z, hz, rfl⟩ := hx
                simp only [Multiset.mem_map] at hz
                obtain ⟨b, hb, rfl⟩ := hz
                exact (hpoint b hb).le)
          simpa using hle
        _ = (1 / 4 : ℝ) := by
          rw [IsAlgClosed.card_roots_eq_natDegree,
            finiteEPolynomial_natDegree hA.ne_zero]
          dsimp [eta]
          rw [nsmul_eq_mul]
          field_simp
    have hbase : finiteERootEvalSum A 0 q =
        (upperHalfPlaneRootCount (finiteEPolynomial A 0) : ℂ) := by
      rw [finiteERootEvalSum, ← sum_upperHalfPlaneIndicator]
      apply congrArg Multiset.sum
      exact Multiset.map_congr rfl hqeval
    rw [hbase] at hmomentTau
    let m := upperHalfPlaneRootCount (finiteEPolynomial A tau)
    let n := upperHalfPlaneRootCount (finiteEPolynomial A 0)
    have hcountNorm : ‖(m : ℂ) - (n : ℂ)‖ < 1 := by
      calc
        ‖(m : ℂ) - (n : ℂ)‖ =
            ‖((m : ℂ) - finiteERootEvalSum A tau q +
              (finiteERootEvalSum A tau q - (n : ℂ)))‖ := by ring_nf
        _ ≤ ‖(m : ℂ) - finiteERootEvalSum A tau q‖ +
            ‖finiteERootEvalSum A tau q - (n : ℂ)‖ := norm_add_le _ _
        _ < 1 := by
          rw [norm_sub_rev]
          nlinarith
    have hcountReal : |(m : ℝ) - (n : ℝ)| < (1 : ℝ) := by
      simpa [← Complex.ofReal_natCast, ← Complex.ofReal_sub] using hcountNorm
    have hmnReal : (m : ℝ) < (n : ℝ) + 1 := by
      linarith [lt_of_abs_lt hcountReal]
    have hnmReal : (n : ℝ) < (m : ℝ) + 1 := by
      linarith [neg_lt_of_abs_lt hcountReal]
    have hmn : m < n + 1 := by exact_mod_cast hmnReal
    have hnm : n < m + 1 := by exact_mod_cast hnmReal
    dsimp [m, n] at hmn hnm ⊢
    omega

theorem exists_pos_finiteEPolynomial_upperRootCount_eq_zero
    {A : ℝ[X]} (hA : A.Separable) :
    ∃ sigma : ℝ, 0 < sigma ∧
      upperHalfPlaneRootCount (finiteEPolynomial A sigma) =
        upperHalfPlaneRootCount (finiteEPolynomial A 0) := by
  have hcount := eventually_finiteEPolynomial_upperRootCount_eq_zero_right hA
  have hpos : ∀ᶠ sigma in nhdsWithin 0 (Set.Ioi (0 : ℝ)), 0 < sigma :=
    self_mem_nhdsWithin
  exact (hpos.and hcount).exists

theorem finiteEPolynomial_upperRootCount_eq_zero_of_pos
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : 0 < tau) :
    upperHalfPlaneRootCount (finiteEPolynomial A tau) =
      upperHalfPlaneRootCount (finiteEPolynomial A 0) := by
  obtain ⟨sigma, hsigma, hcount⟩ :=
    exists_pos_finiteEPolynomial_upperRootCount_eq_zero hA
  exact (finiteEPolynomial_upperRootCount_eq_of_pos
    hA htau hsigma).trans hcount

/-- At every positive parameter, the upper-half-plane root count is no larger
than the lower-half-plane root count.  The endpoint theorem discharges the
root-count hypothesis in the finite bridge. -/
theorem finiteEPolynomial_upper_le_lower_of_pos
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : 0 < tau) :
    upperHalfPlaneRootCount (finiteEPolynomial A tau) ≤
      lowerHalfPlaneRootCount (finiteEPolynomial A tau) :=
  finiteEPolynomial_upper_le_lower_of_upper_count_eq_zero
    hA htau.ne' (finiteEPolynomial_upperRootCount_eq_zero_of_pos hA htau)

/-- The upper and lower root factors satisfy the degree inequality required by
the finite cross-angle construction at every positive parameter. -/
theorem finiteEPolynomial_rootFactor_degree_le_of_pos
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : 0 < tau) :
    (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree ≤
      (lowerRootFactor (finiteEPolynomial A tau)).natDegree :=
  finiteEPolynomial_rootFactor_degree_le_of_upper_count_eq_zero
    hA htau.ne' (finiteEPolynomial_upperRootCount_eq_zero_of_pos hA htau)

/-- The finite algebraic cross angle is injective at every positive homotopy
parameter, with no separate root-count or degree assumption. -/
theorem finiteAlgebraicCrossAngle_injective_of_pos
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : 0 < tau) :
    Function.Injective (finiteAlgebraicCrossAngle A tau) :=
  finiteAlgebraicCrossAngle_injective_of_upper_count_eq_zero
    hA htau.ne' (finiteEPolynomial_upperRootCount_eq_zero_of_pos hA htau)

/-- Exact finite algebraic Gram--Weil inertia at every positive homotopy
parameter, with the homotopy root count proved rather than assumed. -/
theorem finiteAlgebraicGramWeilBlockDefect_hasQuadraticInertia_of_pos
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : 0 < tau) :
    HasQuadraticInertia
      (gramWeilBlockDefectOperator
        (𝕜 := ℂ)
        (P := finiteResidualCoefficientHilbert A tau)
        (N := finiteAlgebraicNegativeSpace A tau)
        (finiteAlgebraicCrossAngle A tau))
      (gramWeilBlockDefectQuadratic
        (𝕜 := ℂ)
        (P := finiteResidualCoefficientHilbert A tau)
        (N := finiteAlgebraicNegativeSpace A tau)
        (finiteAlgebraicCrossAngle A tau))
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree
      ((conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau))).natDegree -
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).natDegree)
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree :=
  finiteAlgebraicGramWeilBlockDefect_hasQuadraticInertia_of_upper_count_eq_zero
    hA htau.ne' (finiteEPolynomial_upperRootCount_eq_zero_of_pos hA htau)

end

end RiemannGaussian
