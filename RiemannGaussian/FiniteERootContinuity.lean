import RiemannGaussian.FiniteRootCountBridge
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Infsep

/-!
# Coefficient and root continuity for the finite homotopy

This file begins the proof of the remaining upper-root-count homotopy
statement.  It normalizes `E_tau` to a monic polynomial without changing its
roots, proves uniform convergence of all coefficients as `tau` varies, and
specializes Mathlib's quantitative continuity-of-roots theorem to this
family.
-/

open Polynomial Filter Topology

namespace RiemannGaussian

noncomputable section

/-- Monic normalization of `E_tau`.  Its normalizing scalar is independent of
`tau` because the derivative term has smaller degree. -/
def finiteEMonicPolynomial (A : ℝ[X]) (tau : ℝ) : ℂ[X] :=
  C (Complex.ofRealHom A.leadingCoeff)⁻¹ * finiteEPolynomial A tau

theorem finiteEMonicPolynomial_monic
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteEMonicPolynomial A tau).Monic := by
  have hmonic := monic_mul_leadingCoeff_inv
    (finiteEPolynomial_ne_zero hA tau)
  rw [finiteEPolynomial_leadingCoeff hA tau] at hmonic
  simpa [finiteEMonicPolynomial, mul_comm] using hmonic

@[simp] theorem finiteEMonicPolynomial_roots
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteEMonicPolynomial A tau).roots =
      (finiteEPolynomial A tau).roots := by
  rw [finiteEMonicPolynomial, roots_C_mul]
  exact inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (leadingCoeff_ne_zero.mpr hA))

@[simp] theorem finiteEMonicPolynomial_natDegree
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteEMonicPolynomial A tau).natDegree = A.natDegree := by
  rw [← IsAlgClosed.card_roots_eq_natDegree,
    finiteEMonicPolynomial_roots hA,
    IsAlgClosed.card_roots_eq_natDegree,
    finiteEPolynomial_natDegree hA]

/-- Every normalized coefficient depends continuously on the real homotopy
parameter. -/
theorem continuous_finiteEMonicPolynomial_coeff
    (A : ℝ[X]) (i : ℕ) :
    Continuous fun tau : ℝ => (finiteEMonicPolynomial A tau).coeff i := by
  simp only [finiteEMonicPolynomial, finiteEPolynomial, coeff_mul,
    coeff_C, coeff_add, coeff_map, coeff_smul,
    Complex.ofRealHom_eq_coe]
  fun_prop

/-- All coefficients converge uniformly in their index as `tau` tends to a
fixed parameter.  Uniformity is elementary here because every member has the
same finite degree. -/
theorem eventually_finiteEMonicPolynomial_coeff_norm_sub_lt
    {A : ℝ[X]} (hA : A ≠ 0) (tau₀ : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ tau in nhds tau₀, ∀ i : ℕ,
      ‖(finiteEMonicPolynomial A tau).coeff i -
        (finiteEMonicPolynomial A tau₀).coeff i‖ < epsilon := by
  have hfinite :
      ∀ i ∈ Finset.range (A.natDegree + 1),
        ∀ᶠ tau in nhds tau₀,
          ‖(finiteEMonicPolynomial A tau).coeff i -
            (finiteEMonicPolynomial A tau₀).coeff i‖ < epsilon := by
    intro i _
    exact (continuous_finiteEMonicPolynomial_coeff A i).continuousAt
      (eventually_norm_sub_lt
        ((finiteEMonicPolynomial A tau₀).coeff i) hepsilon)
  filter_upwards [(eventually_all_finset
    (Finset.range (A.natDegree + 1))).2 hfinite] with tau ht i
  by_cases hi : i < A.natDegree + 1
  · exact ht i (Finset.mem_range.mpr hi)
  · have hdegreeTau : (finiteEMonicPolynomial A tau).natDegree < i := by
      rw [finiteEMonicPolynomial_natDegree hA]
      omega
    have hdegreeZero : (finiteEMonicPolynomial A tau₀).natDegree < i := by
      rw [finiteEMonicPolynomial_natDegree hA]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hdegreeTau,
      coeff_eq_zero_of_natDegree_lt hdegreeZero, sub_self, norm_zero]
    exact hepsilon

/-- Quantitative persistence of every root of one homotopy member under a
coefficient perturbation. -/
theorem exists_finiteEPolynomial_root_norm_sub_lt_of_coeff_close
    {A : ℝ[X]} (hA : A ≠ 0) {tau₀ tau : ℝ}
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {a : ℂ}
    (ha : a ∈ (finiteEPolynomial A tau₀).roots)
    (hcoeff : ∀ i : ℕ,
      ‖(finiteEMonicPolynomial A tau).coeff i -
        (finiteEMonicPolynomial A tau₀).coeff i‖ < epsilon) :
    ∃ b ∈ (finiteEPolynomial A tau).roots,
      ‖a - b‖ <
        ((A.natDegree + 1) * epsilon) ^
            (A.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  have haeval : (finiteEMonicPolynomial A tau₀).eval a = 0 := by
    rw [finiteEMonicPolynomial, eval_mul,
      (mem_roots (finiteEPolynomial_ne_zero hA tau₀)).mp ha,
      mul_zero]
  obtain ⟨b, hb, hdist⟩ :=
    Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := finiteEMonicPolynomial A tau₀)
      (g := finiteEMonicPolynomial A tau)
      hepsilon haeval
      (finiteEMonicPolynomial_monic hA tau₀)
      (finiteEMonicPolynomial_monic hA tau)
      (by simp [finiteEMonicPolynomial_natDegree hA])
      hcoeff (IsAlgClosed.splits _)
  exact ⟨b, by simpa [finiteEMonicPolynomial_roots hA] using hb, by
    simpa [finiteEMonicPolynomial_natDegree hA] using hdist⟩

/-- Eventual quantitative root persistence along the homotopy. -/
theorem eventually_exists_finiteEPolynomial_root_norm_sub_lt
    {A : ℝ[X]} (hA : A ≠ 0) (tau₀ : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ tau in nhds tau₀, ∀ a ∈ (finiteEPolynomial A tau₀).roots,
      ∃ b ∈ (finiteEPolynomial A tau).roots,
        ‖a - b‖ <
          ((A.natDegree + 1) * epsilon) ^
              (A.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  filter_upwards [eventually_finiteEMonicPolynomial_coeff_norm_sub_lt
    hA tau₀ hepsilon] with tau hcoeff a ha
  exact exists_finiteEPolynomial_root_norm_sub_lt_of_coeff_close
    hA hepsilon ha hcoeff

/-- Qualitative root persistence in an arbitrarily prescribed neighborhood.
This is the usable one-root form of coefficient-to-root continuity. -/
theorem eventually_exists_finiteEPolynomial_root_in_norm_ball
    {A : ℝ[X]} (hA : A ≠ 0) (tau₀ : ℝ)
    {delta : ℝ} (hdelta : 0 < delta) {a : ℂ}
    (ha : a ∈ (finiteEPolynomial A tau₀).roots) :
    ∀ᶠ tau in nhds tau₀, ∃ b ∈ (finiteEPolynomial A tau).roots,
      ‖a - b‖ < delta := by
  have hdegreePos : 0 < A.natDegree := by
    rw [← finiteEPolynomial_natDegree hA tau₀,
      ← IsAlgClosed.card_roots_eq_natDegree]
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩
  have hdegree : A.natDegree ≠ 0 := hdegreePos.ne'
  let M : ℝ := max ‖a‖ 1
  have hM : 0 < M := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right ‖a‖ 1)
  let c : ℝ := delta / (2 * M)
  have hc : 0 < c := div_pos hdelta (mul_pos (by norm_num) hM)
  let epsilon : ℝ := c ^ A.natDegree / (A.natDegree + 1)
  have hepsilon : 0 < epsilon := by
    exact div_pos (pow_pos hc _) (by positivity)
  filter_upwards [eventually_exists_finiteEPolynomial_root_norm_sub_lt
    hA tau₀ hepsilon] with tau ht
  obtain ⟨b, hb, hbound⟩ := ht a ha
  refine ⟨b, hb, hbound.trans ?_⟩
  have hbase :
      ((A.natDegree + 1 : ℝ) * epsilon) = c ^ A.natDegree := by
    dsimp [epsilon]
    field_simp
  calc
    ((A.natDegree + 1) * epsilon) ^
          (A.natDegree : ℝ)⁻¹ * max ‖a‖ 1 =
        (c ^ A.natDegree) ^ (A.natDegree : ℝ)⁻¹ * M := by
      rw [hbase]
    _ = c * M := by
      rw [Real.pow_rpow_inv_natCast hc.le hdegree]
    _ = delta / 2 := by
      dsimp [c]
      field_simp [hM.ne']
    _ < delta := by linarith

/-- Root persistence in the reverse direction, uniformly over every root of
the nearby polynomial.  Unlike the one-root statement above, this says that
no new root value can appear far from the root set at the base parameter.  It
does not assume that either polynomial is separable. -/
theorem eventually_forall_finiteEPolynomial_root_exists_base_root_in_norm_ball
    {A : ℝ[X]} (hA : A ≠ 0) (tau₀ : ℝ)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ tau in nhds tau₀, ∀ b ∈ (finiteEPolynomial A tau).roots,
      ∃ a ∈ (finiteEPolynomial A tau₀).roots, ‖b - a‖ < delta := by
  by_cases hdegree : A.natDegree = 0
  · apply Filter.Eventually.of_forall
    intro tau b hb
    have hroots : (finiteEPolynomial A tau).roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [IsAlgClosed.card_roots_eq_natDegree,
        finiteEPolynomial_natDegree hA, hdegree]
    rw [hroots] at hb
    exact (Multiset.notMem_zero b hb).elim
  · let M : ℝ :=
      ((finiteEPolynomial A tau₀).roots.map fun z ↦ ‖z‖).sum + 1
    have hnorms_nonneg : ∀ x ∈
        ((finiteEPolynomial A tau₀).roots.map fun z ↦ ‖z‖), 0 ≤ x := by
      intro x hx
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
      exact norm_nonneg z
    have hsum_nonneg :
        0 ≤ ((finiteEPolynomial A tau₀).roots.map fun z ↦ ‖z‖).sum :=
      Multiset.sum_nonneg hnorms_nonneg
    have hM : 0 < M := by
      dsimp [M]
      linarith
    have hM_one : 1 ≤ M := by
      dsimp [M]
      linarith
    let qHalf : ℝ := 1 / 2
    have hqHalf : 0 < qHalf := by norm_num [qHalf]
    let epsilonHalf : ℝ :=
      qHalf ^ A.natDegree / (A.natDegree + 1)
    have hepsilonHalf : 0 < epsilonHalf := by
      exact div_pos (pow_pos hqHalf _)
        (by positivity)
    let qSmall : ℝ := delta / (2 * M)
    have hqSmall : 0 < qSmall :=
      div_pos hdelta (mul_pos (by norm_num) hM)
    let epsilonSmall : ℝ :=
      qSmall ^ A.natDegree / (A.natDegree + 1)
    have hepsilonSmall : 0 < epsilonSmall := by
      exact div_pos (pow_pos hqSmall _)
        (by positivity)
    filter_upwards [
      eventually_finiteEMonicPolynomial_coeff_norm_sub_lt
        hA tau₀ hepsilonHalf,
      eventually_finiteEMonicPolynomial_coeff_norm_sub_lt
        hA tau₀ hepsilonSmall] with tau hcoeffHalf hcoeffSmall b hb
    have hcoeffHalf' : ∀ i : ℕ,
        ‖(finiteEMonicPolynomial A tau₀).coeff i -
          (finiteEMonicPolynomial A tau).coeff i‖ < epsilonHalf := by
      intro i
      simpa [norm_sub_rev] using hcoeffHalf i
    obtain ⟨aHalf, haHalf, hdistHalf⟩ :=
      exists_finiteEPolynomial_root_norm_sub_lt_of_coeff_close
        hA hepsilonHalf hb hcoeffHalf'
    have hradiusHalf :
        (((A.natDegree + 1 : ℝ) * epsilonHalf) ^
          (A.natDegree : ℝ)⁻¹) = qHalf := by
      have hbase :
          ((A.natDegree + 1 : ℝ) * epsilonHalf) =
            qHalf ^ A.natDegree := by
        dsimp [epsilonHalf]
        field_simp
      rw [hbase, Real.pow_rpow_inv_natCast hqHalf.le hdegree]
    rw [hradiusHalf] at hdistHalf
    have hnorm_aHalf : ‖aHalf‖ < M := by
      have hmem : ‖aHalf‖ ∈
          ((finiteEPolynomial A tau₀).roots.map fun z ↦ ‖z‖) :=
        Multiset.mem_map.mpr ⟨aHalf, haHalf, rfl⟩
      have hle : ‖aHalf‖ ≤
          ((finiteEPolynomial A tau₀).roots.map fun z ↦ ‖z‖).sum :=
        Multiset.single_le_sum hnorms_nonneg _ hmem
      dsimp [M]
      linarith
    have hrootBound : max ‖b‖ 1 < 2 * M := by
      by_cases hbOne : ‖b‖ ≤ 1
      · rw [max_eq_right hbOne]
        linarith
      · have hone_lt : 1 < ‖b‖ := lt_of_not_ge hbOne
        rw [max_eq_left hone_lt.le]
        rw [max_eq_left hone_lt.le] at hdistHalf
        have htriangle : ‖b‖ ≤ ‖b - aHalf‖ + ‖aHalf‖ := by
          calc
            ‖b‖ = ‖(b - aHalf) + aHalf‖ := by ring_nf
            _ ≤ ‖b - aHalf‖ + ‖aHalf‖ := norm_add_le _ _
        dsimp [qHalf] at hdistHalf
        nlinarith
    have hcoeffSmall' : ∀ i : ℕ,
        ‖(finiteEMonicPolynomial A tau₀).coeff i -
          (finiteEMonicPolynomial A tau).coeff i‖ < epsilonSmall := by
      intro i
      simpa [norm_sub_rev] using hcoeffSmall i
    obtain ⟨a, ha, hdist⟩ :=
      exists_finiteEPolynomial_root_norm_sub_lt_of_coeff_close
        hA hepsilonSmall hb hcoeffSmall'
    refine ⟨a, ha, hdist.trans ?_⟩
    have hradiusSmall :
        (((A.natDegree + 1 : ℝ) * epsilonSmall) ^
          (A.natDegree : ℝ)⁻¹) = qSmall := by
      have hbase :
          ((A.natDegree + 1 : ℝ) * epsilonSmall) =
            qSmall ^ A.natDegree := by
        dsimp [epsilonSmall]
        field_simp
      rw [hbase, Real.pow_rpow_inv_natCast hqSmall.le hdegree]
    rw [hradiusSmall]
    calc
      qSmall * max ‖b‖ 1 < qSmall * (2 * M) :=
        mul_lt_mul_of_pos_left hrootBound hqSmall
      _ = delta := by
        dsimp [qSmall]
        field_simp [hM.ne']

/-- A fixed upper-half-plane root has a nearby upper-half-plane root for all
sufficiently close homotopy parameters. -/
theorem eventually_exists_finiteEPolynomial_upper_root_near
    {A : ℝ[X]} (hA : A ≠ 0) (tau₀ : ℝ) {a : ℂ}
    (ha : a ∈ (finiteEPolynomial A tau₀).roots) (hupper : 0 < a.im) :
    ∀ᶠ tau in nhds tau₀, ∃ b ∈ (finiteEPolynomial A tau).roots,
      0 < b.im := by
  filter_upwards [eventually_exists_finiteEPolynomial_root_in_norm_ball
    hA tau₀ hupper ha] with tau ht
  obtain ⟨b, hb, hnorm⟩ := ht
  refine ⟨b, hb, ?_⟩
  have hle : |a.im - b.im| ≤ ‖a - b‖ := by
    simpa using Complex.abs_im_le_norm (a - b)
  have him : |a.im - b.im| < a.im := by
    exact hle.trans_lt hnorm
  exact by linarith [abs_lt.mp him]

/-- A fixed lower-half-plane root has a nearby lower-half-plane root for all
sufficiently close homotopy parameters. -/
theorem eventually_exists_finiteEPolynomial_lower_root_near
    {A : ℝ[X]} (hA : A ≠ 0) (tau₀ : ℝ) {a : ℂ}
    (ha : a ∈ (finiteEPolynomial A tau₀).roots) (hlower : a.im < 0) :
    ∀ᶠ tau in nhds tau₀, ∃ b ∈ (finiteEPolynomial A tau).roots,
      b.im < 0 := by
  filter_upwards [eventually_exists_finiteEPolynomial_root_in_norm_ball
    hA tau₀ (neg_pos.mpr hlower) ha] with tau ht
  obtain ⟨b, hb, hnorm⟩ := ht
  refine ⟨b, hb, ?_⟩
  have hle : |a.im - b.im| ≤ ‖a - b‖ := by
    simpa using Complex.abs_im_le_norm (a - b)
  have him : |a.im - b.im| < -a.im := by
    exact hle.trans_lt hnorm
  exact by linarith [abs_lt.mp him]

/-- At a parameter where `E_tau` is separable, its upper root count is
locally lower semicontinuous.  Distinct base roots are assigned distinct
nearby roots using the positive infimum separation of their finite set. -/
theorem eventually_finiteEPolynomial_upperRootCount_le_of_separable
    {A : ℝ[X]} (hA : A ≠ 0) (tau₀ : ℝ)
    (hseparable : (finiteEPolynomial A tau₀).Separable) :
    ∀ᶠ tau in nhds tau₀,
      upperHalfPlaneRootCount (finiteEPolynomial A tau₀) ≤
        upperHalfPlaneRootCount (finiteEPolynomial A tau) := by
  classical
  let R : Multiset ℂ :=
    (finiteEPolynomial A tau₀).roots.filter fun z => 0 < z.im
  have hRnodup : R.Nodup := by
    exact (nodup_roots hseparable).filter _
  let S : Finset ℂ := ⟨R, hRnodup⟩
  have hcardS : S.card =
      upperHalfPlaneRootCount (finiteEPolynomial A tau₀) := by
    rfl
  by_cases hS : S.Nonempty
  · let margin : ℝ := S.inf' hS fun z => z.im
    have hmargin : 0 < margin := by
      apply (Finset.lt_inf'_iff hS).2
      intro z hz
      change z ∈ R at hz
      exact (Multiset.mem_filter.mp hz).2
    let separation : ℝ := (S : Set ℂ).infsep
    let delta : ℝ :=
      if (S : Set ℂ).Nontrivial then
        min margin (separation / 3) else margin
    have hdelta : 0 < delta := by
      dsimp [delta]
      split_ifs with hnontrivial
      · apply lt_min hmargin
        exact div_pos
          (S.finite_toSet.infsep_pos_iff_nontrivial.mpr hnontrivial)
          (by norm_num)
      · exact hmargin
    have hdeltaMargin : delta ≤ margin := by
      dsimp [delta]
      split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    have hpersist :
        ∀ z ∈ S, ∀ᶠ tau in nhds tau₀,
          ∃ b ∈ (finiteEPolynomial A tau).roots,
            ‖z - b‖ < delta := by
      intro z hz
      apply eventually_exists_finiteEPolynomial_root_in_norm_ball
        hA tau₀ hdelta
      change z ∈ R at hz
      exact (Multiset.mem_filter.mp hz).1
    filter_upwards [(eventually_all_finset S).2 hpersist] with tau ht
    have hroot (z : S) :
        ∃ b ∈ (finiteEPolynomial A tau).roots,
          ‖(z : ℂ) - b‖ < delta :=
      ht z z.property
    let b (z : S) : ℂ := Classical.choose (hroot z)
    have hbmem (z : S) : b z ∈ (finiteEPolynomial A tau).roots :=
      (Classical.choose_spec (hroot z)).1
    have hbclose (z : S) : ‖(z : ℂ) - b z‖ < delta :=
      (Classical.choose_spec (hroot z)).2
    have hbupper (z : S) : 0 < (b z).im := by
      have hmarginLe : margin ≤ (z : ℂ).im :=
        Finset.inf'_le _ z.property
      have hclose : ‖(z : ℂ) - b z‖ < (z : ℂ).im :=
        (hbclose z).trans_le (hdeltaMargin.trans hmarginLe)
      have himle : |(z : ℂ).im - (b z).im| ≤
          ‖(z : ℂ) - b z‖ := by
        simpa using Complex.abs_im_le_norm ((z : ℂ) - b z)
      have him : |(z : ℂ).im - (b z).im| < (z : ℂ).im :=
        himle.trans_lt hclose
      linarith [abs_lt.mp him]
    let T : Finset ℂ :=
      ((finiteEPolynomial A tau).roots.filter fun z => 0 < z.im).toFinset
    let F : S → T := fun z =>
      ⟨b z, by
        apply Multiset.mem_toFinset.mpr
        exact Multiset.mem_filter.mpr ⟨hbmem z, hbupper z⟩⟩
    have hF : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      by_contra hxyne
      by_cases hnontrivial : (S : Set ℂ).Nontrivial
      · have hbxy : b x = b y := congrArg Subtype.val hxy
        have hdeltaSeparation : delta ≤ separation / 3 := by
          simp [delta, hnontrivial]
        have hseparationPos : 0 < separation := by
          exact S.finite_toSet.infsep_pos_iff_nontrivial.mpr hnontrivial
        have hdistlt : dist (x : ℂ) (y : ℂ) < separation := by
          calc
            dist (x : ℂ) (y : ℂ) ≤
                dist (x : ℂ) (b x) + dist (b x) (y : ℂ) :=
              dist_triangle _ _ _
            _ = ‖(x : ℂ) - b x‖ + ‖(y : ℂ) - b y‖ := by
              simp [dist_eq_norm, hbxy, norm_sub_rev]
            _ < delta + delta := add_lt_add (hbclose x) (hbclose y)
            _ < separation := by nlinarith
        exact (not_lt_of_ge
          (Set.infsep_le_dist_of_mem x.property y.property hxyne)) hdistlt
      · apply hnontrivial
        exact ⟨x, x.property, y, y.property, hxyne⟩
    have hcard : S.card ≤ T.card := by
      simpa using Fintype.card_le_of_injective F hF
    calc
      upperHalfPlaneRootCount (finiteEPolynomial A tau₀) = S.card :=
        hcardS.symm
      _ ≤ T.card := hcard
      _ ≤ ((finiteEPolynomial A tau).roots.filter
          fun z => 0 < z.im).card := by
        simpa [T] using Multiset.toFinset_card_le
          ((finiteEPolynomial A tau).roots.filter fun z => 0 < z.im)
      _ = upperHalfPlaneRootCount (finiteEPolynomial A tau) := rfl
  · apply Filter.Eventually.of_forall
    intro tau
    rw [← hcardS]
    simp [Finset.not_nonempty_iff_eq_empty.mp hS]

@[simp] theorem finiteEPolynomial_neg_parameter
    (A : ℝ[X]) (tau : ℝ) :
    finiteEPolynomial A (-tau) = finiteESharpPolynomial A tau := by
  simp [finiteEPolynomial, finiteESharpPolynomial, sub_eq_add_neg]

/-- Reflection shows that separability at `tau` implies separability at the
opposite parameter. -/
theorem finiteEPolynomial_separable_neg_parameter
    {A : ℝ[X]} {tau : ℝ}
    (hseparable : (finiteEPolynomial A tau).Separable) :
    (finiteEPolynomial A (-tau)).Separable := by
  rw [finiteEPolynomial_neg_parameter,
    ← finiteEPolynomial_map_conj]
  exact hseparable.map

@[simp] theorem finiteEPolynomial_neg_parameter_upperCount
    (A : ℝ[X]) (tau : ℝ) :
    upperHalfPlaneRootCount (finiteEPolynomial A (-tau)) =
      lowerHalfPlaneRootCount (finiteEPolynomial A tau) := by
  rw [finiteEPolynomial_neg_parameter]
  exact upperHalfPlaneRootCount_finiteESharp A tau

/-- The lower-root-count analogue of local lower semicontinuity, obtained by
reflecting the parameter. -/
theorem eventually_finiteEPolynomial_lowerRootCount_le_of_separable
    {A : ℝ[X]} (hA : A ≠ 0) (tau₀ : ℝ)
    (hseparable : (finiteEPolynomial A tau₀).Separable) :
    ∀ᶠ tau in nhds tau₀,
      lowerHalfPlaneRootCount (finiteEPolynomial A tau₀) ≤
        lowerHalfPlaneRootCount (finiteEPolynomial A tau) := by
  have hneg := eventually_finiteEPolynomial_upperRootCount_le_of_separable
    hA (-tau₀) (finiteEPolynomial_separable_neg_parameter hseparable)
  have htend : Tendsto (fun tau : ℝ => -tau) (nhds tau₀) (nhds (-tau₀)) :=
    continuousAt_id.neg
  filter_upwards [htend.eventually hneg] with tau hle
  have hle' :
      upperHalfPlaneRootCount (finiteEPolynomial A (-tau₀)) ≤
        upperHalfPlaneRootCount (finiteEPolynomial A (-tau)) := hle
  rw [finiteEPolynomial_neg_parameter_upperCount,
    finiteEPolynomial_neg_parameter_upperCount] at hle'
  exact hle'

/-- Away from the real-axis crossing parameter, the upper root count is
locally constant at every separable member of the homotopy. -/
theorem eventually_finiteEPolynomial_upperRootCount_eq_of_separable
    {A : ℝ[X]} (hA : A.Separable) {tau₀ : ℝ} (htau₀ : tau₀ ≠ 0)
    (hseparable : (finiteEPolynomial A tau₀).Separable) :
    ∀ᶠ tau in nhds tau₀,
      upperHalfPlaneRootCount (finiteEPolynomial A tau) =
        upperHalfPlaneRootCount (finiteEPolynomial A tau₀) := by
  filter_upwards [
    eventually_finiteEPolynomial_upperRootCount_le_of_separable
      hA.ne_zero tau₀ hseparable,
    eventually_finiteEPolynomial_lowerRootCount_le_of_separable
      hA.ne_zero tau₀ hseparable,
    eventually_ne_nhds htau₀] with tau hupper hlower htau
  have hsum₀ := finiteEPolynomial_upper_add_lower hA htau₀
  have hsum := finiteEPolynomial_upper_add_lower hA htau
  omega

/-- If the homotopy has no multiple roots at positive parameters, its upper
root count is constant throughout the positive parameter interval.  This is
the global collision-free case of the finite root-count problem. -/
theorem finiteEPolynomial_upperRootCount_eq_of_forall_separable
    {A : ℝ[X]} (hA : A.Separable)
    (hall : ∀ tau : ℝ, 0 < tau → (finiteEPolynomial A tau).Separable)
    {tau sigma : ℝ} (htau : 0 < tau) (hsigma : 0 < sigma) :
    upperHalfPlaneRootCount (finiteEPolynomial A tau) =
      upperHalfPlaneRootCount (finiteEPolynomial A sigma) := by
  let f : Set.Ioi (0 : ℝ) → ℕ := fun t ↦
    upperHalfPlaneRootCount (finiteEPolynomial A t)
  have hf : IsLocallyConstant f :=
    (IsLocallyConstant.iff_eventually_eq f).2 fun t ↦ by
      have hlocal :=
        eventually_finiteEPolynomial_upperRootCount_eq_of_separable hA
          (ne_of_gt t.property) (hall t t.property)
      exact continuousAt_subtype_val.eventually hlocal
  let hpre : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  exact @IsLocallyConstant.apply_eq_of_preconnectedSpace
    (Set.Ioi (0 : ℝ)) ℕ _ hpre f hf ⟨tau, htau⟩ ⟨sigma, hsigma⟩

end

end RiemannGaussian
