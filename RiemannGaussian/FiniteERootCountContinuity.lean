import RiemannGaussian.FiniteERootMoments
import Mathlib.LinearAlgebra.Lagrange

/-!
# Root-count continuity through collisions

This file proves the missing multiplicity-sensitive local constancy theorem
for the finite homotopy.  At a fixed nonzero parameter, Lagrange interpolation
constructs a polynomial which is exactly the upper-half-plane indicator on
the finite base root set.  Reverse root persistence keeps every nearby root
close to that set, while continuity of the polynomial root sum controls the
total with multiplicity.  Since the two root counts are natural numbers, the
resulting strict distance bound forces equality even when the base polynomial
has multiple roots.
-/

open Polynomial Filter Topology

namespace RiemannGaussian

noncomputable section

/-- The complex-valued indicator of the open upper half-plane. -/
def upperHalfPlaneIndicator (z : ℂ) : ℂ :=
  if 0 < z.im then 1 else 0

/-- Summing the upper-half-plane indicator over the roots gives the root
count, including multiplicity. -/
theorem sum_upperHalfPlaneIndicator (p : ℂ[X]) :
    (p.roots.map upperHalfPlaneIndicator).sum =
      (upperHalfPlaneRootCount p : ℂ) := by
  change (p.roots.map upperHalfPlaneIndicator).sum =
    ((p.roots.filter fun z ↦ 0 < z.im).card : ℂ)
  induction p.roots using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      by_cases hz : 0 < z.im
      · simp [upperHalfPlaneIndicator, hz, ih, add_comm]
      · simp [upperHalfPlaneIndicator, hz, ih]

/-- Every root of a nonzero-parameter member has nonzero imaginary part. -/
theorem finiteEPolynomial_root_im_ne_zero
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z : ℂ} (hz : z ∈ (finiteEPolynomial A tau).roots) :
    z.im ≠ 0 := by
  intro him
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hzeval : (finiteEPolynomial A tau).eval z = 0 :=
    (mem_roots (finiteEPolynomial_ne_zero hA.ne_zero tau)).mp hz
  apply finiteEPolynomial_no_real_zero hA htau z.re
  rw [← hzreal]
  exact hzeval

/-- The upper-half-plane root count is locally constant at every nonzero
parameter, with no separability assumption on the homotopy member.  In
particular, the proof remains valid at multiple-root collisions. -/
theorem eventually_finiteEPolynomial_upperRootCount_eq
    {A : ℝ[X]} (hA : A.Separable) {tau₀ : ℝ} (htau₀ : tau₀ ≠ 0) :
    ∀ᶠ tau in nhds tau₀,
      upperHalfPlaneRootCount (finiteEPolynomial A tau) =
        upperHalfPlaneRootCount (finiteEPolynomial A tau₀) := by
  classical
  by_cases hdegree : A.natDegree = 0
  · apply Filter.Eventually.of_forall
    intro tau
    simp only [upperHalfPlaneRootCount]
    have htauRoots : (finiteEPolynomial A tau).roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [IsAlgClosed.card_roots_eq_natDegree,
        finiteEPolynomial_natDegree hA.ne_zero, hdegree]
    have hbaseRoots : (finiteEPolynomial A tau₀).roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [IsAlgClosed.card_roots_eq_natDegree,
        finiteEPolynomial_natDegree hA.ne_zero, hdegree]
    simp [htauRoots, hbaseRoots]
  · let S : Finset ℂ := (finiteEPolynomial A tau₀).roots.toFinset
    have hrootsCard : (finiteEPolynomial A tau₀).roots.card =
        A.natDegree := by
      rw [IsAlgClosed.card_roots_eq_natDegree,
        finiteEPolynomial_natDegree hA.ne_zero]
    have hS : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hSempty
      have hrootsEmpty : (finiteEPolynomial A tau₀).roots = 0 := by
        exact Multiset.toFinset_eq_empty.mp hSempty
      rw [hrootsEmpty] at hrootsCard
      simp at hrootsCard
      exact hdegree hrootsCard.symm
    let q : ℂ[X] := Lagrange.interpolate S id upperHalfPlaneIndicator
    have hid : Set.InjOn (id : ℂ → ℂ) S := by
      intro x _ y _ hxy
      exact hxy
    have hqeval : ∀ a ∈ (finiteEPolynomial A tau₀).roots,
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
        _ ≤ (finiteEPolynomial A tau₀).roots.card :=
          Multiset.toFinset_card_le (finiteEPolynomial A tau₀).roots
        _ = A.natDegree := hrootsCard
    let eta : ℝ := 1 / (4 * A.natDegree)
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    choose radius hradius hclose using fun a : ℂ ↦
      Metric.continuousAt_iff.mp
        (q.continuous.continuousAt :
          ContinuousAt (fun z : ℂ ↦ q.eval z) a)
        eta heta
    let localRadius : ℂ → ℝ := fun a ↦ min (radius a) |a.im|
    have hlocalRadius : ∀ a ∈ S, 0 < localRadius a := by
      intro a ha
      apply lt_min (hradius a)
      apply abs_pos.mpr
      apply finiteEPolynomial_root_im_ne_zero hA htau₀
      exact Multiset.mem_toFinset.mp ha
    let delta : ℝ := S.inf' hS localRadius
    have hdelta : 0 < delta :=
      (Finset.lt_inf'_iff hS).2 hlocalRadius
    have hnear :=
      eventually_forall_finiteEPolynomial_root_exists_base_root_in_norm_ball
        hA.ne_zero tau₀ hdelta
    have hmoment : ∀ᶠ tau in nhds tau₀,
        ‖finiteERootEvalSum A tau q - finiteERootEvalSum A tau₀ q‖ <
          (1 / 4 : ℝ) :=
      (continuous_finiteERootEvalSum hA.ne_zero q hqdegree).continuousAt
        (eventually_norm_sub_lt _ (by norm_num))
    filter_upwards [hnear, hmoment] with tau hnearTau hmomentTau
    have hpoint : ∀ b ∈ (finiteEPolynomial A tau).roots,
        ‖q.eval b - upperHalfPlaneIndicator b‖ < eta := by
      intro b hb
      obtain ⟨a, ha, hba⟩ := hnearTau b hb
      have haS : a ∈ S := Multiset.mem_toFinset.mpr ha
      have hdeltaLocal : delta ≤ localRadius a :=
        Finset.inf'_le localRadius haS
      have hdeltaRadius : delta ≤ radius a :=
        hdeltaLocal.trans (min_le_left _ _)
      have hdeltaIm : delta ≤ |a.im| :=
        hdeltaLocal.trans (min_le_right _ _)
      have hqclose : ‖q.eval b - q.eval a‖ < eta := by
        simpa [dist_eq_norm] using hclose a (x := b)
          (by simpa [dist_eq_norm] using hba.trans_le hdeltaRadius)
      have himle : |b.im - a.im| ≤ ‖b - a‖ := by
        simpa using Complex.abs_im_le_norm (b - a)
      have himclose : |b.im - a.im| < |a.im| :=
        himle.trans_lt (hba.trans_le hdeltaIm)
      have hindicator :
          upperHalfPlaneIndicator b = upperHalfPlaneIndicator a := by
        have haim : a.im ≠ 0 := finiteEPolynomial_root_im_ne_zero hA htau₀ ha
        by_cases haupper : 0 < a.im
        · have hbupper : 0 < b.im := by
            have habs : |b.im - a.im| < a.im := by
              simpa [abs_of_pos haupper] using himclose
            linarith [abs_lt.mp habs]
          simp [upperHalfPlaneIndicator, haupper, hbupper]
        · have halower : a.im < 0 := lt_of_le_of_ne
              (le_of_not_gt haupper) haim
          have hblower : b.im < 0 := by
            have habs : |b.im - a.im| < -a.im := by
              simpa [abs_of_neg halower] using himclose
            linarith [abs_lt.mp habs]
          simp [upperHalfPlaneIndicator, haupper, not_lt_of_ge hblower.le]
      rw [hindicator, ← hqeval a ha]
      exact hqclose
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
    have hbase : finiteERootEvalSum A tau₀ q =
        (upperHalfPlaneRootCount (finiteEPolynomial A tau₀) : ℂ) := by
      rw [finiteERootEvalSum, ← sum_upperHalfPlaneIndicator]
      apply congrArg Multiset.sum
      exact Multiset.map_congr rfl hqeval
    rw [hbase] at hmomentTau
    let m := upperHalfPlaneRootCount (finiteEPolynomial A tau)
    let n := upperHalfPlaneRootCount (finiteEPolynomial A tau₀)
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

/-- The upper-half-plane root count is constant over the entire positive
parameter interval, including through every multiple-root collision. -/
theorem finiteEPolynomial_upperRootCount_eq_of_pos
    {A : ℝ[X]} (hA : A.Separable)
    {tau sigma : ℝ} (htau : 0 < tau) (hsigma : 0 < sigma) :
    upperHalfPlaneRootCount (finiteEPolynomial A tau) =
      upperHalfPlaneRootCount (finiteEPolynomial A sigma) := by
  let f : Set.Ioi (0 : ℝ) → ℕ := fun t ↦
    upperHalfPlaneRootCount (finiteEPolynomial A t)
  have hf : IsLocallyConstant f :=
    (IsLocallyConstant.iff_eventually_eq f).2 fun t ↦ by
      have hlocal := eventually_finiteEPolynomial_upperRootCount_eq
        hA (ne_of_gt t.property)
      exact continuousAt_subtype_val.eventually hlocal
  let hpre : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  exact @IsLocallyConstant.apply_eq_of_preconnectedSpace
    (Set.Ioi (0 : ℝ)) ℕ _ hpre f hf ⟨tau, htau⟩ ⟨sigma, hsigma⟩

end

end RiemannGaussian
