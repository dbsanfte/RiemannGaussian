import RiemannGaussian.RiemannXiSuzukiBoundedSynthesis

/-!
# A Schur route to Suzuki's bounded-synthesis estimate

The bounded-synthesis frontier can be attacked through the genuine boundary
Gram kernel.  This file proves a finite symmetric Schur estimate over the
reals and applies it to the absolute values of Suzuki's Gram entries.

Consequently, a uniform absolute row-sum bound by `C²` implies the Bessel
bound with constant `C`, hence the boundary `L²` convergence proved in the
preceding file.  A complete summable-row formulation is also provided.  These
row hypotheses are explicit propositions; this file proves the reduction but
does not assert that the spectral xi Gram kernel satisfies them.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Finite symmetric Schur estimate.  A nonnegative symmetric kernel whose
rows over a finite set have mass at most `B` has quadratic form at most
`B * ‖a‖₂²`. -/
theorem finset_symmetric_schur_quadratic_le
    {ι : Type*} (S : Finset ι) (a : ι → ℝ) (K : ι → ι → ℝ) (B : ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (hsym : ∀ i j, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ B) :
    ∑ i ∈ S, ∑ j ∈ S, a i * a j * K i j ≤
      B * ∑ i ∈ S, a i ^ 2 := by
  let Q := ∑ i ∈ S, ∑ j ∈ S, a i * a j * K i j
  let A := ∑ i ∈ S, ∑ j ∈ S, a i ^ 2 * K i j
  let D := ∑ i ∈ S, ∑ j ∈ S, a j ^ 2 * K i j
  have hpair : ∀ i j,
      2 * (a i * a j * K i j) ≤
        a i ^ 2 * K i j + a j ^ 2 * K i j := by
    intro i j
    have h := mul_le_mul_of_nonneg_right
      (two_mul_le_add_sq (a i) (a j)) (hK i j)
    nlinarith
  have hdouble : 2 * Q ≤ A + D := by
    dsimp [Q, A, D]
    calc
      2 * (∑ i ∈ S, ∑ j ∈ S, a i * a j * K i j) =
          ∑ i ∈ S, ∑ j ∈ S, 2 * (a i * a j * K i j) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S, ∑ j ∈ S,
          (a i ^ 2 * K i j + a j ^ 2 * K i j) := by
        apply Finset.sum_le_sum
        intro i _hi
        apply Finset.sum_le_sum
        intro j _hj
        exact hpair i j
      _ = (∑ i ∈ S, ∑ j ∈ S, a i ^ 2 * K i j) +
          ∑ i ∈ S, ∑ j ∈ S, a j ^ 2 * K i j := by
        simp_rw [Finset.sum_add_distrib]
  have hA : A ≤ B * ∑ i ∈ S, a i ^ 2 := by
    dsimp [A]
    calc
      (∑ i ∈ S, ∑ j ∈ S, a i ^ 2 * K i j) =
          ∑ i ∈ S, a i ^ 2 * ∑ j ∈ S, K i j := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S, a i ^ 2 * B := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg (a i))
      _ = B * ∑ i ∈ S, a i ^ 2 := by
        rw [← Finset.sum_mul]
        ring
  have hDA : D = A := by
    dsimp [D, A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hsym]
  have htwo : 2 * Q ≤ 2 * (B * ∑ i ∈ S, a i ^ 2) := by
    calc
      2 * Q ≤ A + D := hdouble
      _ = 2 * A := by rw [hDA]; ring
      _ ≤ 2 * (B * ∑ i ∈ S, a i ^ 2) :=
        mul_le_mul_of_nonneg_left hA (by norm_num)
  linarith

/-- A uniform absolute finite-row bound for the genuine Suzuki zero-function
Gram kernel.  The bound is parameterized as `C²` to match the Bessel norm
constant `C`. -/
def SuzukiXiZeroFunctionAbsoluteGramRowBound (C : ℝ) : Prop :=
  0 < C ∧ ∀ (S : Finset NontrivialZetaZero) (rho : NontrivialZetaZero),
    rho ∈ S →
      ∑ sigma ∈ S, ‖suzukiXiZeroFunctionGramEntry rho sigma‖ ≤ C ^ 2

/-- Absolute values of the Suzuki Gram kernel are symmetric. -/
theorem norm_suzukiXiZeroFunctionGramEntry_swap
    (rho sigma : NontrivialZetaZero) :
    ‖suzukiXiZeroFunctionGramEntry rho sigma‖ =
      ‖suzukiXiZeroFunctionGramEntry sigma rho‖ := by
  rw [suzukiXiZeroFunctionGramEntry_swap]
  simp

/-- Every Gram entry obeys the Hilbert-space Cauchy--Schwarz bound. -/
theorem norm_suzukiXiZeroFunctionGramEntry_le
    (rho sigma : NontrivialZetaZero) :
    ‖suzukiXiZeroFunctionGramEntry rho sigma‖ ≤
      ‖suzukiRealAxisZeroFunctionLp rho‖ *
        ‖suzukiRealAxisZeroFunctionLp sigma‖ := by
  unfold suzukiXiZeroFunctionGramEntry
  exact norm_inner_le_norm _ _

/-- Each genuine Gram entry is the Lebesgue integral of the literal two
zero-function boundary formulas.  This exposes the analytic kernel that must
be estimated to prove a Schur row bound. -/
theorem suzukiXiZeroFunctionGramEntry_eq_integral
    (rho sigma : NontrivialZetaZero) :
    suzukiXiZeroFunctionGramEntry rho sigma =
      ∫ x : ℝ,
        starRingEnd ℂ (suzukiRealAxisZeroFunction rho x) *
          suzukiRealAxisZeroFunction sigma x := by
  unfold suzukiXiZeroFunctionGramEntry
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [suzukiRealAxisZeroFunctionLp_ae rho,
    suzukiRealAxisZeroFunctionLp_ae sigma] with x hrho hsigma
  rw [hrho, hsigma]
  rw [RCLike.inner_apply']

/-- Any Bessel witness necessarily gives a uniform norm bound on every
individual normalized xi-zero function. -/
theorem norm_suzukiRealAxisZeroFunctionLp_le_of_besselBound
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    (rho : NontrivialZetaZero) :
    ‖suzukiRealAxisZeroFunctionLp rho‖ ≤ C := by
  have hsingle := hC.2 (Finsupp.single rho (1 : ℂ))
  simp only [suzukiXiZeroFunctionFiniteSynthesis,
    suzukiXiFiniteCoefficientEmbedding,
    Finsupp.linearCombination_single, Finsupp.lsum_single,
    lp.lsingle_apply, one_smul] at hsingle
  have hone : ‖lp.single (E := fun _ : NontrivialZetaZero ↦ ℂ)
      (2 : ℝ≥0∞) rho (1 : ℂ)‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    norm_num
  rw [hone, mul_one] at hsingle
  exact hsingle

/-- The absolute value of a finitely supported Suzuki Gram quadratic is
bounded by the corresponding nonnegative scalar double sum. -/
theorem norm_suzukiXiZeroFunctionFinsuppGramQuadratic_le
    (c : NontrivialZetaZero →₀ ℂ) :
    ‖suzukiXiZeroFunctionFinsuppGramQuadratic c‖ ≤
      ∑ rho ∈ c.support,
        ∑ sigma ∈ c.support,
          ‖c rho‖ * ‖c sigma‖ *
            ‖suzukiXiZeroFunctionGramEntry rho sigma‖ := by
  unfold suzukiXiZeroFunctionFinsuppGramQuadratic
  calc
    ‖∑ rho ∈ c.support,
        ∑ sigma ∈ c.support,
          starRingEnd ℂ (c rho) * c sigma *
            suzukiXiZeroFunctionGramEntry rho sigma‖ ≤
        ∑ rho ∈ c.support,
          ‖∑ sigma ∈ c.support,
            starRingEnd ℂ (c rho) * c sigma *
              suzukiXiZeroFunctionGramEntry rho sigma‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ c.support,
        ∑ sigma ∈ c.support,
          ‖starRingEnd ℂ (c rho) * c sigma *
            suzukiXiZeroFunctionGramEntry rho sigma‖ := by
      apply Finset.sum_le_sum
      intro rho _hrho
      exact norm_sum_le _ _
    _ = ∑ rho ∈ c.support,
        ∑ sigma ∈ c.support,
          ‖c rho‖ * ‖c sigma‖ *
            ‖suzukiXiZeroFunctionGramEntry rho sigma‖ := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      simp only [norm_mul]
      have hstar : ‖starRingEnd ℂ (c rho)‖ = ‖c rho‖ := by
        change ‖star (c rho)‖ = ‖c rho‖
        exact norm_star _
      rw [hstar]

/-- A uniform absolute Gram row bound proves the exact Bessel estimate for
Suzuki's normalized zero functions. -/
theorem suzukiXiZeroFunctionBesselBound_of_absoluteGramRowBound
    {C : ℝ} (hrow : SuzukiXiZeroFunctionAbsoluteGramRowBound C) :
    SuzukiXiZeroFunctionBesselBound C := by
  rw [suzukiXiZeroFunctionBesselBound_iff_gram]
  refine ⟨hrow.1, ?_⟩
  intro c
  calc
    (suzukiXiZeroFunctionFinsuppGramQuadratic c).re ≤
        ‖suzukiXiZeroFunctionFinsuppGramQuadratic c‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ rho ∈ c.support,
        ∑ sigma ∈ c.support,
          ‖c rho‖ * ‖c sigma‖ *
            ‖suzukiXiZeroFunctionGramEntry rho sigma‖ :=
      norm_suzukiXiZeroFunctionFinsuppGramQuadratic_le c
    _ ≤ C ^ 2 * ∑ rho ∈ c.support, ‖c rho‖ ^ 2 := by
      apply finset_symmetric_schur_quadratic_le
      · intro rho sigma
        exact norm_nonneg _
      · exact norm_suzukiXiZeroFunctionGramEntry_swap
      · intro rho hrho
        exact hrow.2 c.support rho hrho

/-- A complete absolute-row summability statement for the genuine Suzuki
Gram kernel.  As above, this declaration only names the proposition. -/
def SuzukiXiZeroFunctionAbsoluteGramTsumBound (C : ℝ) : Prop :=
  0 < C ∧ ∀ rho : NontrivialZetaZero,
    Summable (fun sigma : NontrivialZetaZero ↦
      ‖suzukiXiZeroFunctionGramEntry rho sigma‖) ∧
    ∑' sigma : NontrivialZetaZero,
      ‖suzukiXiZeroFunctionGramEntry rho sigma‖ ≤ C ^ 2

/-- A complete summable-row bound supplies every finite row bound. -/
theorem absoluteGramRowBound_of_tsumBound
    {C : ℝ} (htsum : SuzukiXiZeroFunctionAbsoluteGramTsumBound C) :
    SuzukiXiZeroFunctionAbsoluteGramRowBound C := by
  refine ⟨htsum.1, ?_⟩
  intro S rho _hrho
  exact ((htsum.2 rho).1.sum_le_tsum S
    (fun sigma _hsigma ↦ norm_nonneg _)).trans (htsum.2 rho).2

/-- Thus complete absolute row summability is one explicit sufficient route
to the bounded-synthesis witness. -/
theorem suzukiXiZeroFunctionBesselBound_of_absoluteGramTsumBound
    {C : ℝ} (htsum : SuzukiXiZeroFunctionAbsoluteGramTsumBound C) :
    SuzukiXiZeroFunctionBesselBound C :=
  suzukiXiZeroFunctionBesselBound_of_absoluteGramRowBound
    (absoluteGramRowBound_of_tsumBound htsum)

end

end RiemannGaussian
