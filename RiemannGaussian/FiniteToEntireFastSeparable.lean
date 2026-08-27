import RiemannGaussian.FiniteToEntireExpandingTaylor

/-!
# Fast separable perturbations on expanding disks

The original constrained separability construction used coefficients of
order `1 / n`.  That is sufficient on fixed compact sets but not on disks of
radius comparable to `sqrt n`, because its cubic degree-lifting term need not
vanish there.

This file makes the perturbation budget arbitrary.  Finite bad-parameter sets
can be avoided inside every positive budget, so both the cubic lift and the
quadratic separability perturbation can be normalized by exact coefficientwise
majorants on any prescribed growing disk.  Lean then obtains a separable,
root-pinned sequence whose total change is at most `exp (-n) / 2` on that
disk.  Consequently separability and degree lifting preserve any expanding-
disk convergence already possessed by the pinned input sequence.
-/

open Filter Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- Constrained separability can be achieved under any prescribed positive
budget tending to zero.  The conclusion retains the exact homotopy root and
degree bound, and records a pointwise norm bound for the two perturbations. -/
theorem exists_separable_finiteERoot_polynomial_sequence_with_budget
    (A : ℕ → ℝ[X]) {f : ℂ → ℂ} {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f atTop Set.univ)
    (hroot : ∀ n, (finiteEPolynomial (A n) eta).eval z = 0)
    (budget : ℕ → ℝ) (hbudgetPos : ∀ n, 0 < budget n)
    (hbudget : Tendsto budget atTop (nhds 0)) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        f atTop Set.univ ∧
      ∀ n, (B n).Separable ∧
        (finiteEPolynomial (B n) eta).eval z = 0 ∧
        (B n).natDegree ≤ max (A n).natDegree 3 ∧
        ∀ w : ℂ,
          ‖((B n).map Complex.ofRealHom).eval w -
              ((A n).map Complex.ofRealHom).eval w‖ ≤
            (budget n / 2) *
              (‖((finiteERootKernelCubic eta z).map
                    Complex.ofRealHom).eval w‖ +
                ‖((finiteERootKernelQuadratic eta z).map
                    Complex.ofRealHom).eval w‖) := by
  have hzeta : z.im + eta ≠ 0 := by linarith
  let r : ℕ → ℝ := fun n ↦ budget n / 2
  let D : ℕ → ℝ[X] := fun n ↦
    finiteERootDegreeLift (A n) eta z (r n)
  have hr : Tendsto r atTop (nhds 0) := by
    simpa [r] using hbudget.div_const 2
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp only [r]
    exact div_pos (hbudgetPos n) (by norm_num)
  have hDlimit : TendstoLocallyUniformlyOn
      (fun n w ↦ ((D n).map Complex.ofRealHom).eval w)
      f atTop Set.univ := by
    exact finiteERootDegreeLift_tendstoLocallyUniformlyOn
      A eta z r hA hr
  have hDdegree (n : ℕ) : 2 < (D n).natDegree := by
    exact finiteERootDegreeLift_natDegree_gt_two eta z
      (ne_of_gt (hrpos n))
  have hDdegreeUpper (n : ℕ) :
      (D n).natDegree ≤ max (A n).natDegree 3 := by
    exact finiteERootDegreeLift_natDegree_le (A n) eta z (r n)
  have hDroot (n : ℕ) :
      (finiteEPolynomial (D n) eta).eval z = 0 := by
    exact finiteERootDegreeLift_isRoot (hroot n) hzeta (r n)
  have hexists (n : ℕ) :
      ∃ t : ℝ, 0 < t ∧ t < r n ∧
        (D n + C t * finiteERootKernelQuadratic eta z).Separable ∧
        (finiteEPolynomial
          (D n + C t * finiteERootKernelQuadratic eta z) eta).eval z = 0 :=
    exists_separable_finiteERootKernelQuadratic_perturbation
      heta hz (hDdegree n) (hDroot n) (hrpos n)
  choose t htpos htbound htsep htroot using hexists
  let B : ℕ → ℝ[X] := fun n ↦
    D n + C (t n) * finiteERootKernelQuadratic eta z
  have ht : Tendsto t atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun n ↦ (htpos n).le
    · exact fun n ↦ (htbound n).le
    · exact hr
  refine ⟨B, ?_, ?_⟩
  · exact add_C_mul_fixedPolynomial_tendstoLocallyUniformlyOn
      D (finiteERootKernelQuadratic eta z) t hDlimit ht
  · intro n
    refine ⟨htsep n, htroot n, ?_, ?_⟩
    · calc
        (B n).natDegree ≤ max (D n).natDegree 2 :=
          add_C_mul_finiteERootKernelQuadratic_natDegree_le
            (D n) eta z (t n)
        _ = (D n).natDegree := max_eq_left (hDdegree n).le
        _ ≤ max (A n).natDegree 3 := hDdegreeUpper n
    · intro w
      let s : ℝ := if (A n).natDegree ≤ 2 then r n else 0
      let cubic : ℂ :=
        ((finiteERootKernelCubic eta z).map Complex.ofRealHom).eval w
      let quadratic : ℂ :=
        ((finiteERootKernelQuadratic eta z).map Complex.ofRealHom).eval w
      have hform :
          ((B n).map Complex.ofRealHom).eval w -
              ((A n).map Complex.ofRealHom).eval w =
            (s : ℂ) * cubic +
              quadratic * Complex.ofRealHom (t n) := by
        simp only [B, Polynomial.map_add, Polynomial.eval_add,
          Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
          Polynomial.eval_C]
        rw [finiteERootDegreeLift_map_eval]
        simp only [s, cubic, quadratic]
        ring
      have hsabs : |s| ≤ r n := by
        dsimp only [s]
        split_ifs
        · rw [abs_of_pos (hrpos n)]
        · simpa using (hrpos n).le
      have htAbs : |t n| ≤ r n := by
        rw [abs_of_pos (htpos n)]
        exact (htbound n).le
      rw [hform]
      calc
        ‖(s : ℂ) * cubic + quadratic * Complex.ofRealHom (t n)‖ ≤
            ‖(s : ℂ) * cubic‖ +
              ‖quadratic * Complex.ofRealHom (t n)‖ :=
          norm_add_le _ _
        _ = |s| * ‖cubic‖ + |t n| * ‖quadratic‖ := by
          simp [mul_comm]
        _ ≤ r n * ‖cubic‖ + r n * ‖quadratic‖ := by
          gcongr
        _ = (budget n / 2) * (‖cubic‖ + ‖quadratic‖) := by
          simp only [r]
          ring

/-- A coefficientwise radial majorant for evaluation of a real polynomial
after mapping it to the complex numbers. -/
def realPolynomialEvaluationMajorant (Q : ℝ[X]) (R : ℝ) : ℝ :=
  Q.sum fun i a ↦ |a| * R ^ i

/-- The coefficientwise evaluation majorant is nonnegative at every
nonnegative radius. -/
theorem realPolynomialEvaluationMajorant_nonneg
    (Q : ℝ[X]) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ realPolynomialEvaluationMajorant Q R := by
  rw [realPolynomialEvaluationMajorant, Polynomial.sum_def]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hR i)

/-- Complex evaluation inside a closed radial disk is bounded by the
coefficientwise polynomial majorant at that radius. -/
theorem norm_realPolynomial_map_eval_le_majorant
    (Q : ℝ[X]) {w : ℂ} {R : ℝ} (hw : ‖w‖ ≤ R) :
    ‖(Q.map Complex.ofRealHom).eval w‖ ≤
      realPolynomialEvaluationMajorant Q R := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def, realPolynomialEvaluationMajorant,
    Polynomial.sum_def]
  calc
    ‖∑ i ∈ Q.support, Complex.ofRealHom (Q.coeff i) * w ^ i‖ ≤
        ∑ i ∈ Q.support,
          ‖Complex.ofRealHom (Q.coeff i) * w ^ i‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ Q.support, |Q.coeff i| * ‖w‖ ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ ≤ ∑ i ∈ Q.support, |Q.coeff i| * R ^ i := by
      gcongr

/-- A positive exponential budget normalized by coefficientwise majorants of
two fixed polynomials on a varying radial scale. -/
def twoPolynomialExpBudget
    (Q P : ℝ[X]) (R : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ)) /
    (1 + realPolynomialEvaluationMajorant Q (R n) +
      realPolynomialEvaluationMajorant P (R n))

/-- The normalized two-polynomial budget is positive, tends to zero, and is
bounded above by `exp (-n)`. -/
theorem twoPolynomialExpBudget_spec
    (Q P : ℝ[X]) (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    (∀ n, 0 < twoPolynomialExpBudget Q P R n) ∧
      Tendsto (twoPolynomialExpBudget Q P R) atTop (nhds 0) ∧
      ∀ n, twoPolynomialExpBudget Q P R n ≤
        Real.exp (-(n : ℝ)) := by
  have hden (n : ℕ) : 1 ≤
      1 + realPolynomialEvaluationMajorant Q (R n) +
        realPolynomialEvaluationMajorant P (R n) := by
    have hQ := realPolynomialEvaluationMajorant_nonneg Q (hR n)
    have hP := realPolynomialEvaluationMajorant_nonneg P (hR n)
    linarith
  have hpos (n : ℕ) : 0 < twoPolynomialExpBudget Q P R n := by
    unfold twoPolynomialExpBudget
    exact div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hden n))
  have hle (n : ℕ) : twoPolynomialExpBudget Q P R n ≤
      Real.exp (-(n : ℝ)) := by
    unfold twoPolynomialExpBudget
    exact div_le_self (Real.exp_pos _).le (hden n)
  refine ⟨hpos, ?_, hle⟩
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ (hpos n).le
  · exact Eventually.of_forall hle
  · exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- On any prescribed nonnegative radial scale, constrained separability can
be arranged so that the total modification is at most `exp (-n) / 2`
throughout the corresponding stage-dependent disk. -/
theorem exists_separable_finiteERoot_polynomial_sequence_with_expanding_control
    (A : ℕ → ℝ[X]) {f : ℂ → ℂ} {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f atTop Set.univ)
    (hroot : ∀ n, (finiteEPolynomial (A n) eta).eval z = 0)
    (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        f atTop Set.univ ∧
      ∀ n, (B n).Separable ∧
        (finiteEPolynomial (B n) eta).eval z = 0 ∧
        (B n).natDegree ≤ max (A n).natDegree 3 ∧
        ∀ w : ℂ, ‖w‖ ≤ R n →
          ‖((B n).map Complex.ofRealHom).eval w -
              ((A n).map Complex.ofRealHom).eval w‖ ≤
            Real.exp (-(n : ℝ)) / 2 := by
  let Q := finiteERootKernelCubic eta z
  let P := finiteERootKernelQuadratic eta z
  let budget : ℕ → ℝ := twoPolynomialExpBudget Q P R
  have hbudgetSpec := twoPolynomialExpBudget_spec Q P R hR
  obtain ⟨B, hBlimit, hB⟩ :=
    exists_separable_finiteERoot_polynomial_sequence_with_budget
      A heta hz hA hroot budget hbudgetSpec.1 hbudgetSpec.2.1
  refine ⟨B, hBlimit, ?_⟩
  intro n
  obtain ⟨hBsep, hBroot, hBdegree, hBbound⟩ := hB n
  refine ⟨hBsep, hBroot, hBdegree, ?_⟩
  intro w hw
  let M : ℝ := realPolynomialEvaluationMajorant Q (R n) +
    realPolynomialEvaluationMajorant P (R n)
  have hQ0 : 0 ≤ realPolynomialEvaluationMajorant Q (R n) :=
    realPolynomialEvaluationMajorant_nonneg Q (hR n)
  have hP0 : 0 ≤ realPolynomialEvaluationMajorant P (R n) :=
    realPolynomialEvaluationMajorant_nonneg P (hR n)
  have hM0 : 0 ≤ M := add_nonneg hQ0 hP0
  have hnorm :
      ‖(Q.map Complex.ofRealHom).eval w‖ +
          ‖(P.map Complex.ofRealHom).eval w‖ ≤ M := by
    dsimp only [M]
    exact add_le_add
      (norm_realPolynomial_map_eval_le_majorant Q hw)
      (norm_realPolynomial_map_eval_le_majorant P hw)
  calc
    ‖((B n).map Complex.ofRealHom).eval w -
        ((A n).map Complex.ofRealHom).eval w‖ ≤
      (budget n / 2) *
        (‖(Q.map Complex.ofRealHom).eval w‖ +
          ‖(P.map Complex.ofRealHom).eval w‖) := by
            simpa only [Q, P] using hBbound w
    _ ≤ (budget n / 2) * M := by
      exact mul_le_mul_of_nonneg_left hnorm
        (div_nonneg (hbudgetSpec.1 n).le (by norm_num))
    _ ≤ Real.exp (-(n : ℝ)) / 2 := by
      have hden : 0 < 1 + M := by linarith
      have hbudgetEq : budget n =
          Real.exp (-(n : ℝ)) / (1 + M) := by
        dsimp [budget, twoPolynomialExpBudget, M]
        congr 1
        ring
      rw [hbudgetEq]
      change
        (Real.exp (-(n : ℝ)) / (1 + M) / 2) * M ≤
          Real.exp (-(n : ℝ)) / 2
      rw [show
        (Real.exp (-(n : ℝ)) / (1 + M) / 2) * M =
          (Real.exp (-(n : ℝ)) / 2 * M) / (1 + M) by
            field_simp]
      rw [div_le_iff₀ hden]
      nlinarith [Real.exp_pos (-(n : ℝ))]

/-- If a root-pinned input sequence already converges uniformly on a family
of expanding disks, the fast separability construction preserves that full
expanding-disk convergence, together with exact roots and degree control. -/
theorem exists_separable_finiteERoot_polynomial_sequence_preserving_expanding_convergence
    (A : ℕ → ℝ[X]) {f : ℂ → ℂ} {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f atTop Set.univ)
    (hroot : ∀ n, (finiteEPolynomial (A n) eta).eval z = 0)
    (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (hAexpanding : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ w : ℂ,
      ‖w‖ ≤ R n →
      ‖((A n).map Complex.ofRealHom).eval w - f w‖ < ε) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        f atTop Set.univ ∧
      (∀ n, (B n).Separable ∧
        (finiteEPolynomial (B n) eta).eval z = 0 ∧
        (B n).natDegree ≤ max (A n).natDegree 3) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ w : ℂ,
        ‖w‖ ≤ R n →
        ‖((B n).map Complex.ofRealHom).eval w - f w‖ < ε := by
  obtain ⟨B, hBlimit, hB⟩ :=
    exists_separable_finiteERoot_polynomial_sequence_with_expanding_control
      A heta hz hA hroot R hR
  refine ⟨B, hBlimit, ?_, ?_⟩
  · intro n
    exact ⟨(hB n).1, (hB n).2.1, (hB n).2.2.1⟩
  · have hperturb : Tendsto
        (fun n : ℕ ↦ Real.exp (-(n : ℝ)) / 2)
        atTop (nhds 0) := by
      simpa using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))).div_const 2
    intro ε hε
    have hAevent := hAexpanding (ε / 2) (by linarith)
    have hpevent : ∀ᶠ n : ℕ in atTop,
        Real.exp (-(n : ℝ)) / 2 < ε / 2 :=
      (tendsto_order.1 hperturb).2 (ε / 2) (by linarith)
    filter_upwards [hAevent, hpevent] with n hAn hpn
    intro w hw
    have hBA := (hB n).2.2.2 w hw
    have hAf := hAn w hw
    calc
      ‖((B n).map Complex.ofRealHom).eval w - f w‖ =
          ‖(((B n).map Complex.ofRealHom).eval w -
              ((A n).map Complex.ofRealHom).eval w) +
            (((A n).map Complex.ofRealHom).eval w - f w)‖ := by
              congr 1
              ring
      _ ≤ ‖((B n).map Complex.ofRealHom).eval w -
              ((A n).map Complex.ofRealHom).eval w‖ +
            ‖((A n).map Complex.ofRealHom).eval w - f w‖ :=
          norm_add_le _ _
      _ < ε := by linarith

end

end RiemannGaussian
