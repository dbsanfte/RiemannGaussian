import RiemannGaussian.Hybrid.EtaGeometricModeSeparation

/-!
# Quantitative decorrelation of finite eta phase blocks

This module turns the checked collision-free eta modes into a quantitative
finite-block statement. For a unit mode `z`, its first `M` powers form a
literal finite vector. The correlation of the vectors for `z` and `w` is the
geometric sum with ratio `star w * z`. Lean retains that complex sum exactly
and proves the phase-sensitive estimate

`|correlation|^2 * |star w * z - 1|^2 <= 4`.

Since a finite injective family of unit modes has a positive minimum phase
gap, its distinct-pair squared normalized coherences are uniformly bounded by
`4 / (M^2 * gap^2)`. The result is instantiated on every finite same-real-part
family of nontrivial zeta zeros and, in particular, on each critical-zero
window after selecting one collision-free odd prime base.

This supplies a scalable quantitative angular estimate rather than mere
linear independence. It is not yet a bound for the literal finite eta-prefix
frame: the remaining transport step must compare sufficiently long normalized
eta blocks with these phase vectors while retaining the off-line real-decay
channel. No improved zero proportion is proved here.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The first `M` powers of one complex geometric mode. -/
def finiteGeometricPhaseVector (M : ℕ) (z : ℂ) : Fin M → ℂ :=
  fun j ↦ z ^ (j : ℕ)

/-- A length-`M` unit-mode vector has squared norm exactly `M`. -/
theorem finiteGeometricPhaseVector_normSq
    (M : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ∑ j : Fin M, ‖finiteGeometricPhaseVector M z j‖ ^ 2 = M := by
  simp [finiteGeometricPhaseVector, norm_pow, hz]

/-- Correlation of two finite mode vectors is the corresponding geometric
sum, with its full complex phase retained. -/
theorem finiteGeometricPhaseVector_correlation_eq_geomSum
    (M : ℕ) (z w : ℂ) :
    star (finiteGeometricPhaseVector M w) ⬝ᵥ
        finiteGeometricPhaseVector M z =
      ∑ j ∈ Finset.range M, (star w * z) ^ j := by
  calc
    _ = ∑ j : Fin M, (star w * z) ^ (j : ℕ) := by
      simp [dotProduct, finiteGeometricPhaseVector, mul_pow]
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ (star w * z) ^ j) M

/-- A finite geometric sum on the unit circle, multiplied by its exact phase
gap from one, has norm at most two. -/
theorem finite_unit_geometric_sum_mul_gap_le_two
    (M : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖∑ j ∈ Finset.range M, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- The correlation of two finite unit-mode vectors obeys the sharp
phase-gap-times-correlation bound. -/
theorem finiteGeometricPhaseVector_correlation_mul_gap_le_two
    (M : ℕ) (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖star (finiteGeometricPhaseVector M w) ⬝ᵥ
        finiteGeometricPhaseVector M z‖ * ‖star w * z - 1‖ ≤ 2 := by
  rw [finiteGeometricPhaseVector_correlation_eq_geomSum]
  apply finite_unit_geometric_sum_mul_gap_le_two
  rw [norm_mul, norm_star, hz, hw]
  norm_num

/-- Distinct unit modes have a nonzero relative phase gap. -/
theorem finiteGeometricPhaseVector_gap_ne_zero
    (z w : ℂ) (hw : ‖w‖ = 1) (hzw : z ≠ w) :
    star w * z - 1 ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hwstar : w * star w = 1 := by
    change w * conj w = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    norm_num
  apply hzw
  calc
    z = 1 * z := by rw [one_mul]
    _ = (w * star w) * z := by rw [hwstar]
    _ = w * (star w * z) := by rw [mul_assoc]
    _ = w := by rw [h, mul_one]

/-- Squaring the phase-gap estimate gives a four-bound for the squared
correlation. -/
theorem finiteGeometricPhaseVector_correlation_sq_mul_gap_sq_le_four
    (M : ℕ) (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖star (finiteGeometricPhaseVector M w) ⬝ᵥ
        finiteGeometricPhaseVector M z‖ ^ 2 *
          ‖star w * z - 1‖ ^ 2 ≤ 4 := by
  have h := finiteGeometricPhaseVector_correlation_mul_gap_le_two
    M z w hz hw
  have hnonneg :
      0 ≤ ‖star (finiteGeometricPhaseVector M w) ⬝ᵥ
          finiteGeometricPhaseVector M z‖ * ‖star w * z - 1‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg
    (‖star (finiteGeometricPhaseVector M w) ⬝ᵥ
        finiteGeometricPhaseVector M z‖ * ‖star w * z - 1‖)]

/-- Squared normalized correlation of two finite geometric phase vectors. -/
def finiteGeometricPhaseCoherenceSq (M : ℕ) (z w : ℂ) : ℝ :=
  ‖star (finiteGeometricPhaseVector M w) ⬝ᵥ
      finiteGeometricPhaseVector M z‖ ^ 2 / (M : ℝ) ^ 2

/-- Normalized squared coherence, multiplied by the exact squared phase gap,
decays at the explicit rate `4 / M^2`. -/
theorem finiteGeometricPhaseCoherenceSq_mul_gap_sq_le
    (M : ℕ) (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    finiteGeometricPhaseCoherenceSq M z w * ‖star w * z - 1‖ ^ 2 ≤
      4 / (M : ℝ) ^ 2 := by
  have hMnonneg : 0 ≤ (M : ℝ) ^ 2 := sq_nonneg _
  calc
    _ = (‖star (finiteGeometricPhaseVector M w) ⬝ᵥ
          finiteGeometricPhaseVector M z‖ ^ 2 *
            ‖star w * z - 1‖ ^ 2) / (M : ℝ) ^ 2 := by
      unfold finiteGeometricPhaseCoherenceSq
      ring
    _ ≤ 4 / (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right
        (finiteGeometricPhaseVector_correlation_sq_mul_gap_sq_le_four
          M z w hz hw) hMnonneg

/-- Once block length times phase gap exceeds two, two distinct unit-mode
vectors have squared normalized coherence strictly below one. -/
theorem finiteGeometricPhaseCoherenceSq_lt_one
    (M : ℕ) (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hlarge : 4 < (M : ℝ) ^ 2 * ‖star w * z - 1‖ ^ 2) :
    finiteGeometricPhaseCoherenceSq M z w < 1 := by
  have hbound :=
    finiteGeometricPhaseVector_correlation_sq_mul_gap_sq_le_four
      M z w hz hw
  have hgap : 0 < ‖star w * z - 1‖ ^ 2 := by
    by_contra hzero
    have hle : ‖star w * z - 1‖ ^ 2 ≤ 0 := le_of_not_gt hzero
    nlinarith [sq_nonneg ‖star w * z - 1‖]
  have hM : 0 < (M : ℝ) ^ 2 := by
    by_contra hzero
    have hle : (M : ℝ) ^ 2 ≤ 0 := le_of_not_gt hzero
    nlinarith [sq_nonneg (M : ℝ)]
  unfold finiteGeometricPhaseCoherenceSq
  apply (div_lt_one hM).2
  nlinarith

/-- Every finite injective family of at least two unit modes has one positive
minimum relative phase gap. -/
theorem exists_uniform_finiteGeometricPhaseGap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode : ι → ℂ) (hunit : ∀ i, ‖mode i‖ = 1)
    (hinj : Function.Injective mode) (hcard : 1 < Fintype.card ι) :
    ∃ g : ℝ, 0 < g ∧
      ∀ a b : ι, a ≠ b → g ≤ ‖star (mode b) * mode a - 1‖ := by
  let pairs := ((Finset.univ : Finset ι).product Finset.univ).filter
    (fun p ↦ p.1 ≠ p.2)
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hcard
  have hpairs : pairs.Nonempty := by
    refine ⟨(a, b), ?_⟩
    simp [pairs, hab]
  let gaps : Finset ℝ := pairs.image
    (fun p ↦ ‖star (mode p.2) * mode p.1 - 1‖)
  have hgaps : gaps.Nonempty := hpairs.image _
  let g := gaps.min' hgaps
  refine ⟨g, ?_, ?_⟩
  · have hgmem : g ∈ gaps := Finset.min'_mem gaps hgaps
    obtain ⟨p, hp, hpg⟩ := Finset.mem_image.mp hgmem
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hmode : mode p.1 ≠ mode p.2 := fun h ↦ hpne (hinj h)
    rw [← hpg]
    exact norm_pos_iff.mpr
      (finiteGeometricPhaseVector_gap_ne_zero
        (mode p.1) (mode p.2) (hunit p.2) hmode)
  · intro i j hij
    apply Finset.min'_le gaps
    apply Finset.mem_image.mpr
    refine ⟨(i, j), ?_, rfl⟩
    simp [pairs, hij]

/-- For a finite injective unit-mode family, one fixed positive gap gives a
simultaneous `O(M^-2)` bound on every distinct-pair squared coherence. -/
theorem exists_uniform_finiteGeometricPhaseCoherence_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode : ι → ℂ) (hunit : ∀ i, ‖mode i‖ = 1)
    (hinj : Function.Injective mode) (hcard : 1 < Fintype.card ι) :
    ∃ g : ℝ, 0 < g ∧
      ∀ (M : ℕ) (a b : ι), a ≠ b →
        finiteGeometricPhaseCoherenceSq M (mode a) (mode b) * g ^ 2 ≤
          4 / (M : ℝ) ^ 2 := by
  obtain ⟨g, hg, hgap⟩ :=
    exists_uniform_finiteGeometricPhaseGap mode hunit hinj hcard
  refine ⟨g, hg, ?_⟩
  intro M a b hab
  have hcoh := finiteGeometricPhaseCoherenceSq_mul_gap_sq_le
    M (mode a) (mode b) (hunit a) (hunit b)
  have hcohNonneg :
      0 ≤ finiteGeometricPhaseCoherenceSq M (mode a) (mode b) := by
    unfold finiteGeometricPhaseCoherenceSq
    positivity
  have hgapNonneg : 0 ≤ ‖star (mode b) * mode a - 1‖ := norm_nonneg _
  have hgLe := hgap a b hab
  have hgSq : g ^ 2 ≤ ‖star (mode b) * mode a - 1‖ ^ 2 := by
    nlinarith
  nlinarith

/-- On a finite same-real-part zeta-zero layer with at least two elements, one
odd prime supplies a positive phase gap and a uniform `O(M^-2)` coherence
bound for all distinct normalized eta modes. -/
theorem exists_prime_uniform_etaGeometricNormalizedModeCoherence_bound
    (s : Finset NontrivialZetaZero) {σ : ℝ}
    (hre : ∀ ρ : NontrivialZetaZero, ρ ∈ s → ρ.val.re = σ)
    (hcard : 1 < s.card) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∃ g : ℝ, 0 < g ∧
        ∀ (M : ℕ) (ρ ζ : s), ρ ≠ ζ →
          finiteGeometricPhaseCoherenceSq M
              (etaGeometricNormalizedMode q ρ.1.val)
              (etaGeometricNormalizedMode q ζ.1.val) * g ^ 2 ≤
            4 / (M : ℝ) ^ 2 := by
  obtain ⟨q, hqPrime, hqOdd, hq, hinj⟩ :=
    exists_prime_etaGeometricNormalizedMode_injOn_zetaZeros_same_re s hre
  let mode : s → ℂ := fun ρ ↦ etaGeometricNormalizedMode q ρ.1.val
  have hunit : ∀ ρ, ‖mode ρ‖ = 1 := fun ρ ↦
    norm_etaGeometricNormalizedMode hq.le ρ.1.val
  have hmodeInj : Function.Injective mode := by
    intro ρ ζ hmode
    apply Subtype.ext
    exact hinj ρ.2 ζ.2 hmode
  have hcardSubtype : 1 < Fintype.card s := by
    simpa using hcard
  obtain ⟨g, hg, hbound⟩ :=
    exists_uniform_finiteGeometricPhaseCoherence_bound
      mode hunit hmodeInj hcardSubtype
  exact ⟨q, hqPrime, hqOdd, hq, g, hg, hbound⟩

/-- The preceding quantitative prime-and-gap selection specializes to every
critical-zero window containing at least two distinct zeros. -/
theorem exists_prime_uniform_spectralCriticalZetaZeroWindowModeCoherence_bound
    (T : ℝ) (hcard : 1 < (spectralCriticalZetaZeroWindow T).card) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∃ g : ℝ, 0 < g ∧
        ∀ (M : ℕ) (ρ ζ : (spectralCriticalZetaZeroWindow T)), ρ ≠ ζ →
          finiteGeometricPhaseCoherenceSq M
              (etaGeometricNormalizedMode q ρ.1.val)
              (etaGeometricNormalizedMode q ζ.1.val) * g ^ 2 ≤
            4 / (M : ℝ) ^ 2 := by
  apply exists_prime_uniform_etaGeometricNormalizedModeCoherence_bound
    (spectralCriticalZetaZeroWindow T) (hcard := hcard)
  intro ρ hρ
  exact (zetaSpectralCoordinate_im_eq_zero_iff ρ.val).1
    (mem_spectralCriticalZetaZeroWindow.mp hρ).2

end

end RiemannGaussian
