import RiemannGaussian.External.Zeta23Benchmark
import RiemannGaussian.GaussianXiDivisorContour

/-!
# Zeta23 counts as finite project zero windows

The imported Zeta23 benchmark is stated with set cardinalities of complex
zeros. The eta development is indexed by this project's subtype
`NontrivialZetaZero` and finite windows. This module closes that representation
seam.

For arbitrary ordinates `T₁ < Im rho ≤ T₂`, Lean constructs finite project
windows of all distinct nontrivial zeros, their critical-line subset, and the
simple critical-line subset.
The subtype coercion maps these windows exactly onto `Zeta23.zerosIn` and its
critical-line intersection. Consequently their cardinalities are exactly
`Zeta23.Ndist`, `Zeta23.N0star`, and `Zeta23.N0simple`.

The final theorems restate both the exact Montgomery--Taylor benchmark and
its checked strict gain over `2/3` directly on these project-native finite
windows. They are still corollaries of attributed external prior work, not a
new eta certificate.
-/

open Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Project nontriviality and Zeta23 strip nontriviality define the same zeta
zeros. The reverse direction uses the project's proved critical-strip
location theorem. -/
theorem zeta23IsNontrivialZero_iff_isNontrivialZetaZero (s : ℂ) :
    Zeta23.IsNontrivialZero s ↔ IsNontrivialZetaZero s := by
  constructor
  · intro hs
    exact ⟨hs.1, hs.not_trivial⟩
  · intro hs
    let rho : NontrivialZetaZero := ⟨s, hs⟩
    exact ⟨hs.1, NontrivialZetaZero.zero_lt_re rho,
      NontrivialZetaZero.re_lt_one rho⟩

/-- Project-subtype zeros with ordinate in the half-open window
`T₁ < Im rho ≤ T₂`. -/
def positiveSpectralZetaZeroWindowSet (T₁ T₂ : ℝ) :
    Set NontrivialZetaZero :=
  {rho | T₁ < rho.1.im ∧ rho.1.im ≤ T₂}

/-- Every bounded ordinate window of project-subtype nontrivial zeros is
finite. -/
theorem positiveSpectralZetaZeroWindowSet_finite (T₁ T₂ : ℝ) :
    (positiveSpectralZetaZeroWindowSet T₁ T₂).Finite := by
  let R : ℝ := max |T₁| |T₂|
  have hR0 : 0 ≤ R := by
    exact (abs_nonneg T₁).trans (le_max_left |T₁| |T₂|)
  apply (spectralZetaZeroWindow R).finite_toSet.subset
  intro rho hrho
  apply (mem_spectralZetaZeroWindow hR0 rho).2
  rw [zetaSpectralCoordinate_re, abs_le]
  change T₁ < rho.1.im ∧ rho.1.im ≤ T₂ at hrho
  constructor
  · calc
      -R ≤ -|T₁| := neg_le_neg (le_max_left |T₁| |T₂|)
      _ ≤ T₁ := neg_abs_le T₁
      _ ≤ rho.1.im := hrho.1.le
  · calc
      rho.1.im ≤ T₂ := hrho.2
      _ ≤ |T₂| := le_abs_self T₂
      _ ≤ R := le_max_right |T₁| |T₂|

/-- The finite project-native window of distinct nontrivial zeta zeros with
`T₁ < Im rho ≤ T₂`. -/
def positiveSpectralZetaZeroWindow (T₁ T₂ : ℝ) :
    Finset NontrivialZetaZero :=
  (positiveSpectralZetaZeroWindowSet_finite T₁ T₂).toFinset

@[simp]
theorem mem_positiveSpectralZetaZeroWindow
    {T₁ T₂ : ℝ} {rho : NontrivialZetaZero} :
    rho ∈ positiveSpectralZetaZeroWindow T₁ T₂ ↔
      T₁ < rho.1.im ∧ rho.1.im ≤ T₂ := by
  simp [positiveSpectralZetaZeroWindow,
    positiveSpectralZetaZeroWindowSet]

/-- Project-subtype critical-line zeros in the same half-open ordinate
window. -/
def positiveSpectralCriticalZetaZeroWindowSet (T₁ T₂ : ℝ) :
    Set NontrivialZetaZero :=
  {rho | rho ∈ positiveSpectralZetaZeroWindowSet T₁ T₂ ∧
    rho.1.re = 1 / 2}

/-- The critical-line subset of every project-native ordinate window is
finite. -/
theorem positiveSpectralCriticalZetaZeroWindowSet_finite (T₁ T₂ : ℝ) :
    (positiveSpectralCriticalZetaZeroWindowSet T₁ T₂).Finite := by
  apply (positiveSpectralZetaZeroWindowSet_finite T₁ T₂).subset
  intro rho hrho
  exact hrho.1

/-- The finite project-native critical-line subset of a positive ordinate
window. -/
def positiveSpectralCriticalZetaZeroWindow (T₁ T₂ : ℝ) :
    Finset NontrivialZetaZero :=
  (positiveSpectralCriticalZetaZeroWindowSet_finite T₁ T₂).toFinset

@[simp]
theorem mem_positiveSpectralCriticalZetaZeroWindow
    {T₁ T₂ : ℝ} {rho : NontrivialZetaZero} :
    rho ∈ positiveSpectralCriticalZetaZeroWindow T₁ T₂ ↔
      (T₁ < rho.1.im ∧ rho.1.im ≤ T₂) ∧ rho.1.re = 1 / 2 := by
  simp [positiveSpectralCriticalZetaZeroWindow,
    positiveSpectralCriticalZetaZeroWindowSet,
    positiveSpectralZetaZeroWindowSet]

/-- The named critical window is exactly the critical-line filter of the
full project-native window. -/
theorem positiveSpectralCriticalZetaZeroWindow_eq_filter (T₁ T₂ : ℝ) :
    positiveSpectralCriticalZetaZeroWindow T₁ T₂ =
      (positiveSpectralZetaZeroWindow T₁ T₂).filter
        (fun rho ↦ rho.1.re = 1 / 2) := by
  ext rho
  simp [and_assoc]

/-- Project-subtype simple critical-line zeros in a half-open ordinate
window. -/
def positiveSpectralSimpleCriticalZetaZeroWindowSet (T₁ T₂ : ℝ) :
    Set NontrivialZetaZero :=
  {rho | rho ∈ positiveSpectralCriticalZetaZeroWindowSet T₁ T₂ ∧
    analyticZetaZeroMultiplicity rho = 1}

/-- Every simple critical-line ordinate window is finite. -/
theorem positiveSpectralSimpleCriticalZetaZeroWindowSet_finite (T₁ T₂ : ℝ) :
    (positiveSpectralSimpleCriticalZetaZeroWindowSet T₁ T₂).Finite := by
  apply (positiveSpectralCriticalZetaZeroWindowSet_finite T₁ T₂).subset
  intro rho hrho
  exact hrho.1

/-- The finite project-native window of simple critical-line zeta zeros. -/
def positiveSpectralSimpleCriticalZetaZeroWindow (T₁ T₂ : ℝ) :
    Finset NontrivialZetaZero :=
  (positiveSpectralSimpleCriticalZetaZeroWindowSet_finite T₁ T₂).toFinset

@[simp]
theorem mem_positiveSpectralSimpleCriticalZetaZeroWindow
    {T₁ T₂ : ℝ} {rho : NontrivialZetaZero} :
    rho ∈ positiveSpectralSimpleCriticalZetaZeroWindow T₁ T₂ ↔
      ((T₁ < rho.1.im ∧ rho.1.im ≤ T₂) ∧ rho.1.re = 1 / 2) ∧
        analyticZetaZeroMultiplicity rho = 1 := by
  simp [positiveSpectralSimpleCriticalZetaZeroWindow,
    positiveSpectralSimpleCriticalZetaZeroWindowSet,
    positiveSpectralCriticalZetaZeroWindowSet,
    positiveSpectralZetaZeroWindowSet]

/-- The two projects use definitionally the same analytic multiplicity for a
nontrivial zeta zero. -/
theorem analyticZetaZeroMultiplicity_eq_zeta23ZeroMult
    (rho : NontrivialZetaZero) :
    analyticZetaZeroMultiplicity rho = Zeta23.zeroMult rho.1 := by
  rfl

/-- For nonnegative `T`, the positive dyadic window is exactly the indicated
filter of the symmetric spectral window already used by the eta carrier. -/
theorem positiveSpectralZetaZeroWindow_dyadic_eq_spectral_filter
    {T : ℝ} (hT : 0 ≤ T) :
    positiveSpectralZetaZeroWindow T (2 * T) =
      (spectralZetaZeroWindow (2 * T)).filter
        (fun rho ↦ T < rho.1.im) := by
  have h2T : 0 ≤ 2 * T := mul_nonneg (by norm_num) hT
  ext rho
  rw [mem_positiveSpectralZetaZeroWindow, Finset.mem_filter,
    mem_spectralZetaZeroWindow h2T, zetaSpectralCoordinate_re]
  constructor
  · intro hrho
    have him0 : 0 ≤ rho.1.im := hT.trans hrho.1.le
    exact ⟨by simpa [abs_of_nonneg him0] using hrho.2, hrho.1⟩
  · intro hrho
    have him0 : 0 ≤ rho.1.im := hT.trans hrho.2.le
    exact ⟨hrho.2, by simpa [abs_of_nonneg him0] using hrho.1⟩

/-- The project-native critical dyadic window is the corresponding
critical-line filter of the symmetric eta spectral window. -/
theorem positiveSpectralCriticalZetaZeroWindow_dyadic_eq_spectral_filter
    {T : ℝ} (hT : 0 ≤ T) :
    positiveSpectralCriticalZetaZeroWindow T (2 * T) =
      (spectralZetaZeroWindow (2 * T)).filter
        (fun rho ↦ T < rho.1.im ∧ rho.1.re = 1 / 2) := by
  rw [positiveSpectralCriticalZetaZeroWindow_eq_filter,
    positiveSpectralZetaZeroWindow_dyadic_eq_spectral_filter hT]
  ext rho
  simp [and_assoc]

/-- Coercing the project-native window to complex numbers gives exactly the
Zeta23 zero set. -/
theorem image_positiveSpectralZetaZeroWindowSet_val (T₁ T₂ : ℝ) :
    ((fun rho : NontrivialZetaZero ↦ (rho.1 : ℂ)) ''
        positiveSpectralZetaZeroWindowSet T₁ T₂) =
      Zeta23.zerosIn T₁ T₂ := by
  ext s
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    exact ⟨(zeta23IsNontrivialZero_iff_isNontrivialZetaZero rho.1).2 rho.2,
      hrho⟩
  · intro hs
    change Zeta23.IsNontrivialZero s ∧ T₁ < s.im ∧ s.im ≤ T₂ at hs
    let rho : NontrivialZetaZero :=
      ⟨s, (zeta23IsNontrivialZero_iff_isNontrivialZetaZero s).1 hs.1⟩
    exact ⟨rho, hs.2, rfl⟩

/-- Coercing the project-native critical window gives exactly Zeta23's
critical-line intersection. -/
theorem image_positiveSpectralCriticalZetaZeroWindowSet_val (T₁ T₂ : ℝ) :
    ((fun rho : NontrivialZetaZero ↦ (rho.1 : ℂ)) ''
        positiveSpectralCriticalZetaZeroWindowSet T₁ T₂) =
      Zeta23.zerosIn T₁ T₂ ∩ {rho | rho.re = 1 / 2} := by
  ext s
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    exact ⟨
      ⟨(zeta23IsNontrivialZero_iff_isNontrivialZetaZero rho.1).2 rho.2,
        hrho.1⟩,
      hrho.2⟩
  · intro hs
    change
      (Zeta23.IsNontrivialZero s ∧ T₁ < s.im ∧ s.im ≤ T₂) ∧
        s.re = 1 / 2 at hs
    let rho : NontrivialZetaZero :=
      ⟨s, (zeta23IsNontrivialZero_iff_isNontrivialZetaZero s).1 hs.1.1⟩
    exact ⟨rho, ⟨hs.1.2, hs.2⟩, rfl⟩

/-- Coercing the project-native simple critical window gives exactly
Zeta23's literal simple critical-line zero set. -/
theorem image_positiveSpectralSimpleCriticalZetaZeroWindowSet_val
    (T₁ T₂ : ℝ) :
    ((fun rho : NontrivialZetaZero ↦ (rho.1 : ℂ)) ''
        positiveSpectralSimpleCriticalZetaZeroWindowSet T₁ T₂) =
      Zeta23.zerosIn T₁ T₂ ∩ {rho | rho.re = 1 / 2} ∩
        {rho | Zeta23.zeroMult rho = 1} := by
  ext s
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    exact ⟨
      ⟨
        ⟨(zeta23IsNontrivialZero_iff_isNontrivialZetaZero rho.1).2 rho.2,
          hrho.1.1⟩,
        hrho.1.2⟩,
      by simpa [analyticZetaZeroMultiplicity_eq_zeta23ZeroMult] using hrho.2⟩
  · intro hs
    change
      ((Zeta23.IsNontrivialZero s ∧ T₁ < s.im ∧ s.im ≤ T₂) ∧
        s.re = 1 / 2) ∧ Zeta23.zeroMult s = 1 at hs
    let rho : NontrivialZetaZero :=
      ⟨s, (zeta23IsNontrivialZero_iff_isNontrivialZetaZero s).1 hs.1.1.1⟩
    refine ⟨rho, ?_, rfl⟩
    exact ⟨⟨hs.1.1.2, hs.1.2⟩,
      by simpa [analyticZetaZeroMultiplicity_eq_zeta23ZeroMult] using hs.2⟩

/-- The project-native distinct-zero window card is exactly `Zeta23.Ndist`.
-/
theorem card_positiveSpectralZetaZeroWindow_eq_Ndist (T₁ T₂ : ℝ) :
    (positiveSpectralZetaZeroWindow T₁ T₂).card =
      Zeta23.Ndist T₁ T₂ := by
  let S := positiveSpectralZetaZeroWindowSet T₁ T₂
  have hfinite := positiveSpectralZetaZeroWindowSet_finite T₁ T₂
  calc
    (positiveSpectralZetaZeroWindow T₁ T₂).card = S.ncard := by
      exact (Set.ncard_eq_toFinset_card S hfinite).symm
    _ = ((fun rho : NontrivialZetaZero ↦ (rho.1 : ℂ)) '' S).ncard :=
      Subtype.val_injective.injOn.ncard_image.symm
    _ = (Zeta23.zerosIn T₁ T₂).ncard := by
      rw [image_positiveSpectralZetaZeroWindowSet_val]
    _ = Zeta23.Ndist T₁ T₂ := rfl

/-- The project-native critical-window card is exactly `Zeta23.N0star`. -/
theorem card_positiveSpectralCriticalZetaZeroWindow_eq_N0star
    (T₁ T₂ : ℝ) :
    (positiveSpectralCriticalZetaZeroWindow T₁ T₂).card =
      Zeta23.N0star T₁ T₂ := by
  let S := positiveSpectralCriticalZetaZeroWindowSet T₁ T₂
  have hfinite := positiveSpectralCriticalZetaZeroWindowSet_finite T₁ T₂
  calc
    (positiveSpectralCriticalZetaZeroWindow T₁ T₂).card = S.ncard := by
      exact (Set.ncard_eq_toFinset_card S hfinite).symm
    _ = ((fun rho : NontrivialZetaZero ↦ (rho.1 : ℂ)) '' S).ncard :=
      Subtype.val_injective.injOn.ncard_image.symm
    _ = (Zeta23.zerosIn T₁ T₂ ∩ {rho | rho.re = 1 / 2}).ncard := by
      rw [image_positiveSpectralCriticalZetaZeroWindowSet_val]
    _ = Zeta23.N0star T₁ T₂ := rfl

/-- The project-native simple critical-window card is exactly
`Zeta23.N0simple`. -/
theorem card_positiveSpectralSimpleCriticalZetaZeroWindow_eq_N0simple
    (T₁ T₂ : ℝ) :
    (positiveSpectralSimpleCriticalZetaZeroWindow T₁ T₂).card =
      Zeta23.N0simple T₁ T₂ := by
  let S := positiveSpectralSimpleCriticalZetaZeroWindowSet T₁ T₂
  have hfinite :=
    positiveSpectralSimpleCriticalZetaZeroWindowSet_finite T₁ T₂
  calc
    (positiveSpectralSimpleCriticalZetaZeroWindow T₁ T₂).card = S.ncard := by
      exact (Set.ncard_eq_toFinset_card S hfinite).symm
    _ = ((fun rho : NontrivialZetaZero ↦ (rho.1 : ℂ)) '' S).ncard :=
      Subtype.val_injective.injOn.ncard_image.symm
    _ = (Zeta23.zerosIn T₁ T₂ ∩ {rho | rho.re = 1 / 2} ∩
        {rho | Zeta23.zeroMult rho = 1}).ncard := by
      rw [image_positiveSpectralSimpleCriticalZetaZeroWindowSet_val]
    _ = Zeta23.N0simple T₁ T₂ := rfl

/-- The exact imported Montgomery--Taylor benchmark, now stated entirely on
project-native finite windows of the actual zeta-zero subtype. -/
theorem externalZeta23_montgomeryTaylor_projectFiniteWindows :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 - ε) *
          ((positiveSpectralZetaZeroWindow T (2 * T)).card : ℝ) ≤
        (positiveSpectralCriticalZetaZeroWindow T (2 * T)).card := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    externalZeta23_montgomeryTaylor_distinctDenominator ε hε
  refine ⟨T₀, fun T hT ↦ ?_⟩
  rw [card_positiveSpectralZetaZeroWindow_eq_Ndist,
    card_positiveSpectralCriticalZetaZeroWindow_eq_N0star]
  exact hT₀ T hT

/-- The actual multiplicity-aware Montgomery--Taylor headline theorem on the
project-native simple critical window.  The denominator remains the literal
analytic-multiplicity count `Ncount`; no distinct-denominator weakening is
used. -/
theorem externalZeta23_montgomeryTaylor_simple_projectFiniteWindows :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ) ≤
        (positiveSpectralSimpleCriticalZetaZeroWindow T (2 * T)).card := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    externalZeta23_montgomeryTaylor_simpleCritical ε hε
  refine ⟨T₀, fun T hT ↦ ?_⟩
  rw [card_positiveSpectralSimpleCriticalZetaZeroWindow_eq_N0simple]
  exact hT₀ T hT

/-- The checked strict positive gain over two-thirds, now stated entirely on
project-native finite windows. -/
theorem externalZeta23_strictlyAboveTwoThirds_projectFiniteWindows :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 : ℝ) / 3 + externalZeta23StrictGainOverTwoThirds - ε) *
          ((positiveSpectralZetaZeroWindow T (2 * T)).card : ℝ) ≤
        (positiveSpectralCriticalZetaZeroWindow T (2 * T)).card := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    externalZeta23_strictlyAboveTwoThirds_distinctDenominator ε hε
  refine ⟨T₀, fun T hT ↦ ?_⟩
  rw [card_positiveSpectralZetaZeroWindow_eq_Ndist,
    card_positiveSpectralCriticalZetaZeroWindow_eq_N0star]
  exact hT₀ T hT

end

end RiemannGaussian
