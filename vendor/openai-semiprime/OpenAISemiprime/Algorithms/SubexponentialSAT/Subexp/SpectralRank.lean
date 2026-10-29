import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SpectralRank
import OpenAISemiprime.Algorithms.SubexponentialSAT.BinomialInterpolation
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.MatrixSupport
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.TensorSpectrum

namespace OAI.Algorithms

/-!
# Actual rank bounds for the multi-color swap construction

The linear-algebra input is the dimension of the actual range of `id - M`.
The local swap multiplicities and the finite tail are kept as ordinary natural
counts, and converted to real inequalities only at the final scaling step.
-/

namespace SubexponentialSAT.Subexp.SpectralRank

open Module
open scoped BigOperators

section Rank

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- The previously proved exact range computation gives a real rank bound
by the number of bad basis indices. -/
theorem real_rank_defect_le_bad
    (b : Basis ι K V) (M : V →ₗ[K] V) (eigenvalue : ι → K)
    (good : ι → Prop) [DecidablePred good]
    (hdiag : ∀ i, M (b i) = eigenvalue i • b i)
    (hgood : ∀ i, good i → eigenvalue i = 1) :
    (finrank K (LinearMap.range (LinearMap.id - M)) : ℝ) ≤
      (Fintype.card {i // ¬ good i} : ℝ) := by
  exact_mod_cast _root_.OAI.Algorithms.SubexponentialSAT.SpectralRank.finrank_defect_le_card_bad
    b M eigenvalue good hdiag hgood

/-- Scale an actual rank bound by the number of slot constraints. -/
theorem scaled_rank_defect_le
    (b : Basis ι K V) (M : V →ₗ[K] V) (eigenvalue : ι → K)
    (good : ι → Prop) [DecidablePred good] (d N : ℕ) (τ : ℝ)
    (hdiag : ∀ i, M (b i) = eigenvalue i • b i)
    (hgood : ∀ i, good i → eigenvalue i = 1)
    (hbad : (d : ℝ) * (Fintype.card {i // ¬ good i} : ℝ) ≤ τ * (N : ℝ)) :
    (d : ℝ) * (finrank K (LinearMap.range (LinearMap.id - M)) : ℝ) ≤
      τ * (N : ℝ) :=
  (mul_le_mul_of_nonneg_left (real_rank_defect_le_bad b M eigenvalue good hdiag hgood)
    (Nat.cast_nonneg d)).trans hbad

end Rank

/-- Spectator registers multiply the tail and the total mass by the same
ordinary integer. No field-characteristic condition enters this count. -/
theorem scale_tail_bound (d copies bad total : ℕ) (τ : ℝ)
    (htail : (d : ℝ) * (bad : ℝ) ≤ τ * (total : ℝ)) :
    (d : ℝ) * ((copies * bad : ℕ) : ℝ) ≤ τ * ((copies * total : ℕ) : ℝ) := by
  calc
    _ = (copies : ℝ) * ((d : ℝ) * (bad : ℝ)) := by push_cast; ring
    _ ≤ (copies : ℝ) * (τ * (total : ℝ)) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg copies)
    _ = _ := by push_cast; ring

section Scalar

variable {K α : Type*} [Field K] [DecidableEq α]

/-- The weight-dependent scalar in equation (3.5). -/
def coefficientEigenvalue (R : ℕ) (c : ℕ → K) (w : ℕ) : K :=
  (-1 : K) ^ w * ∑ j ∈ Finset.range R, c j * (w.choose j : K)

/-- Evaluate the actual elementary-symmetric expression at a sign profile.
The integer number of negative signs is retained before coefficients are
cast to the field, so this is valid when the truncation length exceeds the
characteristic. -/
theorem scalar_signIndicator (h2 : (2 : K) ≠ 0)
    (active ones : Finset α) (hsub : ones ⊆ active) (R : ℕ) (c : ℕ → K) :
    ((∏ l ∈ active, if l ∈ ones then (-1 : K) else 1) *
      ∑ j ∈ Finset.range R, c j *
        ∑ A ∈ active.powersetCard j,
          ∏ l ∈ A, (1 - (if l ∈ ones then (-1 : K) else 1)) / 2) =
      coefficientEigenvalue R c ones.card := by
  classical
  have hfilter : active.filter (fun l => l ∈ ones) = ones := by
    ext l
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hprod : (∏ l ∈ active, if l ∈ ones then (-1 : K) else 1) =
      (-1 : K) ^ ones.card := by
    simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one, hfilter]
  have hprojector (l : α) :
      (1 - (if l ∈ ones then (-1 : K) else 1)) / 2 =
        if l ∈ ones then (1 : K) else 0 := by
    by_cases hl : l ∈ ones
    · simp only [ite_eq_left hl, sub_neg_eq_add, one_add_one_eq_two]
      exact div_self h2
    · simp [hl]
  rw [hprod, coefficientEigenvalue]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp_rw [hprojector]
  exact _root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.sum_powersetCard_prod_indicator active ones hsub j

/-- The constructed parity coefficients make that scalar exactly one at
every integer weight in the interpolation interval. -/
theorem coefficientEigenvalue_parity (A R w : ℕ)
    (hw : w ∈ Finset.Ico A (A + R)) :
    coefficientEigenvalue R
      (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
        (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R)) w = 1 := by
  rw [coefficientEigenvalue,
    _root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.sum_range_extend_parity_of_mem A R w
      (Finset.mem_Ico.mp hw).1 (Finset.mem_Ico.mp hw).2,
    ← mul_pow]
  simp

end Scalar

section ProbabilityTail

open SubexponentialSAT.Subexp.TensorSpectrum SubexponentialSAT.SubexpSwapMultiplicity

/-- The probability of an integer weight outside the interpolation interval,
using the actual normalized tensor multiplicities. -/
def normalizedTail (r q A R : ℕ) : ℚ :=
  ∑ w ∈ Finset.range (q + 1),
    if w ∈ Finset.Ico A (A + R) then 0 else swapProbability r q w

/-- A common denominator converts the exact probability tail to the finite
integer multiplicity tail. -/
theorem normalizedTail_eq_weightedTail (r q A R : ℕ) :
    normalizedTail r q A R =
      (weightedTail q (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) /
        (((positiveMultiplicity r + negativeMultiplicity r) ^ q : ℕ) : ℚ) := by
  rw [multiplicities_add]
  simp only [weightedTail, Nat.cast_sum, Nat.cast_pow, Finset.sum_div]
  unfold normalizedTail
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w ∈ Finset.Ico A (A + R)
  · simp [hw]
  · simp [hw, swapProbability, swapMultiplicity]

/-- The probability tail is exactly the source's binomial tail with negative
probability `(r - 1) / (2*r)`. -/
theorem normalizedTail_eq_binomial (r q A R : ℕ) (hr : 0 < r) :
    normalizedTail r q A R =
      ∑ w ∈ Finset.range (q + 1), if w ∈ Finset.Ico A (A + R) then 0 else
        (q.choose w : ℚ) * negativeProbability r ^ w *
          (1 - negativeProbability r) ^ (q - w) := by
  simp only [normalizedTail, swapProbability_eq_binomial r q _ hr]

/-- The source probability bound and the denominator-cleared rank input are
equivalent when there is at least one color and one slot. -/
theorem normalizedTail_le_iff (r q A R d : ℕ) (τ : ℚ)
    (hr : 0 < r) (hd : 0 < d) :
    normalizedTail r q A R ≤ τ / (d : ℚ) ↔
      (d : ℚ) * (weightedTail q (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ q : ℕ) : ℚ) := by
  have htotal : (0 : ℚ) <
      (((positiveMultiplicity r + negativeMultiplicity r) ^ q : ℕ) : ℚ) := by
    rw [multiplicities_add]
    exact_mod_cast (pow_pos (pow_pos hr 2) q)
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  rw [normalizedTail_eq_weightedTail, div_le_div_iff₀ htotal hd']
  rw [mul_comm (_ : ℚ) (d : ℚ)]

end ProbabilityTail

section ConcreteMatrix

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport SubexponentialSAT.Subexp.TensorSpectrum SubexponentialSAT.SubexpSwapMultiplicity

variable {K : Type*} [Field K] {r Q Δ : ℕ}

/-- Evaluate the scalar belonging to the same concrete matrix used by the
support theorem, rather than introducing a second matrix construction. -/
theorem matrixEigenvalue_signIndicator (h2 : (2 : K) ≠ 0) (t : Fin Q)
    (R : ℕ) (c : ℕ → K) (ones : Finset (Fin Q))
    (hsub : ones ⊆ activePositions t) :
    matrixEigenvalue t R c (fun l => if l ∈ ones then (-1 : K) else 1) =
      coefficientEigenvalue R c ones.card := by
  exact scalar_signIndicator h2 (activePositions t) ones hsub R c

/-- The actual matrix acts diagonally on the explicitly constructed tensor
basis, with the integer number of negative local labels as its weight. -/
theorem jointMatrix_eigenbasis (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (R : ℕ) (c : ℕ → K)
    (a : JointBasisIndex t g i) :
    (jointMatrix i t g R c).mulVecLin (jointEigenbasis K h2 t g i a) =
      coefficientEigenvalue R c (jointWeight a) • jointEigenbasis K h2 t g i a := by
  rw [Matrix.mulVecLin_apply]
  have heig := jointMatrix_eigenvector i t g R c (jointSign K a)
    (jointEigenbasis K h2 t g i a) (jointEigenbasis_sign_eigen K h2 t g i a)
  have hvalue : matrixEigenvalue t R c (jointSign K a) =
      coefficientEigenvalue R c (jointWeight a) := by
    change matrixEigenvalue t R c (fun l => if l ∈ negativePositions a then -1 else 1) = _
    simpa only [card_negativePositions] using
      matrixEigenvalue_signIndicator h2 t R c (negativePositions a)
        (negativePositions_subset a)
  rw [hvalue] at heig
  exact heig

/-- Exact rank, retaining every tensor-basis multiplicity. This is useful
also when some eigenvalues outside the interpolation interval equal one. -/
theorem jointMatrix_defect_rank_eq_card (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (R : ℕ) (c : ℕ → K) :
    finrank K (LinearMap.range (LinearMap.id - (jointMatrix i t g R c).mulVecLin)) =
      Nat.card {a : JointBasisIndex t g i // coefficientEigenvalue R c (jointWeight a) ≠ 1} :=
  _root_.OAI.Algorithms.SubexponentialSAT.SpectralRank.finrank_defect_eq_card
    (jointEigenbasis K h2 t g i) (jointMatrix i t g R c).mulVecLin
    (fun a => coefficientEigenvalue R c (jointWeight a))
    (jointMatrix_eigenbasis h2 t g i R c)

/-- Multi-color matrix rank bound in a form with no division. The tail uses
the actual positive and negative local multiplicities and is an ordinary
finite integer sum. -/
theorem jointMatrix_rank_bound_real (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (c : ℕ → K) (τ : ℝ)
    (hcoeff : ∀ w ∈ Finset.Ico A (A + R),
      (∑ j ∈ Finset.range R, c j * (w.choose j : K)) = (-1 : K) ^ w)
    (htail : (Δ : ℝ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℝ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℝ)) :
    (Δ : ℝ) *
      (finrank K (LinearMap.range (LinearMap.id - (jointMatrix i t g R c).mulVecLin)) : ℝ) ≤
        τ * (Fintype.card (Joint t g i) : ℝ) := by
  apply scaled_rank_defect_le (jointEigenbasis K h2 t g i)
    (jointMatrix i t g R c).mulVecLin
    (fun a => coefficientEigenvalue R c (jointWeight a))
    (fun a => jointWeight a ∈ Finset.Ico A (A + R)) Δ (Fintype.card (Joint t g i)) τ
  · exact jointMatrix_eigenbasis h2 t g i R c
  · intro a ha
    rw [coefficientEigenvalue, hcoeff (jointWeight a) ha, ← mul_pow]
    simp
  · rw [card_bad_jointWeight, card_joint_via_multiplicities]
    exact scale_tail_bound Δ (spectatorCard r Q Δ)
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R)
      ((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1)) τ htail

/-- Rational form used by the authoritative multi-color layout interface. -/
theorem jointMatrix_rank_bound (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (c : ℕ → K) (τ : ℚ)
    (hcoeff : ∀ w ∈ Finset.Ico A (A + R),
      (∑ j ∈ Finset.range R, c j * (w.choose j : K)) = (-1 : K) ^ w)
    (htail : (Δ : ℚ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℚ)) :
    (Δ : ℚ) *
      (finrank K (LinearMap.range (LinearMap.id - (jointMatrix i t g R c).mulVecLin)) : ℚ) ≤
        τ * (Fintype.card (Joint t g i) : ℚ) := by
  have ht : (Δ : ℝ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℝ) ≤
        (τ : ℝ) * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℝ) := by
    exact_mod_cast htail
  have hrank := jointMatrix_rank_bound_real h2 t g i A R c (τ : ℝ) hcoeff ht
  exact_mod_cast hrank

/-- Constructed binomial interpolation coefficients discharge the coefficient
hypothesis without any restriction relating the color count to the field. -/
theorem jointMatrix_parity_rank_bound (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (τ : ℚ)
    (htail : (Δ : ℚ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℚ)) :
    (Δ : ℚ) *
      (finrank K (LinearMap.range (LinearMap.id -
        (jointMatrix i t g R (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
          (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R))).mulVecLin)) : ℚ) ≤
        τ * (Fintype.card (Joint t g i) : ℚ) := by
  apply jointMatrix_rank_bound h2 t g i A R
    (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
      (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R)) τ
  · intro w hw
    exact _root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.sum_range_extend_parity_of_mem A R w
      (Finset.mem_Ico.mp hw).1 (Finset.mem_Ico.mp hw).2
  · exact htail

/-- The literal relative-rank conclusion of Lemma 3.1. -/
theorem jointMatrix_parity_rank_relative (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (τ : ℚ)
    (htail : (Δ : ℚ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℚ)) :
    (finrank K (LinearMap.range (LinearMap.id -
      (jointMatrix i t g R (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
        (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R))).mulVecLin)) : ℚ) ≤
      (τ / (Δ : ℚ)) * (Fintype.card (Joint t g i) : ℚ) := by
  have hd : (0 : ℚ) < Δ := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hrank := jointMatrix_parity_rank_bound h2 t g i A R τ htail
  calc
    _ ≤ (τ * (Fintype.card (Joint t g i) : ℚ)) / (Δ : ℚ) := by
      apply (le_div_iff₀ hd).2
      simpa only [mul_comm] using hrank
    _ = _ := by ring

/-- Direct source-form wrapper: an actual binomial probability tail at most
`τ / Δ` bounds the rank defect of the concrete matrix by the same fraction. -/
theorem jointMatrix_parity_rank_of_probability (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (τ : ℚ)
    (htail : normalizedTail r (Q - 1) A R ≤ τ / (Δ : ℚ)) :
    (Δ : ℚ) *
      (finrank K (LinearMap.range (LinearMap.id -
        (jointMatrix i t g R (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
          (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R))).mulVecLin)) : ℚ) ≤
        τ * (Fintype.card (Joint t g i) : ℚ) := by
  apply jointMatrix_parity_rank_bound h2 t g i A R τ
  exact (normalizedTail_le_iff r (Q - 1) A R Δ τ
    (Nat.zero_lt_of_lt g.isLt) (Nat.zero_lt_of_lt i.isLt)).mp htail

/-- The literal rank fraction, now with only the source probability-tail input. -/
theorem jointMatrix_parity_rank_relative_of_probability (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (τ : ℚ)
    (htail : normalizedTail r (Q - 1) A R ≤ τ / (Δ : ℚ)) :
    (finrank K (LinearMap.range (LinearMap.id -
      (jointMatrix i t g R (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
        (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R))).mulVecLin)) : ℚ) ≤
      (τ / (Δ : ℚ)) * (Fintype.card (Joint t g i) : ℚ) := by
  apply jointMatrix_parity_rank_relative h2 t g i A R τ
  exact (normalizedTail_le_iff r (Q - 1) A R Δ τ
    (Nat.zero_lt_of_lt g.isLt) (Nat.zero_lt_of_lt i.isLt)).mp htail

end ConcreteMatrix

end SubexponentialSAT.Subexp.SpectralRank

end OAI.Algorithms
