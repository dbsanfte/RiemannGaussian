import Zeta23.Assembly
import Zeta23.ZeroSide.RankTraceMult

/-!
# A fourth-moment certificate for the literal Zeta23 matrix

This file supplies the finite-dimensional spectral inequality needed to feed a
one-sided fourth-moment estimate into `Zeta23.seamA_BC`.  It makes no positivity
assumption on the Hermitian matrix: the certificate polynomial is at least one
on the whole nonpositive half-line.
-/

namespace RiemannGaussian

noncomputable section

open Matrix Finset
open RHLinalg
open scoped BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rational degree-four Chebyshev--Markov certificate. -/
def fourthMomentCertificate (x : ℝ) : ℝ :=
  (1 - 7 / 4 * x + 2 / 3 * x ^ 2) ^ 2

lemma fourthMomentCertificate_nonneg (x : ℝ) :
    0 ≤ fourthMomentCertificate x := by
  exact sq_nonneg _

/-- On the entire low spectral sector `x ≤ θ`, the certificate is bounded
below by its elementary threshold surrogate.  The negative sector causes no
loss. -/
lemma fourthMomentCertificate_threshold_lower {x θ : ℝ}
    (hθ1 : θ ≤ 1 / 2) (hx : x ≤ θ) :
    (1 - 7 / 4 * θ) ^ 2 ≤ fourthMomentCertificate x := by
  have hb0 : 0 ≤ 1 - 7 / 4 * θ := by nlinarith
  have hbase : 1 - 7 / 4 * θ ≤ 1 - 7 / 4 * x + 2 / 3 * x ^ 2 := by
    nlinarith [sq_nonneg x]
  exact pow_le_pow_left₀ hb0 hbase 2

/-- The certificate at spectral scale `s`.  The Zeta23 matrix in tilde units
has eigenvalues of size `a L`; its unit-scale moments are therefore obtained
by applying the polynomial to `x / (a L)`. -/
def scaledFourthMomentCertificate (s x : ℝ) : ℝ :=
  fourthMomentCertificate (x / s)

lemma scaledFourthMomentCertificate_nonneg (s x : ℝ) :
    0 ≤ scaledFourthMomentCertificate s x := by
  exact fourthMomentCertificate_nonneg _

lemma scaledFourthMomentCertificate_threshold_lower {s x θ : ℝ}
    (hs : 0 < s) (hθ1 : θ / s ≤ 1 / 2) (hx : x ≤ θ) :
    (1 - 7 / 4 * (θ / s)) ^ 2 ≤ scaledFourthMomentCertificate s x := by
  exact fourthMomentCertificate_threshold_lower hθ1
    (div_le_div_of_nonneg_right hx hs.le)

/-- The low-eigenvalue count times the threshold value of the certificate is
at most its spectral sum. -/
lemma lowEigenvalue_count_mul_certificate_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {θ : ℝ}
    (hθ1 : θ ≤ 1 / 2) :
    (1 - 7 / 4 * θ) ^ 2 *
        ((Fintype.card n : ℝ) - (posIndexAbove hA θ : ℝ)) ≤
      ∑ i, fourthMomentCertificate (hA.eigenvalues i) := by
  classical
  let low : Finset n := Finset.univ.filter fun i => hA.eigenvalues i ≤ θ
  have hlow : (low.card : ℝ) * (1 - 7 / 4 * θ) ^ 2 ≤
      ∑ i ∈ low, fourthMomentCertificate (hA.eigenvalues i) := by
    calc
      (low.card : ℝ) * (1 - 7 / 4 * θ) ^ 2 =
          ∑ _ ∈ low, (1 - 7 / 4 * θ) ^ 2 := by simp
      _ ≤ ∑ i ∈ low, fourthMomentCertificate (hA.eigenvalues i) :=
        Finset.sum_le_sum fun i hi =>
          fourthMomentCertificate_threshold_lower hθ1 (Finset.mem_filter.mp hi).2
  have hsubset : ∑ i ∈ low, fourthMomentCertificate (hA.eigenvalues i) ≤
      ∑ i, fourthMomentCertificate (hA.eigenvalues i) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => fourthMomentCertificate_nonneg _)
  have hcard : low.card + posIndexAbove hA θ = Fintype.card n := by
    simpa [low, posIndexAbove, not_lt, add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset n)) (p := fun i => θ < hA.eigenvalues i))
  have hcast : (low.card : ℝ) =
      (Fintype.card n : ℝ) - (posIndexAbove hA θ : ℝ) := by
    have hcardR : (low.card : ℝ) + (posIndexAbove hA θ : ℝ) =
        (Fintype.card n : ℝ) := by exact_mod_cast hcard
    linarith
  rw [← hcast, mul_comm]
  exact hlow.trans hsubset

/-- Exact expansion of the spectral certificate in the first four matrix
moments. -/
lemma sum_fourthMomentCertificate_eigenvalues
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (∑ i, fourthMomentCertificate (hA.eigenvalues i)) =
      (Fintype.card n : ℝ)
        - 7 / 2 * rtrace A
        + 211 / 48 * rtrace (A ^ 2)
        - 7 / 3 * rtrace (A ^ 3)
        + 4 / 9 * rtrace (A ^ 4) := by
  rw [rtrace_eq_sum_eigenvalues hA,
    Zeta23.ZeroSide.RankTraceMult.rtrace_pow_succ hA 1,
    Zeta23.ZeroSide.RankTraceMult.rtrace_pow_succ hA 2,
    Zeta23.ZeroSide.RankTraceMult.rtrace_pow_succ hA 3]
  simp_rw [fourthMomentCertificate]
  rw [show (∑ i : n, (1 - 7 / 4 * hA.eigenvalues i +
      2 / 3 * hA.eigenvalues i ^ 2) ^ 2) =
      ∑ i : n, (1 - 7 / 2 * hA.eigenvalues i
        + 211 / 48 * hA.eigenvalues i ^ 2
        - 7 / 3 * hA.eigenvalues i ^ 3
        + 4 / 9 * hA.eigenvalues i ^ 4) by
      apply Finset.sum_congr rfl
      intro i _
      ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  rw [← Finset.mul_sum Finset.univ (fun i => hA.eigenvalues i) (7 / 2),
    ← Finset.mul_sum Finset.univ (fun i => hA.eigenvalues i ^ 2) (211 / 48),
    ← Finset.mul_sum Finset.univ (fun i => hA.eigenvalues i ^ 3) (7 / 3),
    ← Finset.mul_sum Finset.univ (fun i => hA.eigenvalues i ^ 4) (4 / 9)]
  ring

/-- Matrix-moment form of the low-sector certificate. -/
theorem posIndexAbove_fourthMoment_lower
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {θ B : ℝ}
    (hθ1 : θ ≤ 1 / 2)
    (hB : (Fintype.card n : ℝ)
        - 7 / 2 * rtrace A
        + 211 / 48 * rtrace (A ^ 2)
        - 7 / 3 * rtrace (A ^ 3)
        + 4 / 9 * rtrace (A ^ 4) ≤ B) :
    (1 - 7 / 4 * θ) ^ 2 *
        ((Fintype.card n : ℝ) - (posIndexAbove hA θ : ℝ)) ≤ B := by
  rw [← sum_fourthMomentCertificate_eigenvalues hA] at hB
  exact (lowEigenvalue_count_mul_certificate_le hA hθ1).trans hB

/-- Exact expansion of the scale-corrected certificate. -/
lemma sum_scaledFourthMomentCertificate_eigenvalues
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {s : ℝ} (hs : s ≠ 0) :
    (∑ i, scaledFourthMomentCertificate s (hA.eigenvalues i)) =
      (Fintype.card n : ℝ)
        - 7 / (2 * s) * rtrace A
        + 211 / (48 * s ^ 2) * rtrace (A ^ 2)
        - 7 / (3 * s ^ 3) * rtrace (A ^ 3)
        + 4 / (9 * s ^ 4) * rtrace (A ^ 4) := by
  rw [rtrace_eq_sum_eigenvalues hA,
    Zeta23.ZeroSide.RankTraceMult.rtrace_pow_succ hA 1,
    Zeta23.ZeroSide.RankTraceMult.rtrace_pow_succ hA 2,
    Zeta23.ZeroSide.RankTraceMult.rtrace_pow_succ hA 3]
  simp_rw [scaledFourthMomentCertificate, fourthMomentCertificate]
  rw [show (∑ i : n, (1 - 7 / 4 * (hA.eigenvalues i / s) +
      2 / 3 * (hA.eigenvalues i / s) ^ 2) ^ 2) =
      ∑ i : n, (1 - 7 / (2 * s) * hA.eigenvalues i
        + 211 / (48 * s ^ 2) * hA.eigenvalues i ^ 2
        - 7 / (3 * s ^ 3) * hA.eigenvalues i ^ 3
        + 4 / (9 * s ^ 4) * hA.eigenvalues i ^ 4) by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
      ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  rw [← Finset.mul_sum Finset.univ (fun i => hA.eigenvalues i) (7 / (2 * s)),
    ← Finset.mul_sum Finset.univ (fun i => hA.eigenvalues i ^ 2) (211 / (48 * s ^ 2)),
    ← Finset.mul_sum Finset.univ (fun i => hA.eigenvalues i ^ 3) (7 / (3 * s ^ 3)),
    ← Finset.mul_sum Finset.univ (fun i => hA.eigenvalues i ^ 4) (4 / (9 * s ^ 4))]
  ring

/-- Scale-corrected fourth-moment bound for the number of eigenvalues above
`θ`. -/
theorem posIndexAbove_scaledFourthMoment_lower
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {s θ B : ℝ}
    (hs : 0 < s) (hθ1 : θ / s ≤ 1 / 2)
    (hB : (Fintype.card n : ℝ)
        - 7 / (2 * s) * rtrace A
        + 211 / (48 * s ^ 2) * rtrace (A ^ 2)
        - 7 / (3 * s ^ 3) * rtrace (A ^ 3)
        + 4 / (9 * s ^ 4) * rtrace (A ^ 4) ≤ B) :
    (1 - 7 / 4 * (θ / s)) ^ 2 *
        ((Fintype.card n : ℝ) - (posIndexAbove hA θ : ℝ)) ≤ B := by
  classical
  let low : Finset n := Finset.univ.filter fun i => hA.eigenvalues i ≤ θ
  have hlow : (low.card : ℝ) * (1 - 7 / 4 * (θ / s)) ^ 2 ≤
      ∑ i ∈ low, scaledFourthMomentCertificate s (hA.eigenvalues i) := by
    calc
      (low.card : ℝ) * (1 - 7 / 4 * (θ / s)) ^ 2 =
          ∑ _ ∈ low, (1 - 7 / 4 * (θ / s)) ^ 2 := by simp
      _ ≤ ∑ i ∈ low, scaledFourthMomentCertificate s (hA.eigenvalues i) :=
        Finset.sum_le_sum fun i hi =>
          scaledFourthMomentCertificate_threshold_lower hs hθ1
            (Finset.mem_filter.mp hi).2
  have hsubset : ∑ i ∈ low, scaledFourthMomentCertificate s (hA.eigenvalues i) ≤
      ∑ i, scaledFourthMomentCertificate s (hA.eigenvalues i) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => scaledFourthMomentCertificate_nonneg _ _)
  have hcard : low.card + posIndexAbove hA θ = Fintype.card n := by
    simpa [low, posIndexAbove, not_lt, add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset n)) (p := fun i => θ < hA.eigenvalues i))
  have hcast : (low.card : ℝ) =
      (Fintype.card n : ℝ) - (posIndexAbove hA θ : ℝ) := by
    have hcardR : (low.card : ℝ) + (posIndexAbove hA θ : ℝ) =
        (Fintype.card n : ℝ) := by exact_mod_cast hcard
    linarith
  rw [← sum_scaledFourthMomentCertificate_eigenvalues hA hs.ne'] at hB
  rw [← hcast, mul_comm]
  exact hlow.trans (hsubset.trans hB)

section LiteralZeta23Seam

open Zeta23 Zeta23.Assembly

/-- Fixed-height, correctly scaled fourth-moment endgame for the concrete
matrix used by Zeta23.  The scale `a L` converts the tilde-unit spectrum to
the unit-scale spectrum on which the rational moment constants live. -/
theorem zeta23_simple_lower_of_scaledFourthMoment
    (Z : ZeroConfig) (P : Params) {T θ₀ B : ℝ}
    (hT : 0 ≤ T) (hBlock : BlockInputs Z P T)
    (hTail : TailInputs Z P T θ₀)
    (hGt : (P.tilde T (Z.Gz P T)).IsHermitian)
    (hscale : 0 < P.a T * P.L T)
    (hθhalf : θ₀ / (P.a T * P.L T) ≤ 1 / 2)
    (hMoment : (P.d T : ℝ)
        - 7 / (2 * (P.a T * P.L T)) * rtrace (P.tilde T (Z.Gz P T))
        + 211 / (48 * (P.a T * P.L T) ^ 2) *
            rtrace ((P.tilde T (Z.Gz P T)) ^ 2)
        - 7 / (3 * (P.a T * P.L T) ^ 3) *
            rtrace ((P.tilde T (Z.Gz P T)) ^ 3)
        + 4 / (9 * (P.a T * P.L T) ^ 4) *
            rtrace ((P.tilde T (Z.Gz P T)) ^ 4) ≤ B) :
    2 * (P.d T : ℝ) - (Z.N T (2 * T) : ℝ) - 2 * (NII Z T : ℝ)
        - 2 * (B / (1 - 7 / 4 * (θ₀ / (P.a T * P.L T))) ^ 2) ≤
      Z.N0s T (2 * T) := by
  have hqbase : 0 < 1 - 7 / 4 * (θ₀ / (P.a T * P.L T)) := by nlinarith
  have hq : 0 < (1 - 7 / 4 * (θ₀ / (P.a T * P.L T))) ^ 2 :=
    sq_pos_of_pos hqbase
  have hMoment' : (Fintype.card (Fin (P.d T)) : ℝ)
        - 7 / (2 * (P.a T * P.L T)) * rtrace (P.tilde T (Z.Gz P T))
        + 211 / (48 * (P.a T * P.L T) ^ 2) *
            rtrace ((P.tilde T (Z.Gz P T)) ^ 2)
        - 7 / (3 * (P.a T * P.L T) ^ 3) *
            rtrace ((P.tilde T (Z.Gz P T)) ^ 3)
        + 4 / (9 * (P.a T * P.L T) ^ 4) *
            rtrace ((P.tilde T (Z.Gz P T)) ^ 4) ≤ B := by
    simpa using hMoment
  have hcert := posIndexAbove_scaledFourthMoment_lower hGt hscale hθhalf hMoment'
  have hlow : (P.d T : ℝ) - (posIndexAbove hGt θ₀ : ℝ) ≤
      B / (1 - 7 / 4 * (θ₀ / (P.a T * P.L T))) ^ 2 := by
    apply (le_div_iff₀ hq).2
    simpa [mul_comm] using hcert
  have hzero := (seamA_BC hT hBlock hTail le_rfl hGt).1
  linarith

end LiteralZeta23Seam

end

end RiemannGaussian
