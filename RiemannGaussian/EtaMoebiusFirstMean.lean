import RiemannGaussian.EtaMoebiusSelectedFamily

/-!
# Cancellation in the complex physical mean

Shifting a divisor parity wave by that divisor reverses its sign. Pairing
the shifted windows before taking norms controls their complex-power
weight by a derivative estimate. This gives a first-mean estimate without
the quadratic Fourier sampling loss. Both original normalization errors
are retained. The result estimates the mean of a signed sum, not its mean
square or mean absolute value.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

private theorem norm_eta_sign (n : ℕ) : ‖(pairedEtaDirichletSign n : ℂ)‖ = 1 := by
  unfold pairedEtaDirichletSign
  split_ifs <;> norm_num

/-- Pairing a parity wave with its divisor shift bounds its full complex weighted mean before any absolute values are summed. -/
theorem norm_sum_cpow_pairedEtaDivisorParity_le
    (rho : NontrivialZetaZero) {A d : ℕ} (hA : 1 ≤ A) (hd : 1 ≤ d) :
    ‖∑ t ∈ Finset.range A,
      ((A + t : ℕ) : ℂ) ^ (-rho.1) * (pairedEtaDirichletSign ((A + t) / d) : ℂ)‖ ≤
        (2 + ‖rho.1‖) * (d : ℝ) * (A : ℝ) ^ (-rho.1.re) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  let f : ℕ → ℂ := fun t ↦
    ((A + t : ℕ) : ℂ) ^ (-rho.1) * (pairedEtaDirichletSign ((A + t) / d) : ℂ)
  let S := ∑ t ∈ Finset.range A, f t
  let V := ∑ t ∈ Finset.range A, f (t + d)
  have hf (t : ℕ) : ‖f t‖ ≤ (A : ℝ) ^ (-rho.1.re) := by
    dsimp only [f]
    rw [norm_mul, norm_eta_sign, mul_one,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < A + t), Complex.neg_re]
    exact Real.rpow_le_rpow_of_nonpos hAR (by exact_mod_cast Nat.le_add_right A t)
      (by linarith [NontrivialZetaZero.zero_lt_re rho])
  have hshift : S - V = (∑ t ∈ Finset.range d, f t) -
      ∑ t ∈ Finset.range d, f (A + t) := by
    have h1 : (∑ t ∈ Finset.range (A + d), f t) = S +
        ∑ t ∈ Finset.range d, f (A + t) := by rw [Finset.sum_range_add]
    have h2 : (∑ t ∈ Finset.range (A + d), f t) =
        (∑ t ∈ Finset.range d, f t) + V := by
      rw [Nat.add_comm A d, Finset.sum_range_add]
      simp only [V, Nat.add_comm d]
    linear_combination h2 - h1
  have hboundary : ‖S - V‖ ≤ 2 * (d : ℝ) * (A : ℝ) ^ (-rho.1.re) := by
    rw [hshift]
    apply (norm_sub_le _ _).trans
    have hfirst : ‖∑ t ∈ Finset.range d, f t‖ ≤ (d : ℝ) * (A : ℝ) ^ (-rho.1.re) := by
      apply (norm_sum_le _ _).trans
      simpa using Finset.sum_le_sum (s := Finset.range d) (fun t _ ↦ hf t)
    have hlast : ‖∑ t ∈ Finset.range d, f (A + t)‖ ≤ (d : ℝ) * (A : ℝ) ^ (-rho.1.re) := by
      apply (norm_sum_le _ _).trans
      simpa using Finset.sum_le_sum (s := Finset.range d) (fun t _ ↦ hf (A + t))
    linarith
  have hpair (t : ℕ) : ‖f t + f (t + d)‖ ≤
      ‖rho.1‖ * (A : ℝ) ^ (-rho.1.re - 1) * d := by
    have hdiv : (A + (t + d)) / d = (A + t) / d + 1 := by
      rw [← Nat.add_assoc, Nat.add_div_right _ hd]
    have he : f t + f (t + d) =
        (((A + t : ℕ) : ℂ) ^ (-rho.1) - ((A + (t + d) : ℕ) : ℂ) ^ (-rho.1)) *
          (pairedEtaDirichletSign ((A + t) / d) : ℂ) := by
      dsimp only [f]
      rw [hdiv, pairedEtaDirichletSign_add_odd _ _ (by decide : Odd 1)]
      push_cast
      ring
    rw [he, norm_mul, norm_eta_sign, mul_one, norm_sub_rev]
    have hb := norm_cpow_sub_cpow_le_above (-rho.1) hAR
      (by simpa using (show -rho.1.re ≤ 1 by linarith [NontrivialZetaZero.zero_lt_re rho]))
      (show (A : ℝ) ≤ (A + t : ℕ) by exact_mod_cast Nat.le_add_right A t)
      (show (A : ℝ) ≤ (A + (t + d) : ℕ) by exact_mod_cast Nat.le_add_right A (t + d))
    simpa only [norm_neg, Complex.neg_re, Complex.ofReal_natCast, Nat.cast_add,
      Complex.ofReal_add, show ((A : ℝ) + (t + d)) - (A + t) = d by ring,
      abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)] using hb
  have hpower : (A : ℝ) * (A : ℝ) ^ (-rho.1.re - 1) = (A : ℝ) ^ (-rho.1.re) := by
    rw [Real.rpow_sub hAR, Real.rpow_one]
    field_simp
  have hbulk : ‖S + V‖ ≤ ‖rho.1‖ * (d : ℝ) * (A : ℝ) ^ (-rho.1.re) := by
    rw [show S + V = ∑ t ∈ Finset.range A, (f t + f (t + d)) by
      rw [Finset.sum_add_distrib]]
    apply (norm_sum_le _ _).trans
    have hh := Finset.sum_le_sum (s := Finset.range A) (fun t _ ↦ hpair t)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
    apply hh.trans_eq
    calc
      _ = ‖rho.1‖ * (d : ℝ) * ((A : ℝ) * (A : ℝ) ^ (-rho.1.re - 1)) := by ring
      _ = _ := by rw [hpower]
  have htriangle := norm_add_le (S - V) (S + V)
  rw [show (S - V) + (S + V) = (2 : ℂ) * S by ring, norm_mul] at htriangle
  norm_num only [norm_ofNat] at htriangle
  change ‖S‖ ≤ _
  nlinarith [norm_nonneg S]

/-- The physical first-mean constant includes both endpoint errors and the full complex-weight derivative cost. -/
def pairedEtaMoebiusFirstMeanConstant (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
    2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho +
    ‖pairedEtaXiCompletionFactor rho.1‖ / 2 * (2 + ‖rho.1‖)

/-- Every term in the physical first-mean constant is nonnegative. -/
theorem pairedEtaMoebiusFirstMeanConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaMoebiusFirstMeanConstant rho := by
  unfold pairedEtaMoebiusFirstMeanConstant
  have hb := pairedEtaCompletedMoebiusPhysicalErrorConstant_nonneg rho
  have hh := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  positivity

/-- The actual completed divisor term has a first-mean bound retaining its completion and both normalization errors, uniformly up to the physical starting cutoff. -/
theorem norm_sum_pairedEtaCompletedMoebiusTerm_le_firstMean
    (rho : NontrivialZetaZero) {A d : ℕ} (hA : 1 ≤ A) (hd : 1 ≤ d) (hdA : d ≤ A) :
    ‖∑ t ∈ Finset.range A, pairedEtaCompletedMoebiusTerm rho (A + t) d‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * d * (A : ℝ) ^ (-rho.1.re) := by
  let B := pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
    2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho
  have hB : 0 ≤ B := by
    dsimp only [B]
    linarith [pairedEtaCompletedMoebiusPhysicalErrorConstant_nonneg rho,
      pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho]
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  let z : ℕ → ℂ := fun t ↦ ((A + t : ℕ) : ℂ) ^ (-rho.1) *
    pairedEtaCompletedMoebiusParityPhase rho (A + t) d
  have herr (t : ℕ) :
      ‖pairedEtaCompletedMoebiusTerm rho (A + t) d - z t‖ ≤
        B * d * (A : ℝ) ^ (-rho.1.re) / A := by
    have hM : 1 ≤ A + t := hA.trans (Nat.le_add_right A t)
    have hdM : d ∈ Finset.Icc 1 (A + t) :=
      Finset.mem_Icc.mpr ⟨hd, hdA.trans (Nat.le_add_right A t)⟩
    have hMne : ((A + t : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    have hcancel : ((A + t : ℕ) : ℂ) ^ (-rho.1) * ((A + t : ℕ) : ℂ) ^ rho.1 = 1 := by
      rw [← Complex.cpow_add _ _ hMne, neg_add_cancel, Complex.cpow_zero]
    have he : pairedEtaCompletedMoebiusTerm rho (A + t) d - z t =
        ((A + t : ℕ) : ℂ) ^ (-rho.1) *
          (((A + t : ℕ) : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusTerm rho (A + t) d -
            pairedEtaCompletedMoebiusParityPhase rho (A + t) d) := by
      dsimp only [z]
      rw [mul_sub, ← mul_assoc, hcancel, one_mul]
    have hp : ‖((A + t : ℕ) : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusTerm rho (A + t) d -
        pairedEtaCompletedMoebiusParityPhase rho (A + t) d‖ ≤ B * d / (A + t : ℕ) := by
      have h := norm_sub_le_norm_sub_add_norm_sub
        (((A + t : ℕ) : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusTerm rho (A + t) d)
        (pairedEtaCompletedMoebiusEndpointPhase rho (A + t) d)
        (pairedEtaCompletedMoebiusParityPhase rho (A + t) d)
      apply (h.trans (add_le_add
        (norm_pairedEtaCompletedMoebiusTerm_physical_sub_endpoint_le rho hdM)
        (norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le rho hM hd))).trans_eq
      dsimp only [B]
      ring
    rw [he, norm_mul, Complex.norm_natCast_cpow_of_pos hM, Complex.neg_re]
    have hpow : ((A + t : ℕ) : ℝ) ^ (-rho.1.re) ≤ (A : ℝ) ^ (-rho.1.re) :=
      Real.rpow_le_rpow_of_nonpos hAR (by exact_mod_cast Nat.le_add_right A t)
        (by linarith [NontrivialZetaZero.zero_lt_re rho])
    have hp' := hp.trans (div_le_div_of_nonneg_left (by positivity : 0 ≤ B * (d : ℝ))
      hAR (by exact_mod_cast Nat.le_add_right A t))
    exact (mul_le_mul hpow hp' (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have herror :
      ‖(∑ t ∈ Finset.range A, pairedEtaCompletedMoebiusTerm rho (A + t) d) -
        ∑ t ∈ Finset.range A, z t‖ ≤ B * d * (A : ℝ) ^ (-rho.1.re) := by
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    have hh := Finset.sum_le_sum (s := Finset.range A) (fun t _ ↦ herr t)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
    apply hh.trans_eq
    field_simp
  have hmain : ‖∑ t ∈ Finset.range A, z t‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ / 2 * (2 + ‖rho.1‖) * d *
        (A : ℝ) ^ (-rho.1.re) := by
    have he : (∑ t ∈ Finset.range A, z t) =
        ((μ d : ℂ) * pairedEtaXiCompletionFactor rho.1 / 2) *
          ∑ t ∈ Finset.range A, ((A + t : ℕ) : ℂ) ^ (-rho.1) *
            (pairedEtaDirichletSign ((A + t) / d) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [z, pairedEtaCompletedMoebiusParityPhase]
      ring
    have hm : ‖(μ d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hc : ‖(μ d : ℂ) * pairedEtaXiCompletionFactor rho.1 / 2‖ ≤
        ‖pairedEtaXiCompletionFactor rho.1‖ / 2 := by
      rw [norm_div, norm_mul]
      norm_num only [norm_ofNat]
      exact div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right hm (norm_nonneg (pairedEtaXiCompletionFactor rho.1)))
        (by norm_num)
    rw [he, norm_mul]
    exact (mul_le_mul hc (norm_sum_cpow_pairedEtaDivisorParity_le rho hA hd)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  apply (norm_le_insert'
    (∑ t ∈ Finset.range A, pairedEtaCompletedMoebiusTerm rho (A + t) d)
    (∑ t ∈ Finset.range A, z t)).trans
  apply (add_le_add hmain herror).trans_eq
  dsimp only [B, pairedEtaMoebiusFirstMeanConstant]
  ring

/-- The complex physical average of the unchanged selected divisor family. -/
def pairedEtaCompletedMoebiusSelectedFirstMean
    (rho : NontrivialZetaZero) (S : Finset ℕ) (A : ℕ) : ℂ :=
  (∑ t ∈ Finset.range A, pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t)) / A

/-- A selected family has first mean at most `C_rho D² A^(-Re(rho)-1)`; this controls the signed complex average, not its mean square. -/
theorem norm_pairedEtaCompletedMoebiusSelectedFirstMean_le
    (rho : NontrivialZetaZero) {S : Finset ℕ} {A D : ℕ}
    (hS : S ⊆ Finset.Icc 1 D) (hA : 1 ≤ A) (hDA : D ≤ A) :
    ‖pairedEtaCompletedMoebiusSelectedFirstMean rho S A‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * (D : ℝ) ^ 2 * (A : ℝ) ^ (-rho.1.re - 1) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hC := pairedEtaMoebiusFirstMeanConstant_nonneg rho
  have hcount : (S.card : ℝ) ≤ D := by
    exact_mod_cast (Finset.card_le_card hS).trans_eq (by simp)
  have hsum : ‖∑ t ∈ Finset.range A, pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t)‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * (D : ℝ) ^ 2 * (A : ℝ) ^ (-rho.1.re) := by
    simp only [pairedEtaCompletedMoebiusSelectedAggregate]
    rw [Finset.sum_comm]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d ∈ S, pairedEtaMoebiusFirstMeanConstant rho * D * (A : ℝ) ^ (-rho.1.re) := by
        apply Finset.sum_le_sum
        intro d hdS
        obtain ⟨hd, hdD⟩ := Finset.mem_Icc.mp (hS hdS)
        apply (norm_sum_pairedEtaCompletedMoebiusTerm_le_firstMean rho hA hd (hdD.trans hDA)).trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hdD) hC) (by positivity)
      _ ≤ (D : ℝ) * (pairedEtaMoebiusFirstMeanConstant rho * D * (A : ℝ) ^ (-rho.1.re)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by ring
  rw [pairedEtaCompletedMoebiusSelectedFirstMean, norm_div, Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hsum hAR.le).trans_eq
  rw [Real.rpow_sub hAR, Real.rpow_one]
  ring

end

end RiemannGaussian
