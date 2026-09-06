import RiemannGaussian.FiniteCircleBandSampling

/-!
# Finite duality for a separated circle spectrum

The exact complex transpose identity precedes Cauchy--Schwarz. The proved
sampling estimate for the integer band then controls arbitrary complex
coefficients on the separated residue spectrum, with the auxiliary grid
size removed and every frequency retained in the synthesis.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

variable {Q : ℕ} [NeZero Q]

/-- Exchanging a residue frequency and an integer sample leaves the
literal character unchanged, with its canonical representative explicit. -/
theorem finiteCircleWave_exchange (k : ZMod Q) (r : ℕ) :
    finiteCircleWave k r = finiteCircleWave (r : ZMod Q) k.val := by
  simp only [finiteCircleWave, ZMod.natCast_zmod_val, mul_comm]

/-- The exact finite transpose identity retains the complete complex
coefficient and test families before any norm or energy estimate. -/
theorem finiteCircleSynthesis_dual_pair (K : Finset (ZMod Q)) (b : ZMod Q → ℂ)
    (a : ℕ → ℂ) (L : ℕ) :
    (∑ r ∈ Finset.range L, finiteCircleSynthesis K id b r * starRingEnd ℂ (a r)) =
      ∑ k ∈ K, b k * finiteCircleSynthesis (Finset.range L)
        (fun r : ℕ ↦ (r : ZMod Q)) (fun r ↦ starRingEnd ℂ (a r)) k.val := by
  simp only [finiteCircleSynthesis, Finset.sum_mul, Finset.mul_sum, id_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro r hr
  rw [finiteCircleWave_exchange k r]
  ring

/-- Finite complex coefficient pairing satisfies the full two-energy
Cauchy--Schwarz bound. -/
theorem norm_sum_mul_sq_le_sum_norm_sq_mul {ι : Type*} (s : Finset ι)
    (b c : ι → ℂ) :
    ‖∑ i ∈ s, b i * c i‖ ^ 2 ≤
      (∑ i ∈ s, ‖b i‖ ^ 2) * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hn : ‖∑ i ∈ s, b i * c i‖ ≤ ∑ i ∈ s, ‖b i‖ * ‖c i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i ↦ b i * c i)
  exact ((sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr hn).trans
      (Finset.sum_mul_sq_le_sq_mul_sq s (fun i ↦ ‖b i‖) (fun i ↦ ‖c i‖))

/-- Finite duality transports the proved integer-band sampling estimate
to arbitrary coefficients on the actual separated residue spectrum. -/
theorem sum_range_finiteCircleSynthesis_separated_le {L h T : ℕ}
    (K : Finset (ZMod Q)) (b : ZMod Q → ℂ)
    (hh : 0 < h) (hT : 0 < T) (hQT : Q = h * T) (hLT : L ≤ T)
    (hsep : ∀ k ∈ K, ∀ l ∈ K, k.val < l.val → k.val + h ≤ l.val) :
    (∑ r ∈ Finset.range L, ‖finiteCircleSynthesis K id b r‖ ^ 2) ≤
      finiteCircleSamplingConstant * T * ∑ k ∈ K, ‖b k‖ ^ 2 := by
  let g := finiteCircleSynthesis K id b
  let E : ℝ := ∑ r ∈ Finset.range L, ‖g r‖ ^ 2
  let H : ZMod Q → ℂ := fun k ↦ finiteCircleSynthesis (Finset.range L)
    (fun r : ℕ ↦ (r : ZMod Q)) (fun r ↦ starRingEnd ℂ (g r)) k.val
  have hE : 0 ≤ E := Finset.sum_nonneg (fun r _ ↦ sq_nonneg _)
  have hH : (∑ k ∈ K, ‖H k‖ ^ 2) ≤ finiteCircleSamplingConstant * T * E := by
    have hs := sum_norm_sq_finiteCircleBand_grid_le (Q := Q)
      (fun r ↦ starRingEnd ℂ (g r)) (K.image ZMod.val) hh hT hQT hLT
      (by intro n hn; obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn; exact k.val_lt)
      (by
        intro n hn m hm hnm
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hm
        exact hsep k hk l hl hnm)
    rw [Finset.sum_image (fun k _ l _ heq ↦ ZMod.val_injective Q heq)] at hs
    simpa only [H, E, Complex.norm_conj] using hs
  have heq : (E : ℂ) = ∑ k ∈ K, b k * H k := by
    have hp := finiteCircleSynthesis_dual_pair K b g L
    change (∑ r ∈ Finset.range L, g r * starRingEnd ℂ (g r)) = _ at hp
    simp_rw [Complex.mul_conj'] at hp
    simpa only [E, H, Complex.ofReal_sum, Complex.ofReal_pow] using hp
  have hsq : E ^ 2 ≤ (∑ k ∈ K, ‖b k‖ ^ 2) *
      (finiteCircleSamplingConstant * T * E) := by
    calc
      _ = ‖∑ k ∈ K, b k * H k‖ ^ 2 := by
        rw [← heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
      _ ≤ _ := (norm_sum_mul_sq_le_sum_norm_sq_mul K b H).trans
        (mul_le_mul_of_nonneg_left hH (Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)))
  change E ≤ _
  rcases eq_or_lt_of_le hE with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg (mul_nonneg finiteCircleSamplingConstant_pos.le (Nat.cast_nonneg T))
      (Finset.sum_nonneg (fun k _ ↦ sq_nonneg _))
  · apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      E * E = E ^ 2 := by ring
      _ ≤ (∑ k ∈ K, ‖b k‖ ^ 2) * (finiteCircleSamplingConstant * T * E) := hsq
      _ = _ := by ring

end

end RiemannGaussian
