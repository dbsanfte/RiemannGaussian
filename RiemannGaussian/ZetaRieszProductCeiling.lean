/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmoothPrimeProduct

/-!
# Product-ceiling and large smooth-cofactor bounds

The exact prime/cofactor product ceiling leaves harmonic cofactor mass.
Beyond the physical cofactor cutoff its complete quadratic prime head has
an independent geometric allowance whenever 2*u^2<1. The actual signed
pair response, arbitrary subband masks and all filter offsets remain.
-/

namespace RiemannGaussian.ZetaRieszProductCeiling
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSmoothPrimeProduct

/-- Retaining the actual product ceiling trades the prime-prefix cost
against the cofactor power exactly, leaving harmonic cofactor mass. -/
theorem norm_pairResponse_le_harmonic (keep : ℕ → Prop) (A Q : Finset ℕ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hQ : ∀ p ∈ Q, p.Prime)
    {L q : ℝ} (hL : 0 < L) (hq : 1 / 2 < q) :
    ‖pairResponse keep A Q P N y L‖ ≤
      (64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      (1 + 1 / (q - 1 / 2)) * ((2 : ℝ) ^ (32 * N)) ^ (q - 1 / 2) *
      ∑ a ∈ A, (2 : ℝ) ^ a.primeFactors.card * Real.exp (-Real.log a) := by
  let B : ℕ := 2 ^ (32 * N)
  let C : ℝ := 64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
    ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  let alpha : ℝ := q - 1 / 2
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hq0 : 0 < q := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : (0 : ℝ) < B := by dsimp [B]; positivity
  have hi (a : ℕ) (ha : a ∈ A) :
      ‖∑ p ∈ Q, if p * a ∈ zetaPrimeLogBand N ∧ keep (p * a) then
        SquarefreeVaughanLogSource.coefficient L (p * a) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p * a : ℕ) else 0‖ ≤
      C * (1 + 1 / alpha) * (B : ℝ) ^ alpha *
        ((2 : ℝ) ^ a.primeFactors.card * Real.exp (-Real.log a)) := by
    have ha0 : 0 < a := Nat.pos_of_ne_zero (hA a ha).ne_zero
    have haR : (0 : ℝ) < a := by exact_mod_cast ha0
    let T := Q.filter (fun p => p * a ∈ zetaPrimeLogBand N ∧ keep (p * a))
    let w : ℝ := (2 : ℝ) ^ a.primeFactors.card *
      Real.exp (-(3 / 2 - q) * Real.log a)
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have hT : T ⊆ Finset.Icc 1 (B / a) := by
      intro p hp
      obtain ⟨hp, hb⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_Icc.mpr
      refine ⟨(hQ p hp).pos, (Nat.le_div_iff_mul_le ha0).mpr ?_⟩
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hb.1).1).2
    have hdiv : ((B / a : ℕ) : ℝ) ≤ (B : ℝ) / a := by
      apply (le_div_iff₀ haR).mpr
      exact_mod_cast Nat.div_mul_le_self B a
    calc
      _ = ‖∑ p ∈ T, SquarefreeVaughanLogSource.coefficient L (p * a) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p * a : ℕ)‖ := by
        simp only [T, Finset.sum_filter]
      _ ≤ ∑ p ∈ T, C * w * (p : ℝ) ^ (alpha - 1) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hp, hb⟩ := Finset.mem_filter.mp hp
        exact norm_prime_pair_atom_le P N y (hA a ha) (hQ p hp) hb.1 hL hq
      _ = C * w * ∑ p ∈ T, (p : ℝ) ^ (alpha - 1) := by rw [Finset.mul_sum]
      _ ≤ C * w * ((1 + 1 / alpha) * ((B / a : ℕ) : ℝ) ^ alpha) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hw)
        apply le_trans _ (ZetaRieszGeneralCofactorTilt.sum_rpow_prefix_le halpha (B / a))
        exact Finset.sum_le_sum_of_subset_of_nonneg hT (fun p _ _ => by positivity)
      _ ≤ C * w * ((1 + 1 / alpha) * ((B : ℝ) / a) ^ alpha) := by
        gcongr
      _ = _ := by
        rw [Real.div_rpow hB.le haR.le, Real.rpow_def_of_pos haR, Real.exp_neg]
        dsimp [w]
        have he : Real.exp (-(3 / 2 - q) * Real.log a) /
            Real.exp (Real.log a * alpha) = (Real.exp (Real.log a))⁻¹ := by
          rw [← Real.exp_sub, ← Real.exp_neg]
          congr 1
          dsimp [alpha]
          ring
        calc
          _ = C * (1 + 1 / alpha) * (B : ℝ) ^ alpha * (2 : ℝ) ^ a.primeFactors.card *
              (Real.exp (-(3 / 2 - q) * Real.log a) / Real.exp (Real.log a * alpha)) := by ring
          _ = _ := by rw [he]; ring
  calc
    _ ≤ ∑ a ∈ A, ‖∑ p ∈ Q, if p * a ∈ zetaPrimeLogBand N ∧ keep (p * a) then
        SquarefreeVaughanLogSource.coefficient L (p * a) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p * a : ℕ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ A, C * (1 + 1 / alpha) * (B : ℝ) ^ alpha *
        ((2 : ℝ) ^ a.primeFactors.card * Real.exp (-Real.log a)) :=
      Finset.sum_le_sum hi
    _ = _ := by simp only [← Finset.mul_sum, B, Nat.cast_pow, Nat.cast_ofNat, C, alpha]

/-- A lower cofactor cutoff pays half of the harmonic weight, while
all prime support is retained in the remaining Euler product. -/
theorem harmonic_head_tail_le (A S : Finset ℕ) (hA : ∀ a ∈ A, Squarefree a)
    (hS : ∀ a ∈ A, a.primeFactors ⊆ S) {X : ℝ} (hX : 0 < X)
    (hlarge : ∀ a ∈ A, X ≤ a) :
    (∑ a ∈ A, (2 : ℝ) ^ a.primeFactors.card * Real.exp (-Real.log a)) ≤
      Real.exp (-(1 / 2 : ℝ) * Real.log X) *
        ∏ p ∈ S, (1 + 2 * Real.exp (-(1 / 2 : ℝ) * Real.log p)) := by
  calc
    _ ≤ ∑ a ∈ A, Real.exp (-(1 / 2 : ℝ) * Real.log X) *
        ((2 : ℝ) ^ a.primeFactors.card * Real.exp (-(1 / 2 : ℝ) * Real.log a)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hl := Real.log_le_log hX (hlarge a ha)
      have he : Real.exp (-(1 / 2 : ℝ) * Real.log a) ≤
          Real.exp (-(1 / 2 : ℝ) * Real.log X) := Real.exp_le_exp.mpr (by linarith)
      calc
        _ = Real.exp (-(1 / 2 : ℝ) * Real.log a) *
            ((2 : ℝ) ^ a.primeFactors.card * Real.exp (-(1 / 2 : ℝ) * Real.log a)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)
    _ = Real.exp (-(1 / 2 : ℝ) * Real.log X) *
        ∑ a ∈ A, (2 : ℝ) ^ a.primeFactors.card * Real.exp (-(1 / 2 : ℝ) * Real.log a) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ZetaRieszSmoothHead.squarefree_head_mass_le A S hA hS (1 / 2)) (by positivity)

/-- The full prime/cofactor response has an independent large-cofactor
allowance, retaining the original product ceiling and every subband mask. -/
theorem norm_pairResponse_large_cofactor_le (keep : ℕ → Prop) (A Q S : Finset ℕ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hS : ∀ a ∈ A, a.primeFactors ⊆ S)
    (hQ : ∀ p ∈ Q, p.Prime) {L q X : ℝ} (hL : 0 < L) (hq : 1 / 2 < q)
    (hX : 0 < X) (hlarge : ∀ a ∈ A, X ≤ a) :
    ‖pairResponse keep A Q P N y L‖ ≤
      (64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      (1 + 1 / (q - 1 / 2)) * ((2 : ℝ) ^ (32 * N)) ^ (q - 1 / 2) *
      (Real.exp (-(1 / 2 : ℝ) * Real.log X) *
        ∏ p ∈ S, (1 + 2 * Real.exp (-(1 / 2 : ℝ) * Real.log p))) := by
  have hq0 : 0 < q := by linarith
  apply (norm_pairResponse_le_harmonic keep A Q P N y hA hQ hL hq).trans
  apply mul_le_mul_of_nonneg_left (harmonic_head_tail_le A S hA hS hX hlarge) (by positivity)

/-- Beyond the physical prime cutoff, a composite smooth cofactor
below that cutoff has exactly zero original coefficient. -/
theorem coefficient_eq_zero_of_beyond_physical {u : ℝ} {N a p : ℕ}
    (ha : Squarefree a) (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (hsmall : ∀ r ∈ a.primeFactors, r ≤ N ^ 2) (hp : p.Prime) (hbig : N ^ 2 < p)
    (hpa : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)
    (haX : a ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (p * a) = 0 := by
  have hnd : ¬ p ∣ a := by
    intro hd
    have hm := (Nat.mem_primeFactors_of_ne_zero ha.ne_zero).mpr ⟨hp, hd⟩
    exact (not_le_of_gt hbig) (hsmall p hm)
  apply ZetaRieszFixedCofactor.coefficient_prime_mul_eq_zero_of_large ha ha1 hap hp hnd
  · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero)
    exact_mod_cast haX
  · apply Real.log_le_log (by positivity)
    exact_mod_cast hpa

/-- The reciprocal square root of the literal physical cutoff has a
source-scale bound with its integer floor retained at every order. -/
theorem physical_reciprocal_le {u : ℝ} (hu : 0 < u) (N : ℕ) :
    Real.exp (-(1 / 2 : ℝ) * SquarefreeVaughanLogSource.length u N) ≤
      ((N : ℝ) + 1) * u ^ N := by
  let d : ℝ := ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hx : 0 < u⁻¹ ^ N / ((N : ℝ) + 1) := by positivity
  have hfloor : u⁻¹ ^ N / ((N : ℝ) + 1) ≤ d := by
    have h := Nat.lt_floor_add_one (u⁻¹ ^ N / ((N : ℝ) + 1))
    dsimp [d, ZetaVaughanCutoffBudget.linearDampedCutoff, ZetaVaughanCutoffBudget.dampedCutoff]
    linarith
  have he : Real.exp (-(1 / 2 : ℝ) * SquarefreeVaughanLogSource.length u N) = 1 / d := by
    unfold SquarefreeVaughanLogSource.length
    change Real.exp (-(1 / 2 : ℝ) * Real.log (d ^ 2)) = 1 / d
    rw [Real.log_pow]
    norm_num
    rw [show -((1 / 2 : ℝ) * (2 * Real.log d)) = -Real.log d by ring,
      Real.exp_neg, Real.exp_log hd]
  rw [he]
  apply (one_div_le_one_div_of_le hx hfloor).trans_eq
  rw [one_div_div, inv_pow]
  field_simp

/-- The rate obtained from the exact product ceiling and a cofactor
beyond the physical cutoff; its boundary value is twice the squared source scale. -/
def largeCofactorRate (u q : ℝ) : ℝ :=
  u ^ 2 * Real.exp (32 * (q - 1 / 2) * Real.log 2) / q

/-- Every positive admissible tilt gives a positive large-cofactor rate. -/
theorem largeCofactorRate_pos {u q : ℝ} (hu : 0 < u) (hq : 0 < q) :
    0 < largeCofactorRate u q := by unfold largeCofactorRate; positivity

/-- The literal large-cofactor response has a full-filter quadratic
polynomial allowance times the exact geometric rate and complete prime head. -/
theorem norm_scaled_large_cofactor_le (keep : ℕ → Prop) (A Q S : Finset ℕ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hS : ∀ a ∈ A, a.primeFactors ⊆ S)
    (hQ : ∀ p ∈ Q, p.Prime) {u q : ℝ} (hu : 0 < u) (hq : 1 / 2 < q)
    (hlarge : ∀ a ∈ A, (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a) :
    ‖(u : ℂ) ^ (N + 1) * pairResponse keep A Q P N y (SquarefreeVaughanLogSource.length u N)‖ ≤
      (64 * Real.log 2 * u * (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        (1 + 1 / (q - 1 / 2))) * (N : ℝ) * ((N : ℝ) + 1) *
      (∏ p ∈ S, (1 + 2 * Real.exp (-(1 / 2 : ℝ) * Real.log p))) *
      largeCofactorRate u q ^ N := by
  have hq0 : 0 < q := by linarith
  have hb := norm_pairResponse_large_cofactor_le keep A Q S P N y hA hS hQ
    (SquarefreeVaughanLogSource.length_pos u N) hq
    (by positivity : (0 : ℝ) < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2)
    (fun a ha => by exact_mod_cast hlarge a ha)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg hu.le _)).trans
  calc
    _ ≤ u ^ (N + 1) *
        ((64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
          ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        (1 + 1 / (q - 1 / 2)) * ((2 : ℝ) ^ (32 * N)) ^ (q - 1 / 2) *
        ((((N : ℝ) + 1) * u ^ N) *
          ∏ p ∈ S, (1 + 2 * Real.exp (-(1 / 2 : ℝ) * Real.log p)))) := by
      gcongr
      exact physical_reciprocal_le hu N
    _ = _ := by
      have he : ((2 : ℝ) ^ (32 * N)) ^ (q - 1 / 2) =
          Real.exp (32 * (q - 1 / 2) * Real.log 2) ^ N := by
        rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [he]
      simp only [largeCofactorRate, div_pow, mul_pow, inv_pow, pow_succ]
      ring

/-- A strict boundary saving supplies an admissible positive tilt;
this is proved analytically for all source scales with twice their square below one. -/
theorem exists_large_cofactor_tilt {u : ℝ} (hu2 : 2 * u ^ 2 < 1) :
    ∃ q : ℝ, 1 / 2 < q ∧ largeCofactorRate u q < 1 := by
  have hc : ContinuousAt (fun q : ℝ => largeCofactorRate u q) (1 / 2) := by
    unfold largeCofactorRate
    fun_prop (disch := norm_num)
  have h0 : largeCofactorRate u (1 / 2) < 1 := by
    simpa [largeCofactorRate, div_eq_mul_inv, mul_comm] using hu2
  have he : ∀ᶠ q : ℝ in nhds (1 / 2), largeCofactorRate u q < 1 :=
    hc.eventually (gt_mem_nhds h0)
  obtain ⟨a, b, ⟨ha, hb⟩, hs⟩ := he.exists_Ioo_subset
  refine ⟨(1 / 2 + b) / 2, by linarith, hs ?_⟩
  exact ⟨by linarith, by linarith⟩

/-- Every large quadratic-head cofactor family has independent decay
at the original orders, with arbitrary prime families and subband masks. -/
theorem tendsto_large_cofactor_pairResponse (keep : ℕ → ℕ → Prop)
    (A Q S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    (hA : ∀ N a, a ∈ A N → Squarefree a)
    (hS : ∀ N a, a ∈ A N → a.primeFactors ⊆ S N)
    (hprime : ∀ N p, p ∈ S N → p.Prime ∧ p ≤ N ^ 2)
    (hQ : ∀ N p, p ∈ Q N → p.Prime) {u : ℝ} (hu : 0 < u)
    (hu2 : 2 * u ^ 2 < 1)
    (hlarge : ∀ N a, a ∈ A N →
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      pairResponse (keep N) (A N) (Q N) P N y (SquarefreeVaughanLogSource.length u N))
      atTop (nhds 0) := by
  obtain ⟨q, hq, hrate⟩ := exists_large_cofactor_tilt hu2
  let r : ℝ := largeCofactorRate u q
  have hr : 0 < r := largeCofactorRate_pos hu (by linarith)
  obtain ⟨eps, heps, hsmall⟩ := ZetaRieszEulerPrimeHeadDensity.exists_small_exponential_factor hr hrate
  let C : ℝ := 64 * Real.log 2 * u * (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
    (1 + 1 / (q - 1 / 2))
  have hq0 : 0 < q := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * pairResponse (keep N) (A N) (Q N) P N y
        (SquarefreeVaughanLogSource.length u N)‖ ≤
      C * (((N : ℝ) + 1) ^ 2 * (r * Real.exp eps) ^ N) := by
    filter_upwards [ZetaRieszEulerPrimeHeadDensity.eventually_quadratic_head_product_le heps]
      with N hN
    apply (norm_scaled_large_cofactor_le (keep N) (A N) (Q N) (S N) P N y
      (hA N) (hS N) (hQ N) hu hq (hlarge N)).trans
    calc
      _ ≤ C * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (eps * N) * r ^ N := by
        gcongr
        exact hN (S N) (hprime N) (1 / 2) le_rfl
      _ = C * ((N : ℝ) * ((N : ℝ) + 1) * (r * Real.exp eps) ^ N) := by
        rw [show eps * (N : ℝ) = (N : ℝ) * eps by ring, Real.exp_nat_mul, mul_pow]
        ring
      _ ≤ _ := by
        gcongr
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
  apply squeeze_zero_norm' hb
  simpa only [mul_zero] using
    (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
      (mul_pos hr (Real.exp_pos eps)) hsmall).const_mul C

end
end RiemannGaussian.ZetaRieszProductCeiling
