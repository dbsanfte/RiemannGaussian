/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovLowDegreeTail

/-!
# Paying a single original tail endpoint

The diagonal tail configurations give a lower bound for the actual mixed
moment. A two-term weighted power inequality then pays one additional
unit Fourier atom with factor two once the retained tail is long enough.
All original block frequencies and tail coordinates remain present.
-/

namespace RiemannGaussian.VinogradovEndpointDeletion
noncomputable section
open scoped BigOperators Classical
open MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPartitionEnergy VinogradovMixedMoments

/-- The same normalized Haar measure as the original mixed count. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle Haar measure is a probability measure. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Every tail tuple supplies a diagonal configuration for every
original block collision, regardless of the tail frequency map. -/
theorem diagonal_tail_le {ι κ a : Type*} [Fintype ι] [Fintype κ] [Fintype a]
    (r s : ℕ) (v : ι → a → ℤ) (u : κ → a → ℤ) :
    (Fintype.card κ : ℝ) ^ s * moment r v ≤ mixedMoment r s v u := by
  rw [moment_eq_collisionCount, mixedMoment_eq_count]
  have hn : collisionCount r v * Fintype.card κ ^ s ≤
      differenceCount (configurationFrequency r s v u) 0 := by
    let S := Finset.univ.filter (fun xy : (Fin r → ι) × (Fin r → ι) =>
      (∑ j, v (xy.1 j)) = ∑ j, v (xy.2 j))
    let g (z : ((Fin r → ι) × (Fin r → ι)) × (Fin s → κ)) :=
      ((z.1.1, z.2), (z.1.2, z.2))
    have hc := Finset.card_le_card_of_injOn g
      (s := S ×ˢ (Finset.univ : Finset (Fin s → κ)))
      (t := Finset.univ.filter (fun z =>
        configurationFrequency r s v u z.1 = configurationFrequency r s v u z.2 + 0))
      (by
        intro z hz
        have he := (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [g, configurationFrequency, tupleFrequency, add_zero, he])
      (by
        intro x hx y hy he
        apply Prod.ext
        · exact Prod.ext (congrArg (fun z => z.1.1) he) (congrArg (fun z => z.2.1) he)
        · exact congrArg (fun z => z.1.2) he)
    simpa only [Finset.card_product, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, S, collisionCount, differenceCount] using hc
  have hr : ((collisionCount r v : ℕ) : ℝ) * (Fintype.card κ : ℝ) ^ s ≤
      ((differenceCount (configurationFrequency r s v u) 0 : ℕ) : ℝ) := by
    exact_mod_cast hn
  simpa only [mul_comm] using hr

/-- A quantitative bound on the small convexity coefficient. -/
theorem one_add_half_inverse_pow_le_two {n : ℕ} (hn : 1 ≤ n) :
    (1 + 1 / (2 * (n : ℝ))) ^ n ≤ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let t : ℝ := 1 / (2 * n)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht2 : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have hnt : (n : ℝ) * t = 1 / 2 := by dsimp [t]; field_simp
  have hb := one_add_mul_le_pow (a := -t) (by linarith : -2 ≤ -t) n
  have hy : (1 / 2 : ℝ) ≤ (1 - t) ^ n := by
    simp only [mul_neg, hnt, ← sub_eq_add_neg] at hb
    linarith
  have hx : 0 ≤ (1 + t) ^ n := by positivity
  have hp : (1 + t) ^ n * (1 - t) ^ n ≤ 1 := by
    rw [← mul_pow]
    calc
      _ ≤ (1 : ℝ) ^ n := by
        apply pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith))
        nlinarith [sq_nonneg t]
      _ = 1 := one_pow n
  have hh := mul_le_mul_of_nonneg_left hy hx
  change (1 + t) ^ n ≤ 2
  nlinarith

/-- Weighted two-term Holder keeps the endpoint contribution separate
from the complete original sum. -/
theorem add_one_power_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (a + 1) ^ n ≤ (1 + 1 / b) ^ (n - 1) * (a ^ n + b ^ (n - 1)) := by
  have h := VinogradovMomentReduction.weighted_power_bound (Finset.univ : Finset (Fin 2))
    ![1, 1 / b] ![a, b] (by intro i hi; fin_cases i <;> simp [hb.le])
    (by intro i hi; fin_cases i <;> simp [ha, hb.le]) hn
  have he : (1 / b) * b ^ n = b ^ (n - 1) := by
    rw [show b ^ n = b * b ^ (n - 1) by rw [← pow_succ', Nat.sub_add_cancel hn]]
    field_simp
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, one_div_mul_cancel hb.ne', he] using h

/-- Scalar absorption of a single endpoint using the actual diagonal
reserve. The parameters are explicit and independent of frequencies. -/
theorem endpoint_absorption {s : ℕ} (hs : 1 ≤ s) {A B E : ℝ}
    (hA : 0 ≤ A) (hdiag : (4 * (s : ℝ)) ^ (2 * s) * B ≤ A)
    (hE : E ≤ (1 + 1 / (4 * (s : ℝ))) ^ (2 * s - 1) *
      (A + (4 * (s : ℝ)) ^ (2 * s - 1) * B)) : E ≤ 2 * A := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hb : (0 : ℝ) < 4 * s := by linarith
  have hcost : (1 + 1 / (4 * (s : ℝ))) ^ (2 * s) ≤ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
      one_add_half_inverse_pow_le_two (n := 2 * s) (by omega)
  have hd : (4 * (s : ℝ)) ^ (2 * s - 1) * B ≤ (1 / (4 * (s : ℝ))) * A := by
    apply (mul_le_mul_iff_of_pos_left hb).mp
    simpa only [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * s),
      mul_one_div_cancel hb.ne', one_mul] using hdiag
  calc
    E ≤ (1 + 1 / (4 * (s : ℝ))) ^ (2 * s - 1) *
        (A + (1 / (4 * (s : ℝ))) * A) :=
      hE.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hd) (by positivity))
    _ = (1 + 1 / (4 * (s : ℝ))) ^ (2 * s) * A := by
      rw [show (1 + 1 / (4 * (s : ℝ))) ^ (2 * s) =
        (1 + 1 / (4 * (s : ℝ))) ^ (2 * s - 1) * (1 + 1 / (4 * (s : ℝ))) by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * s)]]
      ring
    _ ≤ 2 * A := mul_le_mul_of_nonneg_right hcost hA

/-- The final positive interval entry is one literal unit Fourier atom. -/
theorem polynomial_succ {a : Type*} [Fintype a] (N : ℕ) (u : ℕ → a → ℤ)
    (theta : UnitAddTorus a) :
    polynomial (fun x : Fin (N + 1) => u (x.val + 1)) (fun _ => 1) theta =
      polynomial (fun x : Fin N => u (x.val + 1)) (fun _ => 1) theta +
        mFourier (u (N + 1)) theta := by
  simp only [polynomial, one_mul, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

/-- The one-endpoint allowance is obtained from the complete original
mixed integral before using its diagonal reserve. -/
theorem mixedMoment_succ_allowance {ι a : Type*} [Fintype ι] [Fintype a]
    {s : ℕ} (hs : 1 ≤ s) (r N : ℕ) (v : ι → a → ℤ) (u : ℕ → a → ℤ) :
    mixedMoment r s v (fun x : Fin (N + 1) => u (x.val + 1)) ≤
      (1 + 1 / (4 * (s : ℝ))) ^ (2 * s - 1) *
        (mixedMoment r s v (fun x : Fin N => u (x.val + 1)) +
          (4 * (s : ℝ)) ^ (2 * s - 1) * moment r v) := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hb : (0 : ℝ) < 4 * s := by linarith
  let W (theta : UnitAddTorus a) := ‖polynomial v (fun _ => 1) theta‖ ^ (2 * r)
  let f (theta : UnitAddTorus a) := polynomial (fun x : Fin N => u (x.val + 1)) (fun _ => 1) theta
  let C : ℝ := (1 + 1 / (4 * (s : ℝ))) ^ (2 * s - 1)
  let B : ℝ := (4 * (s : ℝ)) ^ (2 * s - 1)
  have hW : Continuous W := (continuous_polynomial _ _).norm.pow _
  have hf : Continuous f := continuous_polynomial _ _
  have hiW : Integrable W := hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun theta => W theta * ‖f theta‖ ^ (2 * s)) :=
    (hW.mul (hf.norm.pow _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (theta : UnitAddTorus a) :
      W theta * ‖polynomial (fun x : Fin (N + 1) => u (x.val + 1)) (fun _ => 1) theta‖ ^ (2 * s) ≤
        C * (W theta * ‖f theta‖ ^ (2 * s) + B * W theta) := by
    have hn : ‖polynomial (fun x : Fin (N + 1) => u (x.val + 1)) (fun _ => 1) theta‖ ≤
        ‖f theta‖ + 1 := by
      rw [polynomial_succ]
      simpa only [f, norm_mFourier_apply] using norm_add_le
        (polynomial (fun x : Fin N => u (x.val + 1)) (fun _ => 1) theta)
        (mFourier (u (N + 1)) theta)
    have hp := (pow_le_pow_left₀ (norm_nonneg _) hn (2 * s)).trans
      (add_one_power_le (by omega : 1 ≤ 2 * s) (norm_nonneg (f theta)) hb)
    have he := mul_le_mul_of_nonneg_left hp (show 0 ≤ W theta by dsimp [W]; positivity)
    exact he.trans_eq (by dsimp [C, B]; ring)
  have he := integral_mono
    ((hW.mul ((continuous_polynomial _ _).norm.pow (2 * s))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((hi.add (hiW.const_mul B)).const_mul C) hpoint
  dsimp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at he
  rw [integral_const_mul, integral_add hi (hiW.const_mul B), integral_const_mul] at he
  simpa only [W, f, C, B, mixedMoment, moment, polynomial, one_mul] using he

/-- A single additional tail endpoint costs at most two once the
retained interval has at least `16*s^2` entries. This is an unconditional
bound on the actual mixed integer-frequency count, with every original
block and tail frequency retained. -/
theorem mixedMoment_succ_le {ι a : Type*} [Fintype ι] [Fintype a]
    {s N : ℕ} (hs : 1 ≤ s) (hN : 16 * s ^ 2 ≤ N)
    (r : ℕ) (v : ι → a → ℤ) (u : ℕ → a → ℤ) :
    mixedMoment r s v (fun x : Fin (N + 1) => u (x.val + 1)) ≤
      2 * mixedMoment r s v (fun x : Fin N => u (x.val + 1)) := by
  have hB : 0 ≤ moment r v := integral_nonneg (fun _ => by positivity)
  have hbase : (4 * (s : ℝ)) ^ 2 ≤ N := by
    have hNR : (16 : ℝ) * (s : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
    nlinarith
  have hpow : (4 * (s : ℝ)) ^ (2 * s) ≤ (N : ℝ) ^ s := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hbase s
  have hdiag := diagonal_tail_le r s v (fun x : Fin N => u (x.val + 1))
  simp only [Fintype.card_fin] at hdiag
  apply endpoint_absorption hs (mixedMoment_nonneg _ _ _ _)
    ((mul_le_mul_of_nonneg_right hpow hB).trans hdiag)
  exact mixedMoment_succ_allowance hs r N v u

/-- Restricting only the tail indices along an injection decreases the
actual mixed count. It does not compare oscillating sums pointwise. -/
theorem mixedMoment_map_le {ι κ τ a : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ] [Fintype a]
    (r s : ℕ) (v : ι → a → ℤ) (u : τ → a → ℤ)
    (f : κ → τ) (hf : Function.Injective f) :
    mixedMoment r s v (fun x => u (f x)) ≤ mixedMoment r s v u := by
  rw [mixedMoment_eq_count, mixedMoment_eq_count]
  let g (z : (Fin r → ι) × (Fin s → κ)) := (z.1, fun j => f (z.2 j))
  have hg : Function.Injective g := by
    intro x y he
    apply Prod.ext
    · exact congrArg (fun z : (Fin r → ι) × (Fin s → τ) => z.1) he
    · funext j
      exact hf (congrArg (fun z : (Fin r → ι) × (Fin s → τ) => z.2 j) he)
  exact_mod_cast VinogradovResidueMoment.differenceCount_map_le g hg
    (configurationFrequency r s v u) 0

end
end RiemannGaussian.VinogradovEndpointDeletion
