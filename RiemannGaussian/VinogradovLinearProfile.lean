/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovConstantPreservation

/-!
# A uniform explicit cost for every finite conditioning profile

The Holder root gives an invariant profile multiplier ceiling
(k!)^2*(1+2*selectionCost)^(2/u), bounded by (2ku)^(7k). This ceiling is
independent of the iteration count. An explicit depth budget now gives
cutoff (k+d)^n for the actual conditioned moments. The original existential
interface is retained. Prime-packet and global moment costs are separate.
-/

namespace RiemannGaussian.VinogradovLinearProfile
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap
open VinogradovDefectRemainder
open VinogradovConstantPreservation

/-- The profile constant update preserves one explicit interval, independent
of how many times the actual conditioning profile is iterated. -/
theorem profile_constant_step_le {F E B u : ℝ} (hF : 1 ≤ F) (hE : 0 ≤ E)
    (hB : 1 ≤ B) (hu : 2 ≤ u) (hcap : B ≤ (F * (1 + 2 * E)) ^ 2) :
    F * (1 + 2 * E * B) ^ (1 / u) ≤ (F * (1 + 2 * E)) ^ 2 := by
  let Q := 1 + 2 * E
  have hQ : 1 ≤ Q := by dsimp only [Q]; linarith
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hinput : 1 + 2 * E * B ≤ (F * Q ^ 2) ^ 2 := by
    calc
      _ ≤ Q * B := by dsimp only [Q]; nlinarith only [hB]
      _ ≤ Q * (F * Q) ^ 2 := mul_le_mul_of_nonneg_left hcap hQ0
      _ = F ^ 2 * Q ^ 3 := by ring
      _ ≤ F ^ 2 * Q ^ 4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hQ (by norm_num : 3 ≤ 4)) (sq_nonneg F)
      _ = _ := by ring
  have hbase : 1 ≤ F * Q ^ 2 := by
    calc
      _ ≤ F := hF
      _ ≤ _ := le_mul_of_one_le_right hF0 (one_le_pow₀ hQ)
  have hu0 : 0 < u := by linarith only [hu]
  have hroot := Real.rpow_le_rpow (by positivity) hinput (one_div_pos.mpr hu0).le
  have hroot' : (1 + 2 * E * B) ^ (1 / u) ≤ F * Q ^ 2 := by
    apply hroot.trans
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hbase)]
    calc
      _ ≤ (F * Q ^ 2) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hbase
        norm_num only [Nat.cast_ofNat, mul_one_div]
        exact (div_le_one hu0).mpr hu
      _ = _ := Real.rpow_one _
  calc
    _ ≤ F * (F * Q ^ 2) := mul_le_mul_of_nonneg_left hroot' hF0
    _ = _ := by dsimp only [Q]; ring

/-- Retaining the actual Holder root gives a smaller explicit invariant ceiling
for the profile constant, independent of the number of conditioning steps. -/
theorem profile_constant_step_sharp {F E B u : ℝ} (hF : 1 ≤ F) (hE : 0 ≤ E)
    (hB : 1 ≤ B) (hu : 2 ≤ u) (hcap : B ≤ F ^ 2 * (1 + 2 * E) ^ (2 / u)) :
    F * (1 + 2 * E * B) ^ (1 / u) ≤ F ^ 2 * (1 + 2 * E) ^ (2 / u) := by
  let Q := 1 + 2 * E
  have hQ : 1 ≤ Q := by dsimp only [Q]; linarith
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hu0 : 0 < u := by linarith only [hu]
  let theta := 1 / u
  have ht : 0 ≤ theta := (one_div_pos.mpr hu0).le
  have hthalf : theta ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hu
  have hinput : 1 + 2 * E * B ≤ Q * (F ^ 2 * Q ^ (2 * theta)) := by
    have htwo : 2 / u = 2 * theta := by dsimp only [theta]; ring
    calc
      _ ≤ Q * B := by dsimp only [Q]; nlinarith only [hB]
      _ ≤ Q * (F ^ 2 * Q ^ (2 * theta)) := by
        apply mul_le_mul_of_nonneg_left _ hQ0.le
        simpa only [htwo] using hcap
  have heF : 1 + 2 * theta ≤ 2 := by linarith only [hthalf]
  have heQ : theta + 2 * theta * theta ≤ 2 * theta := by
    nlinarith only [mul_le_mul_of_nonneg_right hthalf ht]
  calc
    _ ≤ F * (Q * (F ^ 2 * Q ^ (2 * theta))) ^ theta :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hinput ht) hF0.le
    _ = F ^ (1 + 2 * theta) * Q ^ (theta + 2 * theta * theta) := by
      rw [Real.mul_rpow hQ0.le (by positivity), Real.mul_rpow (sq_nonneg F) (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul hF0.le, ← Real.rpow_mul hQ0.le]
      rw [Real.rpow_add hF0, Real.rpow_add hQ0, Real.rpow_one]
      ring
    _ ≤ F ^ (2 : ℝ) * Q ^ (2 * theta) := mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hF heF)
      (Real.rpow_le_rpow_of_exponent_le hQ heQ) (by positivity) (by positivity)
    _ = _ := by dsimp only [Q, theta]; rw [Real.rpow_two]; congr 2; ring

/-- Before any stopping rule, the affine profile cannot decrease faster
than one full defect payment at each conditioning step. -/
theorem affineProfile_lower_bound {r c B : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (n : ℕ) :
    -(n : ℝ) * c ≤ affineProfile r c B n := by
  induction n with
  | zero => simpa only [affineProfile, Nat.cast_zero, neg_zero, zero_mul] using hB
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_left ih hr0
    have hrc := mul_le_mul_of_nonneg_right hr1 (mul_nonneg (Nat.cast_nonneg n) hc)
    simp only [affineProfile, Nat.cast_add, Nat.cast_one]
    nlinarith only [h, hrc]

/-- An explicit descendant-depth budget controls the original conditioned
energies, with the same depth-independent multiplier ceiling. -/
theorem bounded_depth_profile_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 ≤ defect) (n d : ℕ) (hdk : k ≤ d)
    (hdepth : ∀ j < n, -(d : ℝ) / 2 ≤ defect + (k : ℝ) *
      affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) j) :
    ∃ B : ℝ, 1 ≤ B ∧
      B ≤ (k.factorial : ℝ) ^ 2 * (1 + 2 * selectionCost k u) ^ (2 / (u : ℝ)) ∧
      ∀ C : ℝ, 1 ≤ C →
      ∀ (lam : ℝ) (N₀ : ℕ),
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ ((k + d) ^ n * b) ≤ X → N₀ ≤ X / p ^ ((k + d) ^ n * b) + 1 →
      iterationConstant k u ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        (C * B) * (p : ℝ) ^ (delta * a +
          affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) n * b) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hr0 : (0 : ℝ) ≤ (k : ℝ) / u := by positivity
  have hr1 : (k : ℝ) / u ≤ 1 := (div_le_one hu0).mpr (by exact_mod_cast hu)
  have hf : 0 ≤ 1 - 1 / (u : ℝ) := by
    have ht : 1 / (u : ℝ) ≤ 1 := (div_le_one hu0).mpr (by exact_mod_cast (by omega : 1 ≤ u))
    linarith
  have hc : 0 ≤ (1 - 1 / (u : ℝ)) * defect := mul_nonneg hf hdefect0
  have hceiling : 1 ≤ (k.factorial : ℝ) ^ 2 * (1 + 2 * selectionCost k u) ^ (2 / (u : ℝ)) := by
    have hF : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hE : 0 ≤ selectionCost k u := by unfold selectionCost; positivity
    calc
      1 ≤ (k.factorial : ℝ) ^ 2 := one_le_pow₀ hF
      _ ≤ _ := le_mul_of_one_le_right (sq_nonneg _)
        (Real.one_le_rpow (by linarith) (by positivity))
  induction n with
  | zero =>
    refine ⟨1, le_rfl, hceiling, ?_⟩
    intro C hC lam N₀ hdefect hbudget
    dsimp only
    intro p a b xi eta X inst hab hX hN hp heta colourA colourB
    have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
    have hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam := by linarith
    simp only [pow_zero, one_mul] at hX hN
    obtain ⟨hXa, hNa⟩ := quotient_budget_mono hp0 hab.le hX hN
    have he := initial_profile (xi := xi) (eta := eta) hk hu hab.le
      ((Nat.pow_pos hp0).trans_le hX) hC hlam
      (hbudget p a X hp0 hXa hNa) (hbudget p b X hp0 hX hN) colourA colourB
    simpa only [affineProfile, mul_one] using he
  | succ n ih =>
    obtain ⟨B, hB, hBcap, hprev⟩ := ih (fun j hj => hdepth j (by omega))
    let T := (k + d) ^ n
    have hT : 1 ≤ T := Nat.one_le_pow n (k + d) (by omega)
    let beta := affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) n
    have hbeta : beta ≤ (k : ℝ) * u := affineProfile_le hr0 hr1 hc (by positivity) n
    have hddepth : -(d : ℝ) / 2 ≤ defect + (k : ℝ) * beta := hdepth n (by omega)
    let Bnext : ℝ := max 1 ((k.factorial : ℝ) *
      (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ)))
    have hBnext : Bnext ≤ (k.factorial : ℝ) ^ 2 * (1 + 2 * selectionCost k u) ^ (2 / (u : ℝ)) := by
      apply max_le hceiling
      exact profile_constant_step_sharp (by exact_mod_cast Nat.factorial_pos k)
        (by unfold selectionCost; positivity) hB (by exact_mod_cast (show 2 ≤ u by omega)) hBcap
    refine ⟨Bnext, le_max_left _ _, hBnext, ?_⟩
    clear hBcap hceiling hBnext
    intro C hC lam N₀ hdefect hbudget
    let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
    have hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam := by linarith
    dsimp only
    intro p a b xi eta X inst hab hX hN hp heta colourA colourB
    rw [pow_succ] at hX hN
    have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : p.Prime)).le
    have hXpos : 0 < X := (Nat.pow_pos hp0).trans_le hX
    have hdeepExp : k * b + d * b ≤ (T * (k + d)) * b := by
      have he := Nat.mul_le_mul_right ((k + d) * b) hT
      nlinarith only [he]
    obtain ⟨hXd, hNd⟩ := quotient_budget_mono hp0 hdeepExp hX hN
    obtain ⟨hXb, hNb⟩ := quotient_budget_mono hp0 (by nlinarith only [Nat.mul_le_mul_right b hk] : b ≤ k * b + d * b) hXd hNd
    have hH : 1 ≤ d * b := by
      have hd1 : 1 ≤ d := by omega
      have hb1 : 1 ≤ b := by omega
      exact (Nat.mul_le_mul hd1 hb1)
    have hgap : k * b - b ≤ 2 * (d * b) := by
      have he := Nat.mul_le_mul_right b hdk
      omega
    have hdeep : -(((d * b : ℕ) : ℝ) / 2) ≤ (delta + (k : ℝ) * beta) * b := by
      have hdd : -(d : ℝ) / 2 ≤ delta + (k : ℝ) * beta := by dsimp only [delta]; linarith
      have he := mul_le_mul_of_nonneg_right hdd (Nat.cast_nonneg b)
      push_cast
      nlinarith only [he]
    have hnext : ∀ h < d * b, normalizedLevel p k b (k * b + h) eta X u colourB lam ≤
        (C * B) * (p : ℝ) ^ (delta * b + beta * ((k * b + h : ℕ) : ℝ)) := by
      intro h hh
      apply normalized_level_le_of_all hXpos colourB lam
      intro eta' heta' colourC
      have he : T * (k * b + h) ≤ (T * (k + d)) * b := by
        have hs : k * b + h ≤ (k + d) * b := by nlinarith only [hh]
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left T hs
      obtain ⟨hXnext, hNnext⟩ := quotient_budget_mono hp0 he hX hN
      have hbb : b < k * b + h := by nlinarith only [Nat.mul_le_mul_right b hk, hab]
      exact hprev C hC lam N₀ hdefect hbudget p b (k * b + h) eta eta' X
        hbb hXnext hNnext hp heta' colourB colourC
    have he := conditioned_profile_preserving_constant (xi := xi) hk hu hab hH hgap hXpos hC (by positivity : 0 ≤ C * B)
      hlam hp (hbudget p b X hp0 hXb hNb) (hbudget p (k * b + d * b) X hp0 hXd hNd)
      heta colourA colourB hbeta hdeep hnext
    have hcoef : (VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
        (C + 2 * selectionCost k u * (C * B)) ^ (1 / (u : ℝ)) ≤ C * Bnext := by
      have hQ : 0 ≤ 1 + 2 * selectionCost k u * B := by unfold selectionCost; positivity
      have hfactor : C + 2 * selectionCost k u * (C * B) =
          C * (1 + 2 * selectionCost k u * B) := by ring
      rw [hfactor, mul_assoc, profile_constant_homogeneity (zero_lt_one.trans_le hC) hQ]
      calc
        _ = C * ((VinogradovSignedCongruence.colourFactorial colourA : ℝ) *
            (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ))) := by ring
        _ ≤ C * Bnext := by
          apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
          apply le_trans _ (le_max_right _ _)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast VinogradovCoarseCongruence.colourFactorial_le_factorial colourA
    have he' := he.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
    have hbeta_next : affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) (n + 1) =
        -(1 - 1 / (u : ℝ)) * defect + (k : ℝ) / u * beta := by
      change (k : ℝ) / u * beta - (1 - 1 / (u : ℝ)) * defect = _
      ring
    have hslope : -(1 - 1 / (u : ℝ)) * delta + (k : ℝ) / u * beta ≤
        -(1 - 1 / (u : ℝ)) * defect + (k : ℝ) / u * beta := by
      have hd := mul_le_mul_of_nonneg_left hdefect hf
      change (1 - 1 / (u : ℝ)) * defect ≤ (1 - 1 / (u : ℝ)) * delta at hd
      linarith only [hd]
    have hexp := add_le_add (le_refl (delta * a)) (mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg b))
    change _ ≤ (C * Bnext) * (p : ℝ) ^ (delta * a +
      affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) (n + 1) * b)
    rw [hbeta_next]
    exact he'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 hexp)
      (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans (le_max_left _ _))))

/-- The actual profile iteration has one explicit constant ceiling at every
finite depth, without any dependence of that ceiling on the iteration count. -/
theorem uniform_profile_constant_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 ≤ defect) (n : ℕ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∃ B : ℝ, 1 ≤ B ∧
      B ≤ (k.factorial : ℝ) ^ 2 * (1 + 2 * selectionCost k u) ^ (2 / (u : ℝ)) ∧
      ∀ C : ℝ, 1 ≤ C →
      ∀ (lam : ℝ) (N₀ : ℕ),
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      iterationConstant k u ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        (C * B) * (p : ℝ) ^ (delta * a +
          affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) n * b) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hr0 : (0 : ℝ) ≤ (k : ℝ) / u := by positivity
  have hr1 : (k : ℝ) / u ≤ 1 := (div_le_one hu0).mpr (by exact_mod_cast hu)
  have hc : 0 ≤ (1 - 1 / (u : ℝ)) * defect := by
    have hf : 1 / (u : ℝ) ≤ 1 := (div_le_one hu0).mpr (by exact_mod_cast (by omega : 1 ≤ u))
    exact mul_nonneg (by linarith) hdefect0
  let c := (1 - 1 / (u : ℝ)) * defect
  obtain ⟨d, hd⟩ := exists_nat_ge (max (k : ℝ) (2 * k * n * c))
  have hdk : k ≤ d := by exact_mod_cast (le_max_left _ _).trans hd
  have hdsize : 2 * k * n * c ≤ (d : ℝ) := (le_max_right _ _).trans hd
  have hdepth (j : ℕ) (hj : j < n) : -(d : ℝ) / 2 ≤ defect + (k : ℝ) *
      affineProfile ((k : ℝ) / u) c ((k : ℝ) * u) j := by
    have hlow := affineProfile_lower_bound hr0 hr1 hc (by positivity : 0 ≤ (k : ℝ) * u) j
    have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj.le
    have hprod := mul_le_mul_of_nonneg_right hjR hc
    have hscaled := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg k)
    nlinarith only [hscaled, hdsize, hdefect0,
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg k)]
  obtain ⟨B, hB, hcap, h⟩ := bounded_depth_profile_iteration k u hk hu defect hdefect0 n d hdk hdepth
  exact ⟨(k + d) ^ n, Nat.one_le_pow n (k + d) (by omega), B, hB, hcap, h⟩

/-- The entire profile constant ceiling is bounded by an explicit
power with exponent linear in degree, independent of the profile depth. -/
theorem profile_ceiling_le (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    (k.factorial : ℝ) ^ 2 * (1 + 2 * selectionCost k u) ^ (2 / (u : ℝ)) ≤
      (2 * (k : ℝ) * (u : ℝ)) ^ (7 * k) := by
  let P := (2 * (k * u)).descFactorial k
  let V : ℝ := 2 * (k : ℝ) * (u : ℝ)
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hk.trans hu
  have hu0 : (0 : ℝ) < u := by linarith only [hu2]
  have hkV : k ≤ 2 * (k * u) := by nlinarith only [hk, hu]
  have hP : (1 : ℝ) ≤ P := by
    exact_mod_cast Nat.descFactorial_pos.mpr hkV
  have hV : (3 : ℝ) ≤ V := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp only [V]
    nlinarith only [hkR, hu2, mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr hu2)]
  have hV0 : 0 ≤ V := by linarith only [hV]
  have hpowP : (P : ℝ) ≤ V ^ k := by
    have ht := Nat.descFactorial_le_pow (2 * (k * u)) k
    dsimp only [P, V]
    exact_mod_cast (by simpa only [Nat.mul_assoc] using ht)
  have hfac : (k.factorial : ℝ) ≤ V ^ k := by
    have hf : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    apply hf.trans (pow_le_pow_left₀ (by positivity) _ k)
    dsimp only [V]
    exact_mod_cast (by simpa only [Nat.mul_assoc] using hkV)
  have hE : 1 ≤ selectionCost k u := by
    change 1 ≤ (P : ℝ) ^ (2 * u)
    exact one_le_pow₀ hP
  have hinput : 1 + 2 * selectionCost k u ≤ 3 * (P : ℝ) ^ (2 * u) := by
    change 1 + 2 * selectionCost k u ≤ 3 * selectionCost k u
    linarith only [hE]
  have hroot : (1 + 2 * selectionCost k u) ^ (2 / (u : ℝ)) ≤ 3 * (P : ℝ) ^ 4 := by
    have h := Real.rpow_le_rpow (by unfold selectionCost; positivity) hinput (by positivity : 0 ≤ 2 / (u : ℝ))
    apply h.trans
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    have hp : ((P : ℝ) ^ (2 * u)) ^ (2 / (u : ℝ)) = (P : ℝ) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hP)]
      have he : ((2 * u : ℕ) : ℝ) * (2 / (u : ℝ)) = 4 := by
        push_cast
        field_simp
        norm_num
      rw [he, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    rw [hp]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        ((div_le_one hu0).mpr hu2)
      _ = _ := Real.rpow_one _
  have hVk : (3 : ℝ) ≤ V ^ k := by
    apply hV.trans
    exact le_self_pow₀ (by linarith only [hV] : 1 ≤ V) (by omega : k ≠ 0)
  calc
    _ ≤ (V ^ k) ^ 2 * (3 * (V ^ k) ^ 4) := mul_le_mul
      (pow_le_pow_left₀ (by positivity) hfac 2)
      (hroot.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpowP 4) (by norm_num)))
      (by unfold selectionCost; positivity) (by positivity)
    _ ≤ (V ^ k) ^ 2 * (V ^ k * (V ^ k) ^ 4) := by gcongr
    _ = _ := by dsimp only [V]; ring

/-- The original conditioned energies have a depth-independent explicit
profile multiplier bounded by (2ku)^(7k), with linear source-constant cost. -/
theorem uniform_profile_degree_cost_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 ≤ defect) (n : ℕ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∃ B : ℝ, 1 ≤ B ∧ B ≤ (2 * (k : ℝ) * (u : ℝ)) ^ (7 * k) ∧
      ∀ C : ℝ, 1 ≤ C → ∀ (lam : ℝ) (N₀ : ℕ),
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      iterationConstant k u ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        (C * B) * (p : ℝ) ^ (delta * a +
          affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) n * b) := by
  obtain ⟨T, hT, B, hB, hcap, h⟩ := uniform_profile_constant_iteration k u hk hu defect hdefect0 n
  exact ⟨T, hT, B, hB, hcap.trans (profile_ceiling_le k u hk hu), h⟩

/-- A fixed lower exponent defect gives one finite depth uniformly over all source exponents, homogeneous constants and quotient thresholds. -/
theorem linear_constant_profile_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 ≤ defect) (n : ℕ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∃ B : ℝ, 1 ≤ B ∧ ∀ C : ℝ, 1 ≤ C →
      ∀ (lam : ℝ) (N₀ : ℕ),
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      iterationConstant k u ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        (C * B) * (p : ℝ) ^ (delta * a +
          affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) n * b) := by
  obtain ⟨T, hT, B, hB, _hcap, h⟩ := uniform_profile_degree_cost_iteration k u hk hu defect hdefect0 n
  exact ⟨T, hT, B, hB, h⟩

end
end RiemannGaussian.VinogradovLinearProfile
