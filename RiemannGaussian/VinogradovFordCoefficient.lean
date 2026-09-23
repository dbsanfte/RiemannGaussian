/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordIteration
import RiemannGaussian.VinogradovInitialExceptional
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The numerical coefficient in Ford's mixed iteration

The shrinking-tuple recursion retains the exact factorial cost and the
prime/quotient cancellation. A uniform supersolution bounds its numerical
coefficient by the coefficient in Ford's original Lemma 3.4. The source
moment's diagonal forces its exponent to be at least its moment order;
this fact supplies the reserve in the width-exponent supersolution.
-/

namespace RiemannGaussian.VinogradovFordCoefficient
noncomputable section
open scoped BigOperators
open Filter VinogradovMeanValue VinogradovFordScales VinogradovFordIteration

/-- A global power bound for the literal moment cannot have exponent
below the full diagonal tuple count. No extra source hypothesis is added. -/
theorem source_exponent_ge {s k : ℕ} {C lambda : ℝ}
    (hsource : ∀ N : ℕ, 1 ≤ N → meanValue s k N ≤ C * (N : ℝ) ^ lambda) :
    (s : ℝ) ≤ lambda := by
  by_contra h
  have hgap : 0 < (s : ℝ) - lambda := by linarith
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ ((s : ℝ) - lambda)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN, hlarge⟩ :=
    ((eventually_ge_atTop 1).and (ht.eventually (eventually_gt_atTop C))).exists
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdiag : (N : ℝ) ^ s ≤ meanValue s k N := by
    simpa only [meanValue, Fintype.card_fin] using
      VinogradovInitialExceptional.diagonal_le_moment s
        (fun n : Fin N => monomialFrequency k (n.val + 1))
  have hsmall : (N : ℝ) ^ ((s : ℝ) - lambda) ≤ C := by
    rw [Real.rpow_sub hN0, Real.rpow_natCast]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)).mpr (hdiag.trans (hsource N hN))
  linarith

/-- An elementary factorial reserve, proved for every degree in Ford's range. -/
theorem factorial_reserve {k : ℕ} (hk : 26 ≤ k) :
    1024 * k.factorial ≤ k ^ (k - 3) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc
      1024 * (k + 1).factorial = (k + 1) * (1024 * k.factorial) := by
        rw [Nat.factorial_succ]
        ring
      _ ≤ (k + 1) * k ^ (k - 3) := Nat.mul_le_mul_left _ ih
      _ ≤ (k + 1) * (k + 1) ^ (k - 3) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (k + 1) ^ (k + 1 - 3) := by
        rw [show k + 1 - 3 = (k - 3) + 1 by omega, pow_succ]
        ring

/-- The two retained factorials leave a factor 256 below k to the k. -/
theorem packet_factor_bound {k d m : ℕ} (hk : 26 ≤ k) (hdm : d + m = k) :
    256 * ((4 * k ^ 3 * d.factorial * m.factorial : ℕ) : ℝ) ≤ (k : ℝ) ^ k := by
  have hfac : d.factorial * m.factorial ≤ k.factorial := by
    rw [← hdm]
    exact Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add d m)
  have h : 256 * (4 * k ^ 3 * d.factorial * m.factorial) ≤ k ^ k := by
    calc
      _ = k ^ 3 * (1024 * (d.factorial * m.factorial)) := by ring
      _ ≤ k ^ 3 * (1024 * k.factorial) := by gcongr
      _ ≤ k ^ 3 * k ^ (k - 3) := Nat.mul_le_mul_left _ (factorial_reserve hk)
      _ = k ^ k := by rw [← pow_add, show 3 + (k - 3) = k by omega]
  exact_mod_cast h

/-- The packet-width exponent used to dominate every intermediate coefficient. -/
def widthAllowance (k d s : ℕ) : ℝ :=
  2 * (s : ℝ) + ((k : ℝ) ^ 2 - k + (d : ℝ) ^ 2 - d) / 2 + 2

/-- The explicit width allowance is nonnegative at every depth. -/
theorem widthAllowance_nonneg (k d s : ℕ) : 0 ≤ widthAllowance k d s := by
  have hn (a : ℕ) : 0 ≤ (a : ℝ) ^ 2 - a := by
    cases a with
    | zero => norm_num
    | succ a => push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) a, sq_nonneg (a : ℝ)]
  unfold widthAllowance
  linarith [hn k, hn d, Nat.cast_nonneg (α := ℝ) s]

/-- The source's diagonal reserve pays the full next width exponent,
including the nonconstant shrinking-tuple Holder exponent. -/
theorem width_step {k d r s : ℕ} {delta : ℝ}
    (hds : d + 1 ≤ 2 * s) (hdr : d + 1 ≤ r) (hr : r ≤ k) (hd : d + 4 ≤ k)
    (hlambda : (s : ℝ) ≤ sourceExponent k s delta) :
    (primeGap k (d + 1) r s delta + widthAllowance k (d + 1) s) *
      (((k : ℝ) - d) / (2 * ((k : ℝ) - d - 1))) ≤ widthAllowance k d s := by
  have hdrR : (d : ℝ) + 1 ≤ r := by exact_mod_cast hdr
  have hrR : (r : ℝ) ≤ k := by exact_mod_cast hr
  have hdR : (d : ℝ) + 4 ≤ k := by exact_mod_cast hd
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hmain : 0 ≤ ((k : ℝ) - d) * sourceExponent k s delta - 4 * s := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - d - 4 by linarith) hsR,
      mul_nonneg (show 0 ≤ (k : ℝ) - d by linarith) (sub_nonneg.mpr hlambda)]
  have hdepth : 0 ≤ (d : ℝ) * k * ((k : ℝ) - d - 3) :=
    mul_nonneg (by positivity) (by linarith)
  have hrange : 0 ≤ ((k : ℝ) - d) * ((k : ℝ) - r) *
      ((k : ℝ) + r - 2 * d - 3) := by
    apply mul_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · linarith
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (show 0 < 2 * ((k : ℝ) - d - 1) by linarith)).mpr
  rw [primeGap_eq hds hdr]
  unfold widthAllowance sourceExponent at *
  push_cast at *
  nlinarith [sq_nonneg (d : ℝ)]

/-- The binary constants fit the degree-power reserve uniformly over
all active tuple orders at least four. -/
theorem binary_budget {k m : ℝ} (hm : 3 ≤ m) (hkm : m + 1 ≤ k) :
    m + 2 - 8 * ((m + 1) / (2 * m)) ≤
      2 * (k * (2 - 3 * ((m + 1) / (2 * m)))) := by
  have hm0 : 0 < m := by linarith
  have hn : 0 ≤ (k - m - 1) * (m - 3) := mul_nonneg (by linarith) (by linarith)
  have he : 2 * m *
      (2 * (k * (2 - 3 * ((m + 1) / (2 * m)))) -
        (m + 2 - 8 * ((m + 1) / (2 * m)))) =
      2 * (k - m - 1) * (m - 3) + 2 := by field_simp; ring
  nlinarith

/-- The full factorial and binary coefficient fits the invariant k^(2k).
The factor 256 is the explicit factorial reserve, not an asymptotic input. -/
theorem polynomial_step {k m A : ℝ} (hm : 3 ≤ m) (hkm : m + 1 ≤ k)
    (hA : 0 ≤ A) (hfactor : 256 * A ≤ k ^ k) :
    2 ^ (m + 1) * (2 * (A * k ^ (2 * k)) ^ ((m + 1) / (2 * m))) ≤ k ^ (2 * k) := by
  let alpha : ℝ := (m + 1) / (2 * m)
  have hm0 : 0 < m := by linarith
  have hk : 4 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have ha : 0 ≤ alpha := by dsimp [alpha]; positivity
  have ha23 : alpha ≤ 2 / 3 := by
    dsimp [alpha]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hg : 0 ≤ k * (2 - 3 * alpha) := mul_nonneg hk0.le (by linarith)
  have hA' : A ≤ (2 : ℝ) ^ (-8 : ℝ) * k ^ k := by
    norm_num at ⊢
    linarith
  have hinside : A * k ^ (2 * k) ≤ (2 : ℝ) ^ (-8 : ℝ) * k ^ (3 * k) := by
    calc
      _ ≤ ((2 : ℝ) ^ (-8 : ℝ) * k ^ k) * k ^ (2 * k) := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hk0]; congr 2; ring
  have hb : (2 : ℝ) ^ (m + 2 - 8 * alpha) ≤ k ^ (k * (2 - 3 * alpha)) := by
    calc
      _ ≤ (2 : ℝ) ^ (2 * (k * (2 - 3 * alpha))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (binary_budget hm hkm)
      _ = (4 : ℝ) ^ (k * (2 - 3 * alpha)) := by rw [Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hk hg
  calc
    _ ≤ 2 ^ (m + 1) * (2 * ((2 : ℝ) ^ (-8 : ℝ) * k ^ (3 * k)) ^ alpha) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hinside ha) (by norm_num))
        (by positivity)
    _ = (2 : ℝ) ^ (m + 2 - 8 * alpha) * k ^ (3 * k * alpha) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hk0.le]
      rw [show m + 2 - 8 * alpha = (m + 1) + 1 + (-8 * alpha) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_one]
      simp only [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    _ ≤ k ^ (k * (2 - 3 * alpha)) * k ^ (3 * k * alpha) := by gcongr
    _ = _ := by rw [← Real.rpow_add hk0]; congr 1; ring


/-- Every intermediate coefficient is bounded by a physical-endpoint
independent supersolution with Ford's width exponent. -/
theorem coefficient_bound {k b s r : ℕ} {delta eta : ℝ}
    (hk : 26 ≤ k) (hb : 3 ≤ b) (hs : k ≤ s) (hr : r ≤ k) (hstop : k - b ≤ r)
    (heta : 1 ≤ eta) (hlambda : (s : ℝ) ≤ sourceExponent k s delta)
    (n d : ℕ) (hkd : d + (b + n) = k) :
    coefficient k b s r delta eta d n ≤
      (k : ℝ) ^ (2 * k) * eta ^ widthAllowance k d s := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have heta0 : 0 < eta := by linarith
  have hcap : 1 ≤ (k : ℝ) ^ (2 * k) := one_le_pow₀ hk1
  induction n generalizing d with
  | zero =>
    simpa only [coefficient] using
      one_le_mul_of_one_le_of_one_le hcap (Real.one_le_rpow heta (widthAllowance_nonneg _ _ _))
  | succ n ih =>
    have hm : 3 ≤ b + n := by omega
    have hdim : d + 1 + (b + n) = k := by omega
    have hfactor := packet_factor_bound hk hdim
    have hnext := ih (d + 1) (by omega)
    let A : ℝ := ((4 * k ^ 3 * (d + 1).factorial * (b + n).factorial : ℕ) : ℝ)
    let alpha : ℝ := (((b + n : ℕ) : ℝ) + 1) / (2 * ((b + n : ℕ) : ℝ))
    let gap : ℝ := primeGap k (d + 1) r s delta
    have ha : 0 ≤ alpha := by dsimp [alpha]; positivity
    have hA : 0 ≤ A := Nat.cast_nonneg _
    have hpoly : (2 : ℝ) ^ (b + n + 1) *
        (2 * (A * (k : ℝ) ^ (2 * k)) ^ alpha) ≤ (k : ℝ) ^ (2 * k) := by
      have hp := polynomial_step (k := (k : ℝ)) (m := ((b + n : ℕ) : ℝ))
        (by exact_mod_cast hm) (by exact_mod_cast (show b + n + 1 ≤ k by omega))
        hA (by simpa only [Real.rpow_natCast] using hfactor)
      simpa only [← Real.rpow_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        Nat.cast_ofNat, A, alpha] using hp
    have hwidth : (gap + widthAllowance k (d + 1) s) * alpha ≤ widthAllowance k d s := by
      have hw := width_step (k := k) (d := d) (r := r) (s := s)
        (by omega) (by omega) hr (by omega) hlambda
      have he : (k : ℝ) - d = ((b + n : ℕ) : ℝ) + 1 := by
        have he' : k = d + (b + n) + 1 := by omega
        rw [he']
        push_cast
        ring
      simpa only [he, add_sub_cancel_right, gap, alpha] using hw
    have hoff : (2 : ℝ) ^ (b + n + 1) *
        (2 * (A * coefficient k b s r delta eta (d + 1) n * eta ^ gap) ^ alpha) ≤
          (k : ℝ) ^ (2 * k) * eta ^ widthAllowance k d s := by
      have hi : A * coefficient k b s r delta eta (d + 1) n * eta ^ gap ≤
          (A * (k : ℝ) ^ (2 * k)) * eta ^ (gap + widthAllowance k (d + 1) s) := by
        calc
          _ ≤ A * ((k : ℝ) ^ (2 * k) * eta ^ widthAllowance k (d + 1) s) * eta ^ gap := by
            gcongr
          _ = _ := by rw [Real.rpow_add heta0]; ring
      calc
        _ ≤ (2 : ℝ) ^ (b + n + 1) *
            (2 * ((A * (k : ℝ) ^ (2 * k)) *
              eta ^ (gap + widthAllowance k (d + 1) s)) ^ alpha) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow
              (mul_nonneg (mul_nonneg hA (coefficient_nonneg _ _ _ _ _ _ _ _))
                (Real.rpow_nonneg heta0.le _)) hi ha) (by norm_num)
        _ = ((2 : ℝ) ^ (b + n + 1) * (2 * (A * (k : ℝ) ^ (2 * k)) ^ alpha)) *
            eta ^ ((gap + widthAllowance k (d + 1) s) * alpha) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul heta0.le]
          ring
        _ ≤ _ := mul_le_mul hpoly (Real.rpow_le_rpow_of_exponent_le heta hwidth)
          (Real.rpow_nonneg heta0.le _) (by positivity)
    rw [coefficient, mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 ^ (b + n + 1))]
    apply max_le _ hoff
    have hdiag : (2 : ℝ) ^ (b + n + 1) * (k : ℝ) ^ (b + n + 1) ≤ (k : ℝ) ^ (2 * k) := by
      calc
        _ = (2 * (k : ℝ)) ^ (b + n + 1) := by rw [mul_pow]
        _ ≤ ((k : ℝ) ^ 2) ^ (b + n + 1) := by
          apply pow_le_pow_left₀ (by positivity)
          have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
          nlinarith
        _ = (k : ℝ) ^ (2 * (b + n + 1)) := by rw [pow_mul]
        _ ≤ _ := pow_le_pow_right₀ hk1 (by omega)
    exact hdiag.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow heta (widthAllowance_nonneg _ _ _)))

/-- Initial conditioning plus the entire backward width allowance fits
the published exponent 4s+k squared. -/
theorem initial_width_bound {k r s : ℕ} {delta : ℝ} (hk : 2 ≤ k) (hr : r ≤ k)
    (hlambda : 0 ≤ sourceExponent k s delta) :
    widthAllowance k 0 s + primeGap k 0 r s delta ≤ (4 * s + k ^ 2 : ℕ) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (r : ℝ) ≤ k := by exact_mod_cast hr
  have hprod : 0 ≤ ((k : ℝ) - r) * ((k : ℝ) + r - 1) :=
    mul_nonneg (by linarith) (by linarith [Nat.cast_nonneg (α := ℝ) r])
  rw [primeGap_eq (by omega) (by omega)]
  unfold widthAllowance sourceExponent at *
  push_cast at *
  nlinarith

/-- The complete numerical allowance in the actual original moment
bound is at most Ford's published coefficient, with no enlarged constant. -/
theorem full_coefficient_bound {k b s r : ℕ} {delta eta : ℝ}
    (hk : 26 ≤ k) (hb : 3 ≤ b) (hs : k ≤ s) (hr : r ≤ k) (hstop : k - b ≤ r)
    (heta : 1 ≤ eta) (hlambda : (s : ℝ) ≤ sourceExponent k s delta)
    (n : ℕ) (hkn : b + n = k) :
    ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
      coefficient k b s r delta eta 0 n * eta ^ primeGap k 0 r s delta ≤
        (k : ℝ) ^ (3 * k) * eta ^ (4 * s + k ^ 2) := by
  have heta0 : 0 < eta := by linarith
  have hc := coefficient_bound hk hb hs hr hstop heta hlambda n 0 (by omega)
  have ha : ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) ≤ (k : ℝ) ^ k := by
    have hh := packet_factor_bound (d := 0) (m := k) hk (by omega)
    simp only [Nat.factorial_zero, mul_one] at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) (4 * k ^ 3 * k.factorial)]
  calc
    _ ≤ (k : ℝ) ^ k * ((k : ℝ) ^ (2 * k) * eta ^ widthAllowance k 0 s) *
        eta ^ primeGap k 0 r s delta := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg heta0.le _)
      exact mul_le_mul ha hc (coefficient_nonneg _ _ _ _ _ _ _ _) (by positivity)
    _ = (k : ℝ) ^ (3 * k) * eta ^ (widthAllowance k 0 s + primeGap k 0 r s delta) := by
      rw [Real.rpow_add heta0, show 3 * k = k + 2 * k by omega, pow_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le heta
        (initial_width_bound (by omega) hr ((Nat.cast_nonneg s).trans hlambda))

end
end RiemannGaussian.VinogradovFordCoefficient
