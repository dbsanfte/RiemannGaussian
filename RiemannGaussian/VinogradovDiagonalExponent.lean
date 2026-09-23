/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDiagonalMoment

/-!
# An explicit exponent decrement for the actual moment-order step

Keep the selected prime and literal quotient until applying the preceding
homogeneous moment estimate. The resulting exponent decreases the defect
by its exact fraction 1/k. The packet cost is explicit and independent of
the input defect after one stated monotone relaxation.
-/

namespace RiemannGaussian.VinogradovDiagonalExponent
noncomputable section
open scoped BigOperators Classical
open VinogradovMeanValue VinogradovDiagonalMoment

/-- The exact twice-triangular integer identity avoids truncating a real half. -/
theorem twice_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose k 2
  norm_num only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    Nat.factorial_succ, Nat.factorial_zero, mul_one] at h
  simpa only [mul_comm] using h.symm

/-- The total degree of the complete system, expressed using exact natural counts. -/
def degreeWeight (k : ℕ) : ℕ := k + k.choose 2

/-- The exact count exponent at order s with remaining defect delta. -/
def exponent (k s : ℕ) (delta : ℝ) : ℝ := 2 * (s : ℝ) - degreeWeight k + delta

/-- The diagonal conditioning power differs from the input exponent by k^2-delta. -/
theorem power_gap {k : ℕ} (hk : 1 ≤ k) (s : ℕ) (delta : ℝ) :
    ((2 * s + k * (k - 1) / 2 : ℕ) : ℝ) - exponent k s delta =
      (k : ℝ) ^ 2 - delta := by
  have hn : k + 2 * k.choose 2 = k ^ 2 := by
    rw [twice_choose_two]
    have h := Nat.sub_add_cancel hk
    nlinarith
  have hr : (k : ℝ) + 2 * (k.choose 2 : ℝ) = (k : ℝ) ^ 2 := by exact_mod_cast hn
  rw [← Nat.choose_two_right]
  unfold exponent degreeWeight
  push_cast
  linarith

/-- The exact exponent after paying the selected prime. -/
theorem next_exponent {k : ℕ} (hk : 0 < k) (s : ℕ) (delta : ℝ) :
    (k : ℝ) + exponent k s delta + ((k : ℝ) ^ 2 - delta) / k =
      exponent k (s + k) (delta * (1 - 1 / (k : ℝ))) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold exponent
  push_cast
  field_simp
  ring

/-- The prime and quotient powers are bounded together, before replacing
the selected prime by its packet endpoint. -/
theorem diagonal_power_le {k B p P M A : ℕ} (hk : 0 < k)
    (hp : 0 < p) (hP : 0 < P) (hM : 0 < M) (hA : 0 < A)
    (hMP : M ^ k ≤ P) (hpU : p ≤ A * M) {lambda : ℝ} (hgap : lambda ≤ B) :
    (p : ℝ) ^ B * (P : ℝ) ^ k * ((P : ℝ) / p) ^ lambda ≤
      (A : ℝ) ^ ((B : ℝ) - lambda) *
        (P : ℝ) ^ ((k : ℝ) + lambda + ((B : ℝ) - lambda) / k) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hg : 0 ≤ (B : ℝ) - lambda := sub_nonneg.mpr hgap
  have hMP' : (M : ℝ) ^ k ≤ (P : ℝ) := by exact_mod_cast hMP
  have hmroot := Real.rpow_le_rpow (pow_nonneg hMR.le _) hMP' (div_nonneg hg hkR.le)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hMR.le,
    show (k : ℝ) * (((B : ℝ) - lambda) / k) = (B : ℝ) - lambda by field_simp] at hmroot
  have hpU' : (p : ℝ) ≤ (A : ℝ) * M := by exact_mod_cast hpU
  have hprime := Real.rpow_le_rpow hpR.le hpU' hg
  rw [Real.mul_rpow hAR.le hMR.le] at hprime
  have hbound := hprime.trans
    (mul_le_mul_of_nonneg_left hmroot (Real.rpow_nonneg hAR.le _))
  rw [Real.div_rpow hPR.le hpR.le]
  calc
    _ = ((p : ℝ) ^ B / (p : ℝ) ^ lambda) * ((P : ℝ) ^ k * (P : ℝ) ^ lambda) := by ring
    _ = (p : ℝ) ^ ((B : ℝ) - lambda) * (P : ℝ) ^ ((k : ℝ) + lambda) := by
      rw [← Real.rpow_natCast p B, ← Real.rpow_sub hpR,
        ← Real.rpow_natCast P k, ← Real.rpow_add hPR]
    _ ≤ ((A : ℝ) ^ ((B : ℝ) - lambda) *
        (P : ℝ) ^ (((B : ℝ) - lambda) / k)) * (P : ℝ) ^ ((k : ℝ) + lambda) :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hPR.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hPR]
      congr 2
      ring

/-- Every actual packet supplies a quantitative moment step with its
literal cardinality and width, after the prime and quotient powers cancel. -/
theorem moment_step_of_packet_bound {k s P M A : ℕ}
    (hk : 2 ≤ k) (hP : 4 * k ^ 4 ≤ P) (hM : k ≤ M) (hA : 1 ≤ A)
    (π : Finset ℕ) (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ A * M)
    (hbudget : P ^ (2 * k.choose 2) < ∏ p ∈ π, p)
    (hroot : P < (M + 1) ^ k) (hMP : M ^ k ≤ P)
    (hs : 1 ≤ s) (hQ : 16 * s ^ 2 * (A * M) ≤ P)
    {C lambda : ℝ} (hC : 0 ≤ C) (hlambda : 0 ≤ lambda)
    (hgap : lambda ≤ (2 * s + k * (k - 1) / 2 : ℕ))
    (hJ : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ C * (X : ℝ) ^ lambda) :
    meanValue (s + k) k P ≤
      ((4 * π.card * k.factorial : ℕ) : ℝ) * C *
        (A : ℝ) ^ (((2 * s + k * (k - 1) / 2 : ℕ) : ℝ) - lambda) *
          (P : ℝ) ^ ((k : ℝ) + lambda +
            (((2 * s + k * (k - 1) / 2 : ℕ) : ℝ) - lambda) / k) := by
  obtain ⟨p, hp, hpM, hpU, hcount⟩ :=
    exists_diagonal_moment_step_of_packet hk hP hM π hπ hbudget hroot hs hQ
  have hfloor : 16 * s ^ 2 ≤ P / p := (Nat.le_div_iff_mul_le hp.pos).mpr
    ((Nat.mul_le_mul_left (16 * s ^ 2) hpU).trans hQ)
  have hfloor1 : 1 ≤ P / p := by
    have hpows : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    omega
  have htail : meanValue s k (P / p) ≤ C * ((P : ℝ) / p) ^ lambda :=
    (hJ _ hfloor1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le hlambda) hC)
  have hP0 : 0 < P := by
    have hmk : 0 < M := by omega
    exact (pow_pos hmk k).trans_le hMP
  have hpower := diagonal_power_le (by omega : 0 < k) hp.pos hP0 (by omega : 0 < M)
    (by omega : 0 < A) hMP hpU hgap
  have hcoeff : 0 ≤ ((4 * π.card * k.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((4 * π.card * k.factorial : ℕ) : ℝ) *
        (p : ℝ) ^ (2 * s + k * (k - 1) / 2) * (P : ℝ) ^ k *
        (C * ((P : ℝ) / p) ^ lambda) :=
      hcount.trans (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = (((4 * π.card * k.factorial : ℕ) : ℝ) * C) *
        ((p : ℝ) ^ (2 * s + k * (k - 1) / 2) * (P : ℝ) ^ k *
          ((P : ℝ) / p) ^ lambda) := by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hpower (mul_nonneg hcoeff hC)


/-- One proved all-endpoint input moment estimate yields the actual next
moment estimate at every endpoint satisfying the explicit packet conditions. -/
theorem moment_step_of_power_bound {k s P M R : ℕ}
    (hk : 2 ≤ k) (hP : 4 * k ^ 4 ≤ P) (hM : k ≤ M)
    (hbudget : P ^ (2 * k.choose 2) < M ^ R)
    (hroot : P < (M + 1) ^ k) (hMP : M ^ k ≤ P)
    (hs : 1 ≤ s) (hQ : 16 * s ^ 2 * (2 ^ R * M) ≤ P)
    {C lambda : ℝ} (hC : 0 ≤ C) (hlambda : 0 ≤ lambda)
    (hgap : lambda ≤ (2 * s + k * (k - 1) / 2 : ℕ))
    (hJ : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ C * (X : ℝ) ^ lambda) :
    meanValue (s + k) k P ≤
      ((4 * R * k.factorial : ℕ) : ℝ) * C *
        ((2 ^ R : ℕ) : ℝ) ^ (((2 * s + k * (k - 1) / 2 : ℕ) : ℝ) - lambda) *
          (P : ℝ) ^ ((k : ℝ) + lambda +
            (((2 * s + k * (k - 1) / 2 : ℕ) : ℝ) - lambda) / k) := by
  obtain ⟨π, hcard, hπ, hprod, _⟩ :=
    VinogradovTwoBlockPacket.exists_uniform_two_block_packet M R k 0 P
      (by omega : 0 < M) (by simpa only [Nat.zero_add] using hbudget)
  simpa only [hcard] using moment_step_of_packet_bound hk hP hM Nat.one_le_two_pow
    π hπ (by simpa only [Nat.zero_add] using hprod) hroot hMP hs hQ hC hlambda hgap hJ

/-- The same exact defect contraction holds with any proved packet;
only its cardinality and width enter the independent step coefficient. -/
theorem moment_defect_step_of_packet {k s P M A : ℕ}
    (hk : 2 ≤ k) (hP : 4 * k ^ 4 ≤ P) (hM : k ≤ M) (hA : 1 ≤ A)
    (π : Finset ℕ) (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ A * M)
    (hbudget : P ^ (2 * k.choose 2) < ∏ p ∈ π, p)
    (hroot : P < (M + 1) ^ k) (hMP : M ^ k ≤ P)
    (hs : 1 ≤ s) (hQ : 16 * s ^ 2 * (A * M) ≤ P)
    {C delta : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ delta) (hdk : delta ≤ (k : ℝ) ^ 2)
    (hexp : 0 ≤ exponent k s delta)
    (hJ : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ C * (X : ℝ) ^ exponent k s delta) :
    meanValue (s + k) k P ≤
      ((4 * π.card * k.factorial * A ^ (k ^ 2) : ℕ) : ℝ) * C *
        (P : ℝ) ^ exponent k (s + k) (delta * (1 - 1 / (k : ℝ))) := by
  have hgap := power_gap (by omega : 1 ≤ k) s delta
  have hg : exponent k s delta ≤ (2 * s + k * (k - 1) / 2 : ℕ) := by linarith
  have h := moment_step_of_packet_bound hk hP hM hA π hπ hbudget hroot hMP hs hQ hC hexp hg hJ
  rw [hgap, next_exponent (by omega : 0 < k)] at h
  have hpow : (A : ℝ) ^ ((k : ℝ) ^ 2 - delta) ≤
      ((A ^ (k ^ 2) : ℕ) : ℝ) := by
    have he := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ (A : ℝ) by exact_mod_cast hA)
      (show (k : ℝ) ^ 2 - delta ≤ (k : ℝ) ^ 2 by linarith)
    simpa only [← Nat.cast_pow, Real.rpow_natCast, ← pow_mul] using he
  apply h.trans
  have hc : 0 ≤ ((4 * π.card * k.factorial : ℕ) : ℝ) * C := by positivity
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc)
    (Real.rpow_nonneg (Nat.cast_nonneg P) (exponent k (s + k) (delta * (1 - 1 / (k : ℝ)))))
  convert hp using 1
  push_cast
  ring


/-- The exact relative-defect decrement has a packet coefficient
independent of delta throughout its full admissible interval. -/
theorem moment_defect_step {k s P M R : ℕ}
    (hk : 2 ≤ k) (hP : 4 * k ^ 4 ≤ P) (hM : k ≤ M)
    (hbudget : P ^ (2 * k.choose 2) < M ^ R)
    (hroot : P < (M + 1) ^ k) (hMP : M ^ k ≤ P)
    (hs : 1 ≤ s) (hQ : 16 * s ^ 2 * (2 ^ R * M) ≤ P)
    {C delta : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ delta) (hdk : delta ≤ (k : ℝ) ^ 2)
    (hexp : 0 ≤ exponent k s delta)
    (hJ : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ C * (X : ℝ) ^ exponent k s delta) :
    meanValue (s + k) k P ≤
      ((4 * R * k.factorial * 2 ^ (R * k ^ 2) : ℕ) : ℝ) * C *
        (P : ℝ) ^ exponent k (s + k) (delta * (1 - 1 / (k : ℝ))) := by
  have hgap := power_gap (by omega : 1 ≤ k) s delta
  have hg : exponent k s delta ≤ (2 * s + k * (k - 1) / 2 : ℕ) := by linarith
  have h := moment_step_of_power_bound hk hP hM hbudget hroot hMP hs hQ hC hexp hg hJ
  rw [hgap, next_exponent (by omega : 0 < k)] at h
  have hpow : ((2 ^ R : ℕ) : ℝ) ^ ((k : ℝ) ^ 2 - delta) ≤
      ((2 ^ (R * k ^ 2) : ℕ) : ℝ) := by
    have he := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ ((2 ^ R : ℕ) : ℝ) by exact_mod_cast Nat.one_le_two_pow)
      (show (k : ℝ) ^ 2 - delta ≤ (k : ℝ) ^ 2 by linarith)
    simpa only [← Nat.cast_pow, Real.rpow_natCast, ← pow_mul] using he
  apply h.trans
  have hc : 0 ≤ ((4 * R * k.factorial : ℕ) : ℝ) * C := by positivity
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc)
    (Real.rpow_nonneg (Nat.cast_nonneg P) (exponent k (s + k) (delta * (1 - 1 / (k : ℝ)))))
  convert hp using 1
  push_cast
  ring

end
end RiemannGaussian.VinogradovDiagonalExponent
