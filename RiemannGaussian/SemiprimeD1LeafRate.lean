/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1Schedule

/-! # Actual failed schedule guards imply small D.1 leaves
All bounds refer to literal floors and the original integer parameter checks.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1LeafRate
open SemiprimeD1Schedule SemiprimeD1ModeRate SemiprimeD1PrecisionEnvelope

/-- Three explicit original root checks, independent of a precision/path oracle. -/
def RootReady (s lam : ℕ) : Prop :=
  0 < lam/epsilonDenominator ∧
    (minimumLevels lam)^3*(Nat.sqrt lam+1) ≤ (lam/epsilonDenominator)^3 ∧
    lam*(Nat.sqrt lam+1) ≤ s

/-- A small actual retained level forces the original edge count below the leaf cap. -/
theorem small_level_leaf (s lam d M : ℕ) (hr : RootReady s lam)
    (hpath : M*8^d ≤ s) (hu : levels lam d < minimumLevels lam) :
    M ≤ leafSize s lam := by
  let b:=lam/epsilonDenominator
  let B:=minimumLevels lam
  let k:=Nat.sqrt lam+1
  have hB : 0 < B := by dsimp [B,minimumLevels];omega
  have hp : 0 < (2:ℕ)^d := by positivity
  have hf:=Nat.lt_mul_div_succ b hp
  have hule : b/2^d+1 ≤ B := by change b/2^d < B at hu;omega
  have hb : b ≤ B*2^d := by
    have hm:=Nat.mul_le_mul_left (2^d) hule
    nlinarith
  have hcube : b^3 ≤ B^3*8^d := by
    calc
      _  ≤  (B*2^d)^3 := Nat.pow_le_pow_left hb 3
      _ = _ := by
        rw [mul_pow,←pow_mul,Nat.mul_comm d 3,pow_mul]
        norm_num
  have hroot : B^3*k ≤ b^3 := hr.2.1
  have htotal : B^3*(M*k) ≤ B^3*s := by
    calc
      _ = M*(B^3*k) := by ring
      _  ≤  M*b^3 := Nat.mul_le_mul_left M hroot
      _  ≤  M*(B^3*8^d) := Nat.mul_le_mul_left M hcube
      _ = B^3*(M*8^d) := by ring
      _  ≤  B^3*s := Nat.mul_le_mul_left _ hpath
  have hMk : M*k ≤ s := Nat.le_of_mul_le_mul_left htotal (pow_pos hB 3)
  have hk : 0 < k := by dsimp [k];omega
  have hdiv : M ≤ s/k := (Nat.le_div_iff_mul_le hk).mpr hMk
  change M ≤ s/k+1
  omega

/-- Above the actual leaf cap, EVERY original active guard holds automatically. -/
theorem active_of_above_leaf (s lam d M : ℕ) (hr : RootReady s lam)
    (hpath : M*8^d ≤ s) (hM : leafSize s lam < M) : Active s lam d M := by
  have hu : minimumLevels lam ≤ levels lam d := by
    by_contra h
    have hl:=small_level_leaf s lam d M hr hpath (by omega)
    omega
  have hk : 0 < Nat.sqrt lam+1 := by omega
  have hlam : lam ≤ s/(Nat.sqrt lam+1) := (Nat.le_div_iff_mul_le hk).mpr hr.2.2
  have hlevel:=levels_le lam d
  have hlast : levels lam d ≤ M := by
    unfold leafSize at hM
    omega
  exact ⟨hM,hu,hlast⟩

/-- Failure of any actual active guard is a genuine small leaf under root checks. -/
theorem inactive_leaf (s lam d M : ℕ) (hr : RootReady s lam)
    (hpath : M*8^d ≤ s) (hstop : ¬Active s lam d M) : M ≤ leafSize s lam := by
  by_contra h
  exact hstop (active_of_above_leaf s lam d M hr hpath (by omega))

/-- Actual integer leaf size obeys the intended real square-root scale. -/
theorem leafSize_real (s lam : ℕ) (hlam : 0 < lam) :
    (leafSize s lam:ℝ) ≤ (s:ℝ)/Real.sqrt (lam:ℝ)+1 := by
  have hk : 0 < Nat.sqrt lam+1 := by omega
  have hkR : (0:ℝ) < (Nat.sqrt lam+1:ℕ) := by exact_mod_cast hk
  have hsq : Real.sqrt (lam:ℝ) ≤ (Nat.sqrt lam+1:ℕ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    exact_mod_cast le_of_lt (Nat.lt_succ_sqrt' lam)
  have hroot : 0 < Real.sqrt (lam:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hlam)
  have hdiv : ((s/(Nat.sqrt lam+1):ℕ):ℝ) ≤ (s:ℝ)/(Nat.sqrt lam+1:ℕ) := Nat.cast_div_le
  have hbound:=div_le_div_of_nonneg_left (show (0:ℝ) ≤ s by positivity) hroot hsq
  simp only [leafSize,Nat.cast_add,Nat.cast_one]
  linarith

/-- Every stopped actual path node has the fixed intended leaf enumeration scale. -/
theorem inactive_real_leaf (s lam d M : ℕ) (hr : RootReady s lam)
    (hpath : M*8^d ≤ s) (hstop : ¬Active s lam d M) :
    (M:ℝ) ≤ (s:ℝ)/Real.sqrt (lam:ℝ)+1 := by
  have hM : (M:ℝ) ≤ leafSize s lam := by exact_mod_cast inactive_leaf s lam d M hr hpath hstop
  have hpos : 0 < lam := lt_of_lt_of_le hr.1 (Nat.div_le_self _ _)
  exact hM.trans (leafSize_real s lam hpos)

end RiemannGaussian.SemiprimeD1LeafRate
