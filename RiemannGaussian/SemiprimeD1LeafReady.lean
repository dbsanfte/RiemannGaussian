/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1LeafRate
import RiemannGaussian.SemiprimeD1PathRate
import RiemannGaussian.SemiprimeSourceLayoutRate

/-! # Eventual original-input acceptance of the literal D.1 leaf checks
Actual binary ceiling logarithms, integer floors and fixed constants are retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1LeafReady
open scoped Topology
open Filter SemiprimeD1Schedule SemiprimeD1PrecisionEnvelope SemiprimeD1LeafRate

/-- Literal logarithmic minimum-level guard has sublinear cubed size. -/
theorem eventually_minimum_cube :
    ∀ᶠ lam : ℕ in atTop,(minimumLevels lam)^3 ≤ lam := by
  have hlog := (tendsto_add_atTop_nat 1).eventually
    (SemiprimeSourceLayoutRate.eventually_clog_power_le_rpow 3 (1/2) (by norm_num))
  filter_upwards [hlog,eventually_ge_atTop (12000000:ℕ)] with lam hl hlam
  have hm : 1 ≤ Nat.clog 2 (lam+1) := Nat.clog_pos (by decide) (by omega)
  have hB : minimumLevels lam ≤ 12*Nat.clog 2 (lam+1) := by unfold minimumLevels;omega
  have hp : (minimumLevels lam:ℝ)^3 ≤ (12*(Nat.clog 2 (lam+1):ℝ))^3 := by
    exact_mod_cast Nat.pow_le_pow_left hB 3
  have hlambda : (12000000:ℝ) ≤ lam := by exact_mod_cast hlam
  have hquad : (0:ℝ) ≤ (lam:ℝ)*((lam:ℝ)-12000000) :=
    mul_nonneg (by positivity) (by linarith)
  have hsqrt : Real.sqrt (lam+1:ℕ) ≤ (lam:ℝ)/1728 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    push_cast
    nlinarith
  rw [←Real.sqrt_eq_rpow] at hl
  have hfinal : (minimumLevels lam:ℝ)^3 ≤ lam := by nlinarith
  exact_mod_cast hfinal

/-- Large actual root quotient and two computed integer checks imply RootReady. -/
theorem rootReady_of_numeric (s lam : ℕ)
    (hB : (minimumLevels lam)^3 ≤ lam)
    (hlarge : (2*epsilonDenominator)^2 ≤ lam/epsilonDenominator)
    (hinput : lam^2 ≤ s) : RootReady s lam := by
  let b:=lam/epsilonDenominator
  have hK : 0<epsilonDenominator := by norm_num [epsilonDenominator]
  have hb1 : 1 ≤ b := by
    dsimp [b]
    norm_num only [epsilonDenominator] at hlarge ⊢
    omega
  have hlambda : epsilonDenominator ≤ lam := by
    have hm:=Nat.mul_le_mul_right epsilonDenominator hb1
    have hd:=Nat.div_mul_le_self lam epsilonDenominator
    dsimp only [b] at hm
    simpa only [Nat.one_mul] using hm.trans hd
  have hlambda2 : 1<lam := by norm_num only [epsilonDenominator] at hlambda;omega
  have hk : Nat.sqrt lam+1 ≤ lam := by have:=Nat.sqrt_lt_self hlambda2;omega
  have hroot : lam ≤ (2*epsilonDenominator)*b := by
    simpa only [b,epsilonDenominator,show 2*(128*1024)=262144 by norm_num] using
      SemiprimeD1PathRate.root_floor_bound lam hlambda
  have hcube : lam^2 ≤ b^3 := by
    calc
      _ ≤ ((2*epsilonDenominator)*b)^2 := Nat.pow_le_pow_left hroot 2
      _ = (2*epsilonDenominator)^2*b^2 := by ring
      _ ≤ b*b^2 := Nat.mul_le_mul_right _ hlarge
      _ = b^3 := by ring
  refine ⟨by change 0<b;omega,?_,?_⟩
  · exact (Nat.mul_le_mul hB hk).trans (by simpa only [pow_two] using hcube)
  · exact (Nat.mul_le_mul_left lam hk).trans (by simpa only [pow_two] using hinput)

/-- The original binary input parameter's square is eventually paid by root size. -/
theorem eventually_input_square :
    ∀ᶠ s : ℕ in atTop,(Nat.clog 2 (s+2))^2 ≤ s := by
  have hlog := (tendsto_add_atTop_nat 2).eventually
    (SemiprimeSourceLayoutRate.eventually_clog_power_le_rpow 2 (1/2) (by norm_num))
  filter_upwards [hlog,eventually_ge_atTop (3:ℕ)] with s hl hs
  rw [←Real.sqrt_eq_rpow] at hl
  have hsR : (3:ℝ) ≤ s := by exact_mod_cast hs
  have hroot : Real.sqrt (s+2:ℕ) ≤ (s:ℝ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    push_cast
    have hh : (0:ℝ) ≤ ((s:ℝ)-2)*((s:ℝ)+1) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  exact_mod_cast hl.trans hroot

/-- Every literal RootReady check eventually succeeds at the actual original
parameter lam=clog2(s+2), with no eventual-acceptance premise. -/
theorem eventually_rootReady :
    ∀ᶠ s : ℕ in atTop,RootReady s (Nat.clog 2 (s+2)) := by
  have ht : Tendsto (fun s : ℕ => Nat.clog 2 (s+2)) atTop atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  have hB:=ht.eventually eventually_minimum_cube
  have hlarge:=ht.eventually (eventually_ge_atTop
    ((2*epsilonDenominator)^2*epsilonDenominator))
  filter_upwards [hB,hlarge,eventually_input_square] with s hBs hLs hIs
  apply rootReady_of_numeric s (Nat.clog 2 (s+2)) hBs _ hIs
  exact (Nat.le_div_iff_mul_le (by norm_num [epsilonDenominator])).mpr hLs

/-- Uniform original-input bound for EVERY actual stopped path node,
with all extra leaf guards discharged eventually rather than assumed. -/
theorem eventually_inactive_leaf :
    ∀ᶠ s : ℕ in atTop,∀d M : ℕ,
      M*8^d ≤ s → ¬Active s (Nat.clog 2 (s+2)) d M →
      (M:ℝ) ≤ (s:ℝ)/Real.sqrt (Nat.clog 2 (s+2):ℕ)+1 := by
  filter_upwards [eventually_rootReady] with s hr
  intro d M hpath hstop
  exact inactive_real_leaf s _ d M hr hpath hstop

end RiemannGaussian.SemiprimeD1LeafReady
