/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackingReady
import RiemannGaussian.SemiprimeMacroParameters

/-! # Actual public macro dimensions fit the one global D.1 degree cap
Integer powers retain the original scope constant and the literal public scale.
This is a dimension/packing theorem, not a completed recursive bit clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PublicPackingReady
open SemiprimeD1PackingReady

/-- Fixed public root-size scale, before all inputs. -/
def scale (ell : ℕ) : ℕ := 2^20*ell

/-- The literal rounded degree cap has its original eighteenth-power size. -/
theorem degreeCap_power (s : ℕ) : s^18 ≤ (degreeCap s)^20 := by
  have hs : s ≤ 2^logarithm s :=
    (show s ≤ s+2 by omega).trans (Nat.le_pow_clog (by decide : 1<2) _)
  have he : 18*logarithm s ≤ ((9*logarithm s+9)/10)*20 := by omega
  calc
    _ ≤ (2^logarithm s)^18 := Nat.pow_le_pow_left hs _
    _ = 2^(18*logarithm s) := by rw [← pow_mul];congr 1;omega
    _ ≤ 2^(((9*logarithm s+9)/10)*20) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) he
    _ = _ := by rw [degreeCap,← pow_mul]

/-- Every original fourth-power scope estimate fits the literal global cap. -/
theorem scope_of_fourth (ell degree : ℕ) (hell : 0<ell)
    (hd : degree^4 ≤ 512^4*ell^3) : degree ≤ degreeCap (scale ell) := by
  have hp := Nat.pow_le_pow_left hd 5
  have htwenty : degree^20 ≤ 512^20*ell^15 := by
    simpa only [mul_pow,← pow_mul] using hp
  have hel : ell^15 ≤ ell^18 := Nat.pow_le_pow_right hell (by decide)
  have hc : (512:ℕ)^20 ≤ (2^20)^18 := by norm_num
  have hcap := degreeCap_power (scale ell)
  have hfinal : degree^20 ≤ degreeCap (scale ell)^20 :=
    htwenty.trans ((Nat.mul_le_mul hc hel).trans (by simpa only [scale,mul_pow] using hcap))
  exact (Nat.pow_le_pow_iff_left (by decide : (20:ℕ)≠0)).mp hfinal

/-- Actual equality-subdivided public macro scopes fit at every positive input width. -/
theorem actual_scope (ell : ℕ) (hell : 0<ell) :
    SemiprimeMacroParameters.scopeBound ell ≤ degreeCap (scale ell) :=
  scope_of_fourth ell _ hell (SemiprimeMacroParameters.scopeBound_fourth_le hell)

/-- Actual public equality-graph variable count fits the same fixed root size. -/
theorem actual_size (ell : ℕ) (hell : 0<ell) :
    SemiprimeMacroParameters.variableCount ell ≤ scale ell := by
  exact (SemiprimeMacroParameters.variableCount_le hell).trans
    (Nat.mul_le_mul_right ell (by norm_num : 6400≤2^20))

end RiemannGaussian.SemiprimeD1PublicPackingReady
