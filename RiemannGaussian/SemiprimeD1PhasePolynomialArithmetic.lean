/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Fixed scalar bookkeeping for retained phase reports
Actual constructor/report bounds instantiate this arithmetic lemma. In particular
source and child reports keep their literal acquired-menu multiplicities.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PhasePolynomialArithmetic

/-- Sum of fixed scalar coefficients, with all64 groups retained. -/
def coefficient (G F Z C E V B A : ℕ) : ℕ := G+F+Z+64*C+E+V+1+B+A

/-- The acquired mode menu is paid quadratically, including each child's
repeated upstream source/header producer. No sharing is inferred. -/
theorem phase_bound (L D G F Z C E V B A g o src z child e v b ctrl : ℕ)
    (hg : g+o ≤ G) (hs : src ≤ F*(L+1)) (hz : z ≤ Z)
    (hc : child ≤ C*(L+1)*2^D) (he : e ≤ E) (hv : v ≤ V)
    (hb : b ≤ B) (ha : ctrl ≤ A*(L+1)) :
    g+o+src+z+(L*(64*child)+L*e+v+1)+b+ctrl ≤
      coefficient G F Z C E V B A*(L+1)^2*2^D := by
  let K:=(L+1)^2*2^D
  have hp : 1 ≤ 2^D := Nat.one_le_pow _ _ (by decide)
  have hl : L+1 ≤ (L+1)^2 := Nat.le_self_pow (by decide : 2 ≠ 0) _
  have hLK : L+1 ≤ K := hl.trans (by
    dsimp only [K]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((L+1)^2) hp)
  have h1 : 1 ≤ K := (by omega : 1 ≤ L+1).trans hLK
  have hLL : L*(L+1)*2^D ≤ K := by
    dsimp only [K]
    exact Nat.mul_le_mul_right _ (by nlinarith only [Nat.le_succ L])
  have lift (x : ℕ) : x ≤ x*K := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left x h1
  have hg':=hg.trans (lift G)
  have hs':=hs.trans (Nat.mul_le_mul_left F hLK)
  have hz':=hz.trans (lift Z)
  have hc' : L*(64*child) ≤ (64*C)*K := by
    calc
      _ ≤ L*(64*(C*(L+1)*2^D)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 64 hc)
      _ = (64*C)*(L*(L+1)*2^D) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hLL
  have he' : L*e ≤ E*K := by
    calc
      _ ≤ L*E := Nat.mul_le_mul_left L he
      _ = E*L := Nat.mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_left E (by omega : L ≤ K)
  have hv' : v+1 ≤ (V+1)*K := (Nat.add_le_add_right hv 1).trans (lift (V+1))
  have hb':=hb.trans (lift B)
  have ha':=ha.trans (Nat.mul_le_mul_left A hLK)
  calc
    _ ≤ G*K+F*K+Z*K+((64*C)*K+E*K+(V+1)*K)+B*K+A*K := by omega
    _ = coefficient G F Z C E V B A*K := by unfold coefficient;ring
    _ = _ := by dsimp only [K];ring

end RiemannGaussian.SemiprimeD1PhasePolynomialArithmetic
