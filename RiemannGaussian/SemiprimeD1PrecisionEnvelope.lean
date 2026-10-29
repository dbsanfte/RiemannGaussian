/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRate
import Mathlib.Data.Nat.Log

/-! # Inherited D.11 precision and derived node acquisition guards

The actual precision update preserves a numeric path envelope. A logarithmic
minimum taper length makes the additional 2^u reserve pay inherited precision
and evaluation loss. The original schedule/active-leaf theorem remains a later
join; the envelope is not an oracle for an acquired coefficient or precision.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1PrecisionEnvelope
open SemiprimeD1ModeRate

/-- A conservative explicit coefficient for the path's inherited precision. -/
def pathFactor (lam depth : ℕ) : ℕ := 40*depth*(4*lam+1)+1

/-- Precision at a call before its new cumulative exponent is introduced. -/
def pathCap (s lam depth previous : ℕ) : ℕ := s*pathFactor lam depth*2^previous

/-- A computable logarithmic guard for absorbing all polynomial level losses. -/
def minimumLevels (lam : ℕ) : ℕ := 4*Nat.clog 2 (lam+1)+8

/-- At the root the envelope is precisely the original input precision budget. -/
theorem root_cap (s lam : ℕ) : pathCap s lam 0 0=s := by simp [pathCap,pathFactor]

/-- The actual ceiling height never exceeds four times the original edge count. -/
theorem jetHeight_le (M u : ℕ) (hu : u ≤ M) : jetHeight M u ≤ 4*M := by
  have h := Nat.div_le_self (3*M+u-1) u
  unfold jetHeight
  omega

/-- A single literal precision update costs at most the explicit next-level reserve. -/
theorem update_le (s lam M u a i p : ℕ) (hM : M ≤ s) (hu : u ≤ M) (ha : a ≤ 4*lam) :
    workingPrecision M u a i p ≤ p+40*s*(4*lam+1)*2^a := by
  have hh : jetHeight M u ≤ 4*s := (jetHeight_le M u hu).trans (by omega)
  have hD : 2^(a-i) ≤ (2:ℕ)^a := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hpow : 1 ≤ (2:ℕ)^a := Nat.one_le_pow _ _ (by decide)
  have he : 8*jetHeight M u*2^(a-i) ≤ 32*s*2^a := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hh) hD
    convert h using 1
    ring
  have hv : 8*M*(a+1) ≤ 8*s*(4*lam+1)*2^a := by
    calc
      _ ≤ 8*s*(4*lam+1) := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hM) (by omega)
      _ ≤ _ := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (8*s*(4*lam+1)) hpow
  have h32 : 32*s*2^a ≤ 32*s*(4*lam+1)*2^a := by
    have h := Nat.mul_le_mul_right (32*s*2^a) (show 1 ≤ 4*lam+1 by omega)
    convert h using 1 <;> ring
  have hsum : 32*s*2^a+8*s*(4*lam+1)*2^a ≤ 40*s*(4*lam+1)*2^a := by
    calc
      _ ≤ 32*s*(4*lam+1)*2^a+8*s*(4*lam+1)*2^a := Nat.add_le_add_right h32 _
      _ = _ := by ring
  unfold workingPrecision
  omega

/-- Actual child precision preserves the creation-depth envelope. -/
theorem update_cap (s lam depth previous M u a i p : ℕ)
    (hM : M ≤ s) (hu : u ≤ M) (ha : a ≤ 4*lam) (hprev : previous ≤ a)
    (hp : p ≤ pathCap s lam depth previous) :
    workingPrecision M u a i p ≤ pathCap s lam (depth+1) a := by
  have hpow : (2:ℕ)^previous ≤ 2^a := Nat.pow_le_pow_right (by decide) hprev
  have hcap : pathCap s lam depth previous ≤ s*pathFactor lam depth*2^a :=
    Nat.mul_le_mul_left _ hpow
  calc
    _ ≤ p+40*s*(4*lam+1)*2^a := update_le s lam M u a i p hM hu ha
    _ ≤ s*pathFactor lam depth*2^a+40*s*(4*lam+1)*2^a :=
      Nat.add_le_add_right (hp.trans hcap) _
    _ = _ := by unfold pathCap pathFactor;ring

/-- Before every depth at most lam, inherited precision has a uniform quadratic factor. -/
theorem cap_uniform (s lam depth previous : ℕ) (hd : depth ≤ lam) :
    pathCap s lam depth previous ≤ s*(201*(lam+1)^2)*2^previous := by
  have h : pathFactor lam depth ≤ 201*(lam+1)^2 := by
    unfold pathFactor
    have hx := Nat.mul_le_mul_right (40*(4*lam+1)) hd
    nlinarith
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)

/-- The logarithmic taper guard gives the needed concrete exponential reserve. -/
theorem reserve_le (lam u : ℕ) (hu : minimumLevels lam ≤ u) :
    201*(lam+1)^4 ≤ (2:ℕ)^u := by
  have hc : lam+1 ≤ (2:ℕ)^Nat.clog 2 (lam+1) := Nat.le_pow_clog (by decide) _
  have hp := Nat.pow_le_pow_left hc 4
  have he : (2:ℕ)^(minimumLevels lam)=256*((2:ℕ)^Nat.clog 2 (lam+1))^4 := by
    unfold minimumLevels
    rw [show 4*Nat.clog 2 (lam+1)=Nat.clog 2 (lam+1)*4 by omega,pow_add,pow_mul]
    norm_num
    ring
  calc
    _ ≤ 256*((2:ℕ)^Nat.clog 2 (lam+1))^4 :=
      Nat.mul_le_mul (by decide : 201 ≤ 256) hp
    _ = 2^(minimumLevels lam) := he.symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hu

/-- Inherited precision satisfies the actual first node guard, not a desired rate answer. -/
theorem input_guard (s lam depth previous M u a i p : ℕ)
    (hp : p ≤ pathCap s lam depth previous) (hd : depth ≤ lam)
    (hsize : s ≤ M*(lam+1)) (hu : u ≤ lam) (hlevels : minimumLevels lam ≤ u)
    (ha : previous+2*u ≤ a) (hi : i ≤ u) : p*u ≤ M*2^(a-i) := by
  have hcap := hp.trans (cap_uniform s lam depth previous hd)
  have hscale : s*(201*(lam+1)^2)*2^previous*u ≤
      M*(201*(lam+1)^4)*2^previous := by
    calc
      _ ≤ M*(lam+1)*(201*(lam+1)^2)*2^previous*u := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsize))
      _ ≤ M*(lam+1)*(201*(lam+1)^2)*2^previous*(lam+1) :=
        Nat.mul_le_mul_left _ (show u ≤ lam+1 by omega)
      _ = _ := by ring
  have hreserve := reserve_le lam u hlevels
  have hexp : previous+u ≤ a-i := by omega
  calc
    _ ≤ s*(201*(lam+1)^2)*2^previous*u := Nat.mul_le_mul_right u hcap
    _ ≤ M*(201*(lam+1)^4)*2^previous := hscale
    _ ≤ M*2^u*2^previous := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hreserve)
    _ = M*2^(previous+u) := by rw [pow_add];ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp)

/-- The same reserve pays the evaluation term in the actual working precision. -/
theorem evaluation_guard (lam u a i : ℕ) (hu : u ≤ lam)
    (hlevels : minimumLevels lam ≤ u) (ha : a ≤ 4*lam) (hstep : 2*u ≤ a) (hi : i ≤ u) :
    (a+1)*u ≤ (2:ℕ)^(a-i) := by
  have hpoly : (a+1)*u ≤ 201*(lam+1)^4 := by
    have h := Nat.mul_le_mul (show a+1 ≤ 4*lam+1 by omega) hu
    have hh : (lam+1)^2 ≤ (lam+1)^4 :=
      Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4)
    nlinarith
  exact (hpoly.trans (reserve_le lam u hlevels)).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

end RiemannGaussian.SemiprimeD1PrecisionEnvelope
