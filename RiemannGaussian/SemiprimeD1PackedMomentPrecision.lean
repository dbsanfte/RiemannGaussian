/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedMomentOriginal
import RiemannGaussian.SemiprimeD1PrecisionEnvelope
import RiemannGaussian.SemiprimeD1PublicPackingReady

/-! # All locally marked coefficients fit the public 2ell-bit precision
The proof uses the actual LOCAL source width checks and public radix schedule,
not knowledge of an accepted full assignment or of the unknown factors.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedMomentPrecision
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroParameters
open SemiprimePublicFactorCount SemiprimeD1PackedMomentDigits SemiprimeD1PackedMomentOriginal
open SemiprimeD1PackedMomentAlgebra
attribute [local instance] Classical.propDecidable

/-- Public scalar precision; the root still has no jet axes and rank one. -/
def precision (N : ℕ) : ℕ := 2*bitLength N

/-- The root's scalar modulus is exactly the square used by the moment identity. -/
theorem modulus (N : ℕ) : 2^precision N=(2^bitLength N)^2 := by
  rw [precision,Nat.mul_comm 2, pow_mul]

/-- Every active digit's exact radix position and local width lie inside ell. -/
theorem digit_width (ell i : ℕ) (hL : 0 < ell) (hi : i < digitCount ell) :
    activeDigitBits ell i+radixBits ell*i  ≤  ell := by
  have hw := (activeDigitBits_bounds hL hi).1
  have hr := Nat.min_le_right (radixBits ell) (ell-i*radixBits ell)
  change 0 < min (radixBits ell) (ell-i*radixBits ell) at hw
  have hm : i*radixBits ell ≤ ell := by omega
  have he := Nat.sub_add_cancel hm
  unfold activeDigitBits
  rw [Nat.mul_comm (radixBits ell) i]
  omega

/-- A checked active digit's contribution fits ell bits BEFORE the mark is
constructed. This is independent of all other local or global assignments. -/
theorem digit_contribution (N digit i : ℕ) (hN : 0 < N) (hi : i < digitCount (bitLength N))
    (hd : digit < 2^activeDigitBits (bitLength N) i) :
    digit*(2^radixBits (bitLength N))^i < 2^bitLength N := by
  have hm := Nat.mul_lt_mul_of_pos_right hd (show 0 < (2^radixBits (bitLength N))^i by positivity)
  have he : 2^activeDigitBits (bitLength N) i*(2^radixBits (bitLength N))^i=
      2^(activeDigitBits (bitLength N) i+radixBits (bitLength N)*i) := by rw [←pow_mul,←pow_add]
  rw [he] at hm
  exact hm.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    (digit_width (bitLength N) i (bitLength_pos hN) hi))

/-- The actual input checker supplies the entire local mark bound, including
zero inactive words and both operand sides. No factor value is a premise. -/
theorem input_mark (N : ℕ) (hN : 0 < N) (side : Fin 2)
    (i : Fin ((publicConfig N hN).r*(publicConfig N hN).t))
    (x : LocalSlot (Vertex.input (r:=(publicConfig N hN).r) (t:=(publicConfig N hN).t)
      (digits:=(publicConfig N hN).digits) side i)→Bool)
    (hx : localTable (publicConfig N hN) (.input side i) x) :
    originalMark (publicConfig N hN) (.input side i) x < 2^bitLength N := by
  let p := publicConfig N hN
  dsimp only [localTable] at hx
  change (if side=0 then readWord (p.r*p.t+1) (fun bit => x (.inl bit))*(2^p.bits)^i.val else 0) < 2^bitLength N
  by_cases hs : side=0
  · rw [ite_eq_left hs]
    by_cases hi : i.val < p.digits
    · rw [dite_eq_left hi] at hx
      exact digit_contribution N _ i.val hN hi hx.1
    · rw [dite_eq_right hi] at hx
      rw [hx,Nat.zero_mul]
      positivity
  · rw [ite_eq_right hs]
    positivity

/-- Every actual valid local table row has an ell-bit mark; all equality and
non-input vertices contribute zero. This is stronger than an accepted-model bound. -/
theorem local_mark (N : ℕ) (hN : 0 < N) (v : SubdividedVertex (publicConfig N hN).r
    (publicConfig N hN).t (publicConfig N hN).digits)
    (x : Fin (subdividedArity v)→Bool)
    (hx : subdividedTable (publicConfig N hN) v x=true) :
    localMark (publicConfig N hN) v x < 2^bitLength N := by
  cases v with
  | inl v =>
    have hv : localTable (publicConfig N hN) v (fun slot => x ((localSlotFinEquiv v) slot)) := of_decide_eq_true hx
    change originalMark (publicConfig N hN) v _ < 2^bitLength N
    cases v with
    | input side i => exact input_mark N hN side i _ hv
    | first tr j | scale tr j k | second tr k | product k | carry k | orGate side i | inputCheck side =>
      change 0 < 2^bitLength N
      positivity
    | carryInitial | carryTerminal =>
      change 0 < 2^bitLength N
      positivity
  | inr signal =>
    change 0 < 2^bitLength N
    positivity

/-- Exact binary coefficient specification: original false rows remain zero;
the sole change is a mark on first-side input rows of original value one. -/
def coefficient (N : ℕ) (hN : 0 < N) (v : SubdividedVertex (publicConfig N hN).r
    (publicConfig N hN).t (publicConfig N hN).digits) (x : Fin (subdividedArity v)→Bool) : ℕ :=
  if subdividedTable (publicConfig N hN) v x then 1+2^bitLength N*localMark (publicConfig N hN) v x else 0

/-- ALL locally supplied table coefficients fit the paid 2ell-bit root precision,
without assuming that a local row extends to a satisfying assignment. -/
theorem coefficient_fits (N : ℕ) (hN : 0 < N) (v : SubdividedVertex (publicConfig N hN).r
    (publicConfig N hN).t (publicConfig N hN).digits) (x : Fin (subdividedArity v)→Bool) :
    coefficient N hN v x < 2^precision N := by
  unfold coefficient
  rw [modulus]
  by_cases hx : subdividedTable (publicConfig N hN) v x=true
  · rw [ite_eq_left hx]
    have hb : 1 < 2^bitLength N := (show 1 ≤ N by omega).trans_lt (input_lt_bitLength_power N)
    exact packed_lt _ 1 _ hb (local_mark N hN v x hx)
  · rw [ite_eq_right hx]
    positivity

/-- Casting the actual nonnegative coefficient specification gives exactly
the local weighted table used in the full graph moment theorem. -/
theorem coefficient_value (N : ℕ) (hN : 0 < N) (v : SubdividedVertex (publicConfig N hN).r
    (publicConfig N hN).t (publicConfig N hN).digits) (x : Fin (subdividedArity v)→Bool) :
    (coefficient N hN v x : ZMod ((2^bitLength N)^2))=
      markedTable (publicConfig N hN) ((2^bitLength N : ℕ) : ZMod ((2^bitLength N)^2)) v x := by
  unfold coefficient markedTable
  split  <;> simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_zero]

/-- The larger root precision fits the ALREADY PROVED inherited path budget,
with no additional jet axis or rank multiplier. -/
theorem precision_le_scale (N : ℕ) : precision N ≤ SemiprimeD1PublicPackingReady.scale (bitLength N) := by
  unfold precision SemiprimeD1PublicPackingReady.scale
  exact Nat.mul_le_mul_right _ (by decide : (2:ℕ) ≤ 2^20)

/-- The existing numeric envelope admits the new root precision for EVERY
public input. Its physical metadata source remains a separate obligation. -/
theorem root_precision_guard (N lam : ℕ) : precision N ≤
    SemiprimeD1PrecisionEnvelope.pathCap (SemiprimeD1PublicPackingReady.scale (bitLength N)) lam 0 0 := by
  rw [SemiprimeD1PrecisionEnvelope.root_cap]
  exact precision_le_scale N

end RiemannGaussian.SemiprimeD1PackedMomentPrecision
