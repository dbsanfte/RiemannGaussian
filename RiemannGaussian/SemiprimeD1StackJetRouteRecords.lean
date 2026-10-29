/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetSuffixOriginal
/-! # Original-derived routing record tape and byte bounds -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteRecords
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Specification of the acquired record bytes, not an input to the route. -/
def tape : List (ℕ×ℕ)→List Bool
  | []=>[]
  | (q,d)::xs=>frame (unary q) (frame (unary d) (tape xs))
@[simp] theorem tape_cons_length (q d : ℕ) (xs : List (ℕ×ℕ)) :
    (tape ((q,d)::xs)).length=2*q+2*d+2+(tape xs).length := by
  simp [tape,SemiprimeSourceHistogramKeyBits.frame_length,unary]
  omega
/-- The executed supplier's record bytes are precisely the frozen original suffix records. -/
theorem acquired_tape (axes : List ℕ) :
    SemiprimeD1StackJetSuffixOriginal.recordTape axes 1 []=
      tape (SemiprimeD1StackRouteArithmetic.records axes) := by
  induction axes with
  | nil=>rfl
  | cons q qs ih=>simp only [SemiprimeD1StackJetSuffixOriginal.recordTape,
      SemiprimeD1StackRouteArithmetic.records,tape,Nat.mul_one,ih]

/-- Every original suffix record is rank-bounded, so the actual encoded inventory
is polynomial in axis count and the rank acquired by the supplier. -/
theorem original_tape_length (axes : List ℕ) (hp : ∀q∈axes,0<q) :
    (tape (SemiprimeD1StackRouteArithmetic.records axes)).length≤(4*axes.prod+2)*axes.length := by
  have aux : ∀(rs : List (ℕ×ℕ)) (cap : ℕ),
      (∀p∈rs,p.1≤cap ∧ p.2≤cap)→(tape rs).length≤(4*cap+2)*rs.length := by
    intro rs cap hb
    induction rs with
    | nil=>simp [tape]
    | cons p ps ih=>
      rcases p with ⟨q,d⟩
      have hqd:=hb (q,d) (by simp)
      have ht:=ih (fun p hp=>hb p (by simp [hp]))
      rw [tape_cons_length,List.length_cons]
      nlinarith
  have hb : ∀p∈SemiprimeD1StackRouteArithmetic.records axes,p.1≤axes.prod ∧ p.2≤axes.prod := by
    intro p hmem
    have h:=SemiprimeD1StackRouteArithmetic.record_bounds axes hp p.1 p.2 hmem
    exact ⟨h.2.2.1,h.2.2.2.1⟩
  have hlen : (SemiprimeD1StackRouteArithmetic.records axes).length=axes.length := by
    clear hp hb
    induction axes with
    | nil=>rfl
    | cons q qs ih=>simp [SemiprimeD1StackRouteArithmetic.records,ih]
  simpa only [hlen] using aux _ axes.prod hb
end RiemannGaussian.SemiprimeD1StackJetRouteRecords
