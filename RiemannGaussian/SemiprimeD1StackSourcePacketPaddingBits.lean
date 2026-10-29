/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingEncoding
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingPrimitives
/-! # Real unary-controlled bit cut and literal zero-prefix loops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingBits
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPaddingPrimitives SemiprimeD1StackProcedureTrace
namespace Old
export SemiprimeD1PacketRoundBits (cut)
end Old
/-- An empty actual binary suffix has no true low bit at any acquired exponent. -/
theorem cut_nil (a:Nat) :(Old.cut a []).low=false ∧ (Old.cut a []).high=[] :=by cases a <;> exact ⟨rfl,rfl⟩
/-- Only physically active cut/count words differ from the arbitrary retained25-word caller bank. -/
def cutWords (w:Words) (a:Nat) (bits:List Bool) :Words:=
  {w with cutTodo:=List.replicate a true,frequency:={w.frequency with oldCount:=bits}}
/-- Every exponent marker and every corresponding actual bit/EOF pop is paid; the finite OR flag is computed, never advised. -/
theorem cut_run (a:Nat) (bits:List Bool) (low:Bool) (w:Words) :
    Runs program (2*a+1) (.cut low) (bank (cutWords w a bits)) (.cutDone (low||(Old.cut a bits).low))
      (bank (cutWords w 0 (Old.cut a bits).high)) :=by
  induction a generalizing bits low with
  | zero=>
    have h:=pop_run (.cut low) (.cutDone low) .abort (.cutBit low) (aux .cutTodo)
      (bank (cutWords w 0 bits)) [] rfl rfl
    rw [update_cutTodo] at h
    change Runs program 1 (.cut low) (bank (cutWords w 0 bits)) (.cutDone low) (bank (cutWords w 0 bits)) at h
    simpa only [Old.cut,SemiprimeSourceCompactBits.copy_bits,Bool.or_false,Nat.mul_zero,Nat.zero_add] using h
  | succ a ih=>
    have h0:=pop_run (.cut low) (.cutDone low) .abort (.cutBit low) (aux .cutTodo)
      (bank (cutWords w (a+1) bits)) (true::List.replicate a true) rfl rfl
    rw [update_cutTodo] at h0
    change Runs program 1 (.cut low) (bank (cutWords w (a+1) bits)) (.cutBit low) (bank (cutWords w a bits)) at h0
    cases bits with
    | nil=>
      have h1:=pop_run (.cutBit low) (.cut low) (.cut low) (.cut true) (frequencyStack F.oldCount)
        (bank (cutWords w a [])) [] rfl rfl
      rw [update_oldCount] at h1
      have h2:=ih [] low
      have h:=join (join h0 h1) h2
      simp only [(cut_nil a).1,(cut_nil a).2,Bool.or_false] at h
      simp only [Old.cut,Bool.or_false]
      convert h using 1; omega
    | cons b bits=>
      have h1:=pop_run (.cutBit low) (.cut low) (.cut low) (.cut true) (frequencyStack F.oldCount)
        (bank (cutWords w a (b::bits))) (b::bits) rfl rfl
      rw [update_oldCount] at h1
      have hlabel:SemiprimeD1StackBytecode.choose (Label.cut low) (Label.cut low) (Label.cut true) (b::bits).head?=Label.cut (low||b):=by cases b <;> cases low <;> rfl
      rw [hlabel] at h1
      have h2:=ih bits (low||b)
      have h:=join (join h0 h1) h2
      rw [Bool.or_assoc] at h
      simp only [Old.cut]
      convert h using 1; omega
/-- A literal false pushed during each marker visit has exactly the intended zero-prefix order. -/
theorem zeros_push (a:Nat) (word:List Bool) :
    List.replicate a false++false::word=List.replicate (a+1) false++word :=by
  induction a with
  | zero=>rfl
  | succ a ih=>simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih
/-- Only the actual second exponent copy and actual high counter word vary in this physical loop. -/
def prefixWords (w:Words) (a:Nat) (bits:List Bool) :Words:=
  {w with prefixTodo:=List.replicate a true,frequency:={w.frequency with count:=bits}}
/-- Exactly one actual false bit per acquired exponent marker, never a unary packet-size or unary numerical maximum expansion. -/
theorem prefix_run (a:Nat) (bits:List Bool) (w:Words) :
    Runs program (2*a+1) .prefix (bank (prefixWords w a bits)) .reverse
      (bank (prefixWords w 0 (List.replicate a false++bits))) :=by
  induction a generalizing bits with
  | zero=>
    have h:=pop_run .prefix .reverse .abort .zero (aux .prefixTodo) (bank (prefixWords w 0 bits)) [] rfl rfl
    rw [update_prefixTodo] at h
    exact h
  | succ a ih=>
    have h0:=pop_run .prefix .reverse .abort .zero (aux .prefixTodo) (bank (prefixWords w (a+1) bits)) (true::List.replicate a true) rfl rfl
    rw [update_prefixTodo] at h0
    have h1:=push_run .zero .prefix (frequencyStack (F.aux .count)) false (bank (prefixWords w a bits)) rfl
    rw [update_count] at h1
    have h2:=ih (false::bits)
    have h:=join (join h0 h1) h2
    rw [zeros_push] at h
    convert h using 1; omega
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingBits
