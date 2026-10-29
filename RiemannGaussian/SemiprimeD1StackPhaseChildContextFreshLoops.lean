/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshPrimitives
/-! # Entire physical dense-index coefficient allocation and byte serialization loops -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshLoops
open SemiprimeD1StackPhaseChildContextFresh SemiprimeD1StackPhaseChildContextFreshArithmetic
open SemiprimeD1StackPhaseChildContextFreshPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
/-- Every unused old-rank marker is physically drained, including q=1 and early exhaustion. -/
theorem clear_skip (ph : H.Stack→List Bool) (r : Nat) (hist out scratch : List Bool) :
    Runs program (r+1) .clearSkip (store ph [] (unary r) hist out scratch) .seed (store ph [] [] hist out scratch) :=by
  induction r with
  | zero=>exact empty_skip .clearSkip .seed .clearSkip rfl ph [] hist out scratch
  | succ r ih=>
    have h0:=pop_skip .clearSkip .seed .clearSkip rfl ph [] (unary r) hist out scratch true
    have hh:=join h0 ih
    simpa only [show (r+1)+1=1+(r+1) by omega,unary,List.replicate_succ] using hh
/-- All coefficients AFTER the unique fresh index are physically emitted empty. -/
theorem after_loop (ph : H.Stack→List Bool) (n : Nat) (hist out scratch : List Bool) :
    Runs program (3*n+2) .after (store ph (unary n) [] hist out scratch) .seed
      (store ph [] [] ((bytes (List.replicate n [])).reverse++hist) out scratch) :=by
  induction n generalizing hist with
  | zero=>
    have hh:=join (empty_remaining .after .clearSkip .zeroAfter0 rfl ph [] hist out scratch)
      (clear_skip ph 0 hist out scratch)
    simpa [unary,bytes] using hh
  | succ n ih=>
    have h0:=pop_remaining .after .clearSkip .zeroAfter0 rfl ph (unary n) [] hist out scratch true
    have h1:=zero_after ph (unary n) [] hist out scratch
    have hh:=join (join h0 h1) (ih ([false,true]++hist))
    rw [show 3*(n+1)+2=1+2+(3*n+2) by omega]
    simpa [unary,List.replicate_succ,bytes,chunk,SemiprimeSourceHistogramKeyBits.frame,List.reverse_append,List.append_assoc] using hh
/-- Physical width peek plus two/four actual pushes emits the ORIGINAL reduced scalar unit. -/
theorem unit_emit (ph : H.Stack→List Bool) (rem hist out scratch : List Bool) :
    ∃time≤ 5,Runs program time .unit (store ph rem [] hist out scratch) .after
      (store ph rem [] ((chunk (unit (positive ph))).reverse++hist) out scratch) :=by
  have h0:=unit_peek ph rem hist out scratch
  cases hb:positive ph with
  | false=>
    rw [hb] at h0
    refine ⟨3,by omega,?_⟩
    simpa [unit,hb,chunk,SemiprimeSourceHistogramKeyBits.frame] using join h0 (zero_after ph rem [] hist out scratch)
  | true=>
    rw [hb] at h0
    refine ⟨5,by omega,?_⟩
    simpa [unit,hb,chunk,SemiprimeSourceHistogramKeyBits.frame] using join h0 (one ph rem [] hist out scratch)
/-- Actual rank counters drive the complete fresh dense vector; no list allocator opcode exists. -/
theorem before_loop (ph : H.Stack→List Bool) (n r : Nat) (hist out scratch : List Bool) :
    ∃time≤ 6*n+r+3,Runs program time .before (store ph (unary n) (unary r) hist out scratch) .seed
      (store ph [] [] ((bytes (words n r (positive ph))).reverse++hist) out scratch) :=by
  induction n generalizing r hist with
  | zero=>
    have h0:=empty_remaining .before .clearSkip .choose rfl ph (unary r) hist out scratch
    have hh:=join h0 (clear_skip ph r hist out scratch)
    refine ⟨1+(r+1),by omega,?_⟩
    simpa [unary,words,bytes] using hh
  | succ n ih=>
    have h0:=pop_remaining .before .clearSkip .choose rfl ph (unary n) (unary r) hist out scratch true
    cases r with
    | zero=>
      have h1:=empty_skip .choose .unit .zeroBefore0 rfl ph (unary n) hist out scratch
      obtain ⟨b,hb,h2⟩:=unit_emit ph (unary n) hist out scratch
      have h3:=after_loop ph n ((chunk (unit (positive ph))).reverse++hist) out scratch
      have hh:=join (join (join h0 h1) h2) h3
      refine ⟨1+1+b+(3*n+2),by omega,?_⟩
      simpa [unary,List.replicate_succ,words,bytes,List.reverse_append,List.append_assoc] using hh
    | succ r=>
      have h1:=pop_skip .choose .unit .zeroBefore0 rfl ph (unary n) (unary r) hist out scratch true
      have h2:=zero_before ph (unary n) (unary r) hist out scratch
      obtain ⟨b,hb,h3⟩:=ih r ([false,true]++hist)
      have hh:=join (join (join h0 h1) h2) h3
      refine ⟨1+1+2+b,by omega,?_⟩
      simpa [unary,List.replicate_succ,words,bytes,chunk,SemiprimeSourceHistogramKeyBits.frame,List.reverse_append,List.append_assoc] using hh
/-- One actual vector-terminator push precedes the real history reverse. -/
theorem seed (ph : H.Stack→List Bool) (hist : List Bool) :
    Runs program 1 .seed (store ph [] [] hist [] []) .reverse (store ph [] [] hist [false] []) :=by
  apply one_base program .seed .reverse (.push (aux .output) false .reverse) _ _ rfl
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Complete actual allocation+reversal cost is linear in both physically materialized rank counters. -/
theorem allocate (ph : H.Stack→List Bool) (n r : Nat) :
    ∃time≤ 10*n+r+12,Runs program time .before (store ph (unary n) (unary r) [] [] []) .done
      (store ph [] [] [] (SemiprimeD1TensorTapeCodec.vectorBits (words n r (positive ph))) []) :=by
  obtain ⟨b,hb,h0⟩:=before_loop ph n r [] [] []
  simp only [List.append_nil] at h0
  have h1:=seed ph (bytes (words n r (positive ph))).reverse
  have h2:=reverse_call ph (bytes (words n r (positive ph))).reverse [false]
  simp only [List.reverse_reverse,bytes_vector] at h2
  have hh:=join (join h0 h1) h2
  have hlen:=bytes_length n r (positive ph)
  refine ⟨b+1+(2*(bytes (words n r (positive ph))).reverse.length+3),?_,hh⟩
  rw [List.length_reverse]
  omega
end RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshLoops
