/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetSuffixCalls
import RiemannGaussian.SemiprimeD1StackRouteArithmetic

/-! # Actual parsing/reversal pass of original axis counters -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetSuffixPass
open SemiprimeD1StackJetSuffix SemiprimeD1StackJetSuffixCalls
open SemiprimeD1StackUnaryDivmod (unary unary_succ)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => SemiprimeD1StackJetSuffix.control

/-- Every literal data-bank projection is an actual fixed stack, not a getter oracle. -/
@[simp] theorem data_apply (axes reverseAxes axis radix product records scratch valid : List Bool) (k : Stack) :
    data axes reverseAxes axis radix product records scratch valid k=
      match k with
      | .axes => axes | .reverseAxes => reverseAxes | .axis => axis | .radix => radix
      | .product => product | .records => records | .scratch => scratch | .valid => valid := rfl

/-- Physical unary length is its original numeric value. -/
@[simp] theorem unary_length (q : ℕ) : (unary q).length=q := by simp [unary]

/-- Actual fixed-program trace concatenation. -/
theorem compose {m n : ℕ} {pc mid next : Label} {bank middle result : Stack → List Bool}
    (h : Trace.Runs code m pc bank mid middle) (g : Trace.Runs code n mid middle next result) :
    Trace.Runs code (m+n) pc bank next result :=
  Trace.runs_trans code m n pc mid next bank middle result h g

/-- Consume one actual nonterminal vector marker. -/
theorem vector_true (tail reverseAxes radix product records : List Bool) :
    Trace.Runs code 1 (ctl .vector) (data (true::tail) reverseAxes [] radix product records [] [])
      (ctl .readAxis) (data tail reverseAxes [] radix product records [] []) := by
  apply Trace.one_base code (ctl .vector) (ctl .readAxis)
    (.pop .axes (ctl (.fail 0)) (ctl .startSuffix) (ctl .readAxis)) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
  · simp [SemiprimeD1StackBytecode.execute]

/-- The acquired field's actual true-validity cell is consumed before use. -/
theorem axis_flag (axes reverseAxes word radix product records : List Bool) :
    Trace.Runs code 1 (ctl .axisRead) (data axes reverseAxes word radix product records [] [true])
      (ctl .positive) (data axes reverseAxes word radix product records [] []) := by
  apply Trace.one_base code (ctl .axisRead) (ctl .positive)
    (.pop .valid (ctl (.fail 0)) (ctl (.fail 0)) (ctl .positive)) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
  · simp [SemiprimeD1StackBytecode.execute]

/-- Original positivity discharges the actual empty-counter guard, not a supplied test answer. -/
theorem axis_positive (q : ℕ) (hq : 0<q) (axes reverseAxes radix product records : List Bool) :
    Trace.Runs code 1 (ctl .positive) (data axes reverseAxes (unary q) radix product records [] [])
      (ctl .reverseFrame) (data axes reverseAxes (unary q) radix product records [] []) := by
  apply Trace.one_base code (ctl .positive) (ctl .reverseFrame)
    (.peek .axis (ctl (.fail 0)) (ctl .reverseFrame) (ctl .reverseFrame)) _ _ rfl
  · cases q with
    | zero => omega
    | succ q => simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,unary_succ]
  · rfl

/-- Every parsed original counter cell is physically cleared after framing. -/
theorem clear_axis (word axes reverseAxes radix product records : List Bool) :
    Trace.Runs code (word.length+1) (ctl .clearAxis)
      (data axes reverseAxes word radix product records [] [])
      (ctl .vector) (data axes reverseAxes [] radix product records [] []) := by
  induction word with
  | nil =>
    apply Trace.one_base code (ctl .clearAxis) (ctl .vector)
      (.pop .axis (ctl .vector) (ctl .clearAxis) (ctl .clearAxis)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
    · simp [SemiprimeD1StackBytecode.execute]
  | cons b bs ih =>
    have hs : Trace.Runs code 1 (ctl .clearAxis)
        (data axes reverseAxes (b::bs) radix product records [] [])
        (ctl .clearAxis) (data axes reverseAxes bs radix product records [] []) := by
      apply Trace.one_base code (ctl .clearAxis) (ctl .clearAxis)
        (.pop .axis (ctl .vector) (ctl .clearAxis) (ctl .clearAxis)) _ _ rfl
      · cases b <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
      · simp [SemiprimeD1StackBytecode.execute]
    have h := compose hs ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- One original positive axis is read, checked, framed and cleared by actual calls. -/
theorem one_axis (q : ℕ) (hq : 0<q) (tail reverseAxes radix product records : List Bool) :
    Trace.Runs code (15*q+16) (ctl .vector)
      (data (true::frame (unary q) tail) reverseAxes [] radix product records [] [])
      (ctl .vector) (data tail (frame (unary q) reverseAxes) [] radix product records [] []) := by
  have h1 := vector_true (frame (unary q) tail) reverseAxes radix product records
  have h2 := axes_read (unary q) tail reverseAxes radix product records
  have h3 := axis_flag tail reverseAxes (unary q) radix product records
  have h4 := axis_positive q hq tail reverseAxes radix product records
  have h5 := reverse_frame tail reverseAxes (unary q) radix product records
  have h6 := clear_axis (unary q) tail (frame (unary q) reverseAxes) radix product records
  have h := compose h1 (compose h2 (compose h3 (compose h4 (compose h5 h6))))
  simp only [unary_length] at h
  rw [show 1+(8*q+7+(1+(1+(6*q+5+(q+1)))))=15*q+16 by omega] at h
  exact h

/-- Pure specification of the ACTUALLY acquired reverse field stream. -/
def reverseFields : List ℕ → List Bool → List Bool
  | [],acc => acc
  | q::qs,acc => reverseFields qs (frame (unary q) acc)

/-- Full first pass is actual input parsing and copying, not a supplied reversed array. -/
theorem first_pass (axes : List ℕ) (hp : ∀q∈axes,0<q) (acc radix product records : List Bool) :
    Trace.Runs code (15*axes.sum+16*axes.length+1) (ctl .vector)
      (data (vectorBits (axes.map unary)) acc [] radix product records [] [])
      (ctl .startSuffix) (data [] (reverseFields axes acc) [] radix product records [] []) := by
  induction axes generalizing acc with
  | nil =>
    apply Trace.one_base code (ctl .vector) (ctl .startSuffix)
      (.pop .axes (ctl (.fail 0)) (ctl .startSuffix) (ctl .readAxis)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,vectorBits]
    · simp [SemiprimeD1StackBytecode.execute,vectorBits,reverseFields]
  | cons q qs ih =>
    have hq := hp q (by simp)
    have ht := ih (fun v hv => hp v (by simp [hv])) (frame (unary q) acc)
    have hs := one_axis q hq (vectorBits (qs.map unary)) acc radix product records
    have h := compose hs ht
    change Trace.Runs code (15*q+16+(15*qs.sum+16*qs.length+1)) _ _ _ _ at h
    have he : 15*q+16+(15*qs.sum+16*qs.length+1)=15*(q::qs).sum+16*(q::qs).length+1 := by
      simp only [List.sum_cons,List.length_cons]
      omega
    rw [he] at h
    exact h

/-- The acquired reverse-field validity cell is consumed, rather than read as advice. -/
theorem reverse_flag (axes reverseAxes word radix product records : List Bool) :
    Trace.Runs code 1 (ctl .reverseRead)
      (data axes reverseAxes word radix product records [] [true])
      (ctl .frameRadix) (data axes reverseAxes word radix product records [] []) := by
  apply Trace.one_base code (ctl .reverseRead) (ctl .frameRadix)
    (.pop .valid (ctl (.fail 0)) (ctl (.fail 0)) (ctl .frameRadix)) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
  · simp [SemiprimeD1StackBytecode.execute]

/-- The previous suffix product is physically erased before replacement. -/
theorem clear_radix (word axes reverseAxes product records : List Bool) :
    Trace.Runs code (word.length+1) (ctl .clearRadix)
      (data axes reverseAxes [] word product records [] [])
      (ctl .moveProduct) (data axes reverseAxes [] [] product records [] []) := by
  induction word with
  | nil =>
    apply Trace.one_base code (ctl .clearRadix) (ctl .moveProduct)
      (.pop .radix (ctl .moveProduct) (ctl .clearRadix) (ctl .clearRadix)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
    · simp [SemiprimeD1StackBytecode.execute]
  | cons b bs ih =>
    have hs : Trace.Runs code 1 (ctl .clearRadix)
        (data axes reverseAxes [] (b::bs) product records [] [])
        (ctl .clearRadix) (data axes reverseAxes [] bs product records [] []) := by
      apply Trace.one_base code (ctl .clearRadix) (ctl .clearRadix)
        (.pop .radix (ctl .moveProduct) (ctl .clearRadix) (ctl .clearRadix)) _ _ rfl
      · cases b <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
      · simp [SemiprimeD1StackBytecode.execute]
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using compose hs ih

/-- Moving the newly executed product is an actual pop/push loop. -/
theorem move_product (n : ℕ) (axes reverseAxes radix records : List Bool) :
    Trace.Runs code (2*n+1) (ctl .moveProduct)
      (data axes reverseAxes [] radix (unary n) records [] [])
      (ctl .suffixPeek) (data axes reverseAxes [] (unary n++radix) [] records [] []) := by
  induction n generalizing radix with
  | zero =>
    apply Trace.one_base code (ctl .moveProduct) (ctl .suffixPeek)
      (.pop .product (ctl .suffixPeek) (ctl .movePush) (ctl .movePush)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,unary]
    · simp [SemiprimeD1StackBytecode.execute,unary]
  | succ n ih =>
    have hp : Trace.Runs code 1 (ctl .moveProduct)
        (data axes reverseAxes [] radix (unary (n+1)) records [] [])
        (ctl .movePush) (data axes reverseAxes [] radix (unary n) records [] []) := by
      apply Trace.one_base code (ctl .moveProduct) (ctl .movePush)
        (.pop .product (ctl .suffixPeek) (ctl .movePush) (ctl .movePush)) _ _ rfl
      · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,unary_succ]
      · simp [SemiprimeD1StackBytecode.execute,unary_succ]
    have hq : Trace.Runs code 1 (ctl .movePush)
        (data axes reverseAxes [] radix (unary n) records [] [])
        (ctl .moveProduct) (data axes reverseAxes [] (true::radix) (unary n) records [] []) := by
      apply Trace.one_base code (ctl .movePush) (ctl .moveProduct)
        (.push .radix true (ctl .moveProduct)) _ _ rfl
      · rfl
      · simp [SemiprimeD1StackBytecode.execute]
    have h := compose hp (compose hq (ih (true::radix)))
    rw [show 1+(1+(2*n+1))=2*(n+1)+1 by omega] at h
    simpa only [SemiprimeD1StackUnaryDivmod.unary_bump,unary_succ,List.cons_append] using h

end RiemannGaussian.SemiprimeD1StackJetSuffixPass
