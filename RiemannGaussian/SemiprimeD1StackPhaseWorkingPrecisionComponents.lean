/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionShifts
/-! # Closed binary working-precision join from the actually acquired metadata cache -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionComponents
open SemiprimeD1StackPhaseWorkingPrecision SemiprimeD1StackPhaseWorkingPrecisionArithmetic
open SemiprimeD1StackPhaseWorkingPrecisionPrimitives SemiprimeD1StackProcedureTrace
/-- Exact actual complete37-role acquired cache, not a runtime answer supplier. -/
def old (a u edges : Nat) (t p : List Bool) : M.Stack→List Bool :=
  SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.result a u edges t p
/-- Exact actual acquired guard value, described only for the semantic/source proof. -/
abbrev accepted :=SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives.accepted
/-- Exact actual height acquired by real unary division. -/
abbrev height :=SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic.height
/-- Exact actual original dyadic order acquired by the real geometry source. -/
abbrev order :=SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives.order
/-- Exact acquired a-i shift count. -/
def delta (a : Nat) (t : List Bool) : Nat :=a-order a t
/-- Exact acquired bounded product for the second precision term. -/
def product (a edges : Nat) : Nat :=edges*(a+1)
/-- Empty fresh binary bank atop the ACTUALLY acquired cache. -/
def clean (a u edges : Nat) (t p : List Bool) : Stack→List Bool :=data (old a u edges t p) [] [] [] [] [] [] [] [] []
/-- Final BINARY P/D, with every other new physical field clear and all37 old fields retained. -/
def result (a u edges : Nat) (t p : List Bool) : Stack→List Bool :=
  data (old a u edges t p) [] []
    (if accepted a u t then precisionWord (height edges u) (product a edges) (delta a t) p else [])
    [] [] [] [] [] (if accepted a u t then shift (delta a t) [true] else [])
/-- Own ready clock counts every actual conversion/shift/adder instruction. -/
def readyBound (a u edges : Nat) (t p : List Bool) : Nat :=1000000000*(edges+a+u+t.length+p.length+1)^4
/-- The old cache has the exact REAL acquired height word, not a caller-provided h. -/
theorem height_word (a u edges : Nat) (t p : List Bool) (ha : accepted a u t=true) :
    old a u edges t p (M.divStack .quotient)=List.replicate (height edges u) true :=by
  simp only [old,SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.result,
    SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.resultCounts,ha,ite_true]
  rfl
/-- The old bounded product word comes from the actual whole UnaryProduct trace. -/
theorem product_word (a u edges : Nat) (t p : List Bool) (ha : accepted a u t=true) :
    old a u edges t p (M.aux .r)=List.replicate (product a edges) true :=by
  simp only [old,SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.result,
    SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.resultCounts,ha,ite_true]
  rfl
/-- The old shift count comes from actual physical subtraction of acquired i from original a. -/
theorem delta_word (a u edges : Nat) (t p : List Bool) (ha : accepted a u t=true) :
    old a u edges t p (M.aux .delta)=List.replicate (delta a t) true :=by
  simp only [old,SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.result,
    SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.resultCounts,ha,ite_true]
  rfl
/-- Arbitrary original precision remains its IDENTICAL BINARY word. -/
theorem precision_word (a u edges : Nat) (t p : List Bool) :old a u edges t p (M.aux .precision)=p :=rfl
/-- The ready verdict is read PHYSICALLY from the actual retained guard singleton. -/
theorem branch_run (a u edges : Nat) (t p : List Bool) :
    Runs program 1 .branch (clean a u edges t p)
      (if accepted a u t then .copyZero false else .done) (clean a u edges t p) :=by
  apply one_base program .branch _ (.peek (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .output)))
    .done .done (.copyZero false)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.done Label.done (Label.copyZero false)
      ([accepted a u t].head?))=some _
    cases accepted a u t <;> rfl
  · rfl
/-- Actual binary h/r conversions, shifts and two adders close the ENTIRE accepted precision source. -/
theorem accepted_run (a u edges : Nat) (t p : List Bool) (ha : accepted a u t=true) :
    ∃q,q+2≤ readyBound a u edges t p ∧ Runs program q (.copyZero false) (clean a u edges t p)
      .done (result a u edges t p) :=by
  let cache:=old a u edges t p
  let h:=height edges u
  let r:=product a edges
  let d:=delta a t
  obtain ⟨b,hb,h0⟩:=SemiprimeD1StackPhaseWorkingPrecisionConvert.source_run false cache [] [] h (height_word a u edges t p ha)
  have h1:=SemiprimeD1StackPhaseWorkingPrecisionShifts.left_run cache h d p
    (delta_word a u edges t p ha) (precision_word a u edges t p)
  have h2:=adder_call false cache (heightTerm h d) p (shift d [true])
  obtain ⟨c,hc,h3⟩:=SemiprimeD1StackPhaseWorkingPrecisionConvert.source_run true cache
    (partialWord h d p) (shift d [true]) r (product_word a u edges t p ha)
  have h4:=SemiprimeD1StackPhaseWorkingPrecisionShifts.right_run cache r (partialWord h d p) (shift d [true])
  have h5:=adder_call true cache (partialWord h d p) (productTerm r) (shift d [true])
  have hh:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  refine ⟨_,?_,by simpa only [result,ha,ite_true,clean,precisionWord] using hh⟩
  let I:=edges+a+u+t.length+p.length+1
  have hI:1≤ I:=by dsimp [I];omega
  have hI2:I≤ I^2:=Nat.le_pow (by decide : 0<(2:Nat))
  have hI4:I^2≤ I^4:=by
    calc
      _≤(I^2)^2:=Nat.le_pow (by decide : 0<(2:Nat))
      _=_:=by ring
  have haI:a+1≤ I:=by dsimp [I];omega
  have heI:edges≤ I:=by dsimp [I];omega
  have hpI:p.length≤ I:=by dsimp [I];omega
  have hdI:d≤ I:=by dsimp [d,delta];omega
  have hhI:h≤4*I:=by
    have hH:h≤3*edges+u:=SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic.height_le edges u
    dsimp [I]
    omega
  have hrI:r≤ I^2:=by
    calc
      _=edges*(a+1):=rfl
      _≤ I*I:=Nat.mul_le_mul heI haI
      _=_:=by ring
  have hHpow:(h+1)^2≤25*I^2:=by
    calc
      _≤(5*I)^2:=Nat.pow_le_pow_left (by omega) 2
      _=_:=by ring
  have hRpow:(r+1)^2≤4*I^4:=by
    calc
      _≤(2*I^2)^2:=Nat.pow_le_pow_left (by omega) 2
      _=_:=by ring
  have hb':b≤5000*I^2:=by omega
  have hc':c≤800*I^4:=by omega
  have hlH:(heightTerm h d).length≤9*I:=by
    rw [heightTerm,shift_length,shift_length,counterWord_length]
    omega
  have hlR:(productTerm r).length≤5*I^2:=by
    rw [productTerm,shift_length,counterWord_length]
    omega
  have hlP:(partialWord h d p).length≤11*I:=by
    have ht:=partialWord_length h d p
    omega
  have hA:=adder_time_le (heightTerm h d) p
  have hB:=adder_time_le (partialWord h d p) (productTerm r)
  change _≤1000000000*I^4
  omega
/-- Whole ready trace continues DIRECTLY from the actual acquired37-role cache. -/
theorem ready_trace (a u edges : Nat) (t p : List Bool) :
    ∃q,q+1≤ readyBound a u edges t p ∧ Runs program q .branch (clean a u edges t p) .done (result a u edges t p) :=by
  have h0:=branch_run a u edges t p
  cases ha:accepted a u t with
  | false=>
    rw [ha] at h0
    refine ⟨1,?_,?_⟩
    · unfold readyBound
      have hp:0<(edges+a+u+t.length+p.length+1)^4:=by positivity
      omega
    · simpa only [clean,result,ha,Bool.false_eq_true,ite_false] using h0
  | true=>
    rw [ha] at h0
    obtain ⟨b,hb,h1⟩:=accepted_run a u edges t p ha
    exact ⟨1+b,by omega,join h0 h1⟩
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionComponents
