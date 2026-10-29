/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryEncoding
/-! # Real included arithmetic and preserving-copy recovery traces -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryPrimitives
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic SemiprimeBitDivision
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact actual fragment concatenation preserves all real outer return frames. -/
theorem join {m n : ℕ} {pc mid next : Label} {before between after : Stack→List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between next after) :
    Runs program (m+n) pc before next after := runs_trans program m n pc mid next before between after h g
/-- Actual preserving copy, including restoration of its borrowed dedicated scratch. -/
theorem copy_call (site : Copy) (pc next : Label)
    (hc : program pc=.call (copyLabel site 0) next)
    (before : Stack→List Bool) (xs ys : List Bool)
    (hx : before (copyStack site 0)=xs) (hy : before (copyStack site 1)=ys)
    (hs : before (copyStack site 2)=[]) :
    Runs program (5*xs.length+4) pc before next (Function.update before (copyStack site 1) (xs++ys)) := by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi : Link.DataRel (copyStack site) before start.store before := by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack site) (copy_injective site) before start.store before hi (1:Fin 3) (xs++ys)
  have he : Function.update start.store 1 (xs++ys)=stop.store := by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack site) (copyLabel site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _ => rfl) pc next hc (5*xs.length+3)
    start stop before _ rfl rfl (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Own real addition call clock, including its physical caller return. -/
def addTime (xs ys : List Bool) : ℕ := 3*(max xs.length ys.length+1)+2*(addBits xs ys false).bits.length+3
/-- Complete included addition, preserving every foreign physical word and real return. -/
theorem add_call (r m x w v u) (xs ys : List Bool) (pc finish : Label)
    (hc : program pc=.call (adderLabel (.start false)) finish) :
    Runs program (addTime xs ys) pc (view r m (A.store xs ys [] []) x w v u) finish (view r m (A.store [] [] [] (addBits xs ys false).bits) x w v u) := by
  let source:=SemiprimeD1StackAdder.state (some (.start false)) none xs ys [] []
  let stop:=SemiprimeD1StackAdder.state none none [] [] [] (addBits xs ys false).bits
  let before:=view r m (A.store xs ys [] []) x w v u
  let after:=view r m (A.store [] [] [] (addBits xs ys false).bits) x w v u
  have hi : Link.DataRel adder before source.store before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel adder before stop.store after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · rfl
      · rcases k with k|k|k|k|k
        · rfl
        · exact False.elim (hk k rfl)
        · rfl
        · rfl
        · rfl
      · rfl
  exact included_call program adder adderLabel (squareRoot_injective.comp SemiprimeD1StackBinarySquareRoot.adder_injective)
    A.code (.start false) (fun _ => rfl) pc finish hc _ source stop before after rfl rfl
    (SemiprimeD1StackAdderExecution.source_run xs ys false) hi ho
/-- Own real subtraction call clock, including its physical caller return. -/
def subtractTime (xs ys : List Bool) : ℕ := 3*(max xs.length ys.length+1)+2*(subBits xs ys false).result.bits.length+4
/-- Complete included subtraction, preserving every foreign physical word and real return. -/
theorem subtract_call (r m x w v u) (xs ys : List Bool) (pc finish : Label)
    (hc : program pc=.call (subtractLabel (.start false)) finish) :
    Runs program (subtractTime xs ys) pc (view r m (A.store xs ys [] []) x w v u) finish (view r m (A.store [] [] [] ((subBits xs ys false).borrow::(subBits xs ys false).result.bits)) x w v u) := by
  let source:=SemiprimeD1StackSubtractor.state (some (.start false)) none xs ys [] []
  let stop:=SemiprimeD1StackSubtractor.state none none [] [] [] ((subBits xs ys false).borrow::(subBits xs ys false).result.bits)
  let before:=view r m (A.store xs ys [] []) x w v u
  let after:=view r m (A.store [] [] [] ((subBits xs ys false).borrow::(subBits xs ys false).result.bits)) x w v u
  have hi : Link.DataRel adder before source.store before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel adder before stop.store after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · rfl
      · rcases k with k|k|k|k|k
        · rfl
        · exact False.elim (hk k rfl)
        · rfl
        · rfl
        · rfl
      · rfl
  exact included_call program adder subtractLabel (squareRoot_injective.comp SemiprimeD1StackBinarySquareRoot.adder_injective)
    SemiprimeD1StackSubtractor.code (.start false) (fun _ => rfl) pc finish hc _ source stop before after rfl rfl
    (SemiprimeD1StackSubtractorExecution.source_run xs ys false) hi ho
/-- Own real multiplication call clock, including its physical caller return. -/
def multiplyTime (xs ys : List Bool) : ℕ := 2*xs.length+1+SemiprimeD1StackMultiplierExecution.loopClock ys xs.reverse []+1
/-- Complete included multiplication, preserving every foreign physical word and real return. -/
theorem multiply_call (r m a w v u) (xs ys : List Bool) (pc finish : Label)
    (hc : program pc=.call (multiplyLabel (.control .start)) finish) :
    Runs program (multiplyTime xs ys) pc (view r m a (X.payload xs ys [] [] [] [] [] [] []) w v u) finish (view r m a (X.payload [] [] [] [] (mulBits xs ys).bits [] [] [] []) w v u) := by
  let source:=SemiprimeD1StackMultiplier.state (some (.control .start)) none none xs ys [] [] [] [] [] [] []
  let stop:=SemiprimeD1StackMultiplier.state none none none [] [] [] [] (mulBits xs ys).bits [] [] [] []
  let before:=view r m a (X.payload xs ys [] [] [] [] [] [] []) w v u
  let after:=view r m a (X.payload [] [] [] [] (mulBits xs ys).bits [] [] [] []) w v u
  have hi : Link.DataRel multiply before source.data before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel multiply before stop.data after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · rfl
      · rcases k with k|k|k|k|k
        · rfl
        · rfl
        · exact False.elim (hk k rfl)
        · rfl
        · rfl
      · rfl
  exact SemiprimeD1StackProcedureCallsTrace.included_call program multiply multiplyLabel (squareRoot_injective.comp SemiprimeD1StackBinarySquareRoot.multiply_injective)
    X.code (.control .start) (fun _ => rfl) pc finish hc _ source stop before after rfl rfl
    rfl rfl (SemiprimeD1StackMultiplierExecution.source_run xs ys) hi ho
/-- Own real comparison call clock, including its physical caller return. -/
def compareTime (xs ys : List Bool) : ℕ := SemiprimeD1StackWordLessExecution.totalTime xs ys+1
/-- Complete included comparison, preserving every foreign physical word and real return. -/
theorem compare_call (r m a x v u) (xs ys : List Bool) (pc finish : Label)
    (hc : program pc=.call (compareLabel .start) finish) :
    Runs program (compareTime xs ys) pc (view r m a x (W.store xs ys [] [] []) v u) finish (view r m a x (W.store [] [] [] [] [SemiprimeD1StackWordLessExecution.answer xs ys]) v u) := by
  let source:=SemiprimeD1StackWordLess.initial xs ys
  let stop:=SemiprimeD1StackWordLessExecution.done xs ys
  let before:=view r m a x (W.store xs ys [] [] []) v u
  let after:=view r m a x (W.store [] [] [] [] [SemiprimeD1StackWordLessExecution.answer xs ys]) v u
  have hi : Link.DataRel compare before source.data before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel compare before stop.data after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · rfl
      · rcases k with k|k|k|k|k
        · rfl
        · rfl
        · rfl
        · exact False.elim (hk k rfl)
        · rfl
      · rfl
  exact SemiprimeD1StackProcedureCallsTrace.included_call program compare compareLabel (squareRoot_injective.comp SemiprimeD1StackBinarySquareRoot.compare_injective)
    W.program .start (fun _ => rfl) pc finish hc _ source stop before after rfl rfl
    rfl rfl (SemiprimeD1StackWordLessExecution.source_run xs ys) hi ho
/-- One actual FALSE pop follows the literal matching branch and retains all foreign data. -/
theorem pop_false (pc finish other missing : Label) (k : Stack) (before : Stack→List Bool) (xs : List Bool)
    (hc : program pc=.base (.pop k missing finish other))
    (hx : before k=false::xs) :
    Runs program 1 pc before finish (Function.update before k xs) := by
  apply one_base program pc finish _ before _ hc
  · change some (SemiprimeD1StackBytecode.choose missing finish other (before k).head?)=some finish
    rw [hx]
    rfl
  · change Function.update before k (before k).tail=Function.update before k xs
    rw [hx]
    rfl
/-- One actual TRUE pop follows the literal matching branch and retains all foreign data. -/
theorem pop_true (pc finish other missing : Label) (k : Stack) (before : Stack→List Bool) (xs : List Bool)
    (hc : program pc=.base (.pop k missing other finish))
    (hx : before k=true::xs) :
    Runs program 1 pc before finish (Function.update before k xs) := by
  apply one_base program pc finish _ before _ hc
  · change some (SemiprimeD1StackBytecode.choose missing other finish (before k).head?)=some finish
    rw [hx]
    rfl
  · change Function.update before k (before k).tail=Function.update before k xs
    rw [hx]
    rfl
/-- An actual EOF pop still executes its physical empty-word update. -/
theorem pop_empty (pc finish low high : Label) (k : Stack) (before : Stack→List Bool)
    (hc : program pc=.base (.pop k finish low high)) (hx : before k=[]) :
    Runs program 1 pc before finish (Function.update before k []) := by
  apply one_base program pc finish _ before _ hc
  · change some (SemiprimeD1StackBytecode.choose finish low high (before k).head?)=some finish
    rw [hx]
    rfl
  · change Function.update before k (before k).tail=Function.update before k []
    rw [hx]
    rfl
/-- One literal bit push, charged as one actual transition. -/
theorem push_bit (pc finish : Label) (k : Stack) (bit : Bool) (before : Stack→List Bool)
    (hc : program pc=.base (.push k bit finish)) :
    Runs program 1 pc before finish (Function.update before k (bit::before k)) :=
  one_base program pc finish _ before _ hc rfl rfl
/-- Every actual cleanup pop is paid, including its final EOF pop. -/
theorem drain_call (pc finish : Label) (k : Stack) (before : Stack→List Bool) (xs : List Bool)
    (hc : program pc=.base (.pop k finish pc pc)) (hx : before k=xs) :
    Runs program (xs.length+1) pc before finish (Function.update before k []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program pc finish k hc before xs
  have he : Function.update before k xs=before := by rw [←hx];exact Function.update_eq_self _ _
  rw [he] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryPrimitives
