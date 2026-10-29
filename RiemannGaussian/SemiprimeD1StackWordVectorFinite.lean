/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordVectorBounds
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Original word-before-bit finite assignment order, physically acquired
The original graph uses finProdFinEquiv to flatten word and bit indices. This
identifies that exact order with the completed actual word-vector machine and
its LINEAR clock/storage, including every retained suffix and both caches.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordVectorFinite
open SemiprimeD1StackWordVector SemiprimeD1StackWordVectorSpec

/-- The exact first k original word-before-bit blocks of one finite assignment.
This is a correctness specification, never a grouping input to the program. -/
def words (width : List Bool) {n k : ℕ} (hk : k ≤ n) (input : Fin (n*width.length)→Bool) : List (List Bool) :=
  List.ofFn (fun j : Fin k=>List.ofFn (fun b : Fin width.length=>
    input (finProdFinEquiv (⟨j.val,Nat.lt_of_lt_of_le j.isLt hk⟩,b))))

/-- An actual raw source block has the exact graph's original finite-product
coordinate order, including every original high zero bit. -/
theorem block_ofFn (width : List Bool) {n : ℕ} (input : Fin (n*width.length)→Bool) (j : Fin n) :
    ((List.ofFn input).drop (j.val*width.length)).take width.length=
      List.ofFn (fun b : Fin width.length=>input (finProdFinEquiv (j,b))) := by
  have hb:=Nat.mul_le_mul_right width.length (show j.val+1 ≤ n by omega)
  rw [Nat.add_mul,Nat.one_mul] at hb
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro i hi hi'
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

/-- Every physically emitted indexed block equals its original finite word;
no original word value or getter is an execution premise. -/
theorem blocks_ofFn (width : List Bool) {n k : ℕ} (hk : k ≤ n) (input : Fin (n*width.length)→Bool) :
    blocks width k (List.ofFn input)=words width hk input := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j<k
  · have hfull : k*width.length ≤ (List.ofFn input).length := by
      rw [List.length_ofFn]
      exact Nat.mul_le_mul_right width.length hk
    rw [blocks_get_take width k (List.ofFn input) j hj hfull]
    simp only [words,List.getElem?_ofFn,hj,dite_eq_left]
    exact congrArg some (block_ofFn width input ⟨j,by omega⟩)
  · have hnone : (blocks width k (List.ofFn input)).length ≤ j := by
      rw [blocks_length]
      omega
    rw [List.getElem?_eq_none hnone]
    simp [words,hj]

/-- Exact original finite-assignment output, with its whole original input,
physical caches and unread suffix retained as in the actual source machine. -/
def finiteDone (width count : List Bool) {n k : ℕ} (hk : k ≤ n) (input : Fin (n*width.length)→Bool) :
    C.State Stack Label :=
  ⟨none,none,none,store (List.ofFn input) ((List.ofFn input).drop (count.length*width.length))
    width count [] [] [] (SemiprimeD1TensorTapeCodec.vectorBits (words width hk input)),[]⟩
/-- The full actual source halt is the original graph-ordered finite word family. -/
theorem done_original (width count : List Bool) {n k : ℕ} (hk : k ≤ n)
    (input : Fin (n*width.length)→Bool) (hcount : count.length=k) :
    SemiprimeD1StackWordVectorExecution.done (List.ofFn input) width count=finiteDone width count hk input := by
  unfold SemiprimeD1StackWordVectorExecution.done SemiprimeD1StackWordVectorExecution.result finiteDone
  rw [hcount,blocks_ofFn width hk input]

/-- Genuine original finite-assignment acquisition in LINEAR bit time. The
physical count representation and raw bit order are identified, not advised. -/
noncomputable def machineAcquirePrefix (width count : List Bool) {n k : ℕ} (hk : k ≤ n)
    (input : Fin (n*width.length)→Bool) (hcount : count.length=k) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.ofFn input) width count))
      (some (SemiprimeD1StackCalls.configuration (finiteDone width count hk input)))
      (200*SemiprimeD1StackWordVectorBounds.inputSize (List.ofFn input) width count) := by
  have hfull : count.length*width.length ≤ (List.ofFn input).length := by
    rw [hcount,List.length_ofFn]
    exact Nat.mul_le_mul_right width.length hk
  have h:=SemiprimeD1StackWordVectorBounds.machineAcquireLinear (List.ofFn input) width count hfull
  rw [done_original width count hk input hcount] at h
  exact h

/-- Every actual prefix of the same original finite-assignment acquisition has
LINEAR total storage, counting original input/suffix/caches/output/real returns. -/
theorem machine_prefix_linear (width count : List Bool) {n k : ℕ} (hk : k ≤ n)
    (input : Fin (n*width.length)→Bool) (hcount : count.length=k) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (List.ofFn input) width count)))=some cfg) :
    (∑s : Stack,(cfg.stk (some s)).length)+(cfg.stk none).length ≤
      3000*SemiprimeD1StackWordVectorBounds.inputSize (List.ofFn input) width count := by
  apply SemiprimeD1StackWordVectorBounds.machine_prefix_cells_linear (List.ofFn input) width count _ fuel cfg hr
  rw [hcount,List.length_ofFn]
  exact Nat.mul_le_mul_right width.length hk

end RiemannGaussian.SemiprimeD1StackWordVectorFinite
