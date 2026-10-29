/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeTreeExecution

/-! # Primitive transition and Boolean-cell bounds for actual tree lookup
The input is an actual well-formed serialized table followed by an arbitrary
suffix, with an already prepared Boolean path stack. Serialization and preparation
of that path remain separate operations; no whole-controller machine is claimed.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TensorTapeTreeBounds
open Turing Turing.TM2
open SemiprimeD1TensorTapeTreeMachine SemiprimeD1TensorTapeTreeExecution
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1TensorTables (Table lookup)

/-- Every stack, including the auxiliary task/path stacks, has two symbols. -/
theorem alphabet_card (k : Stack) : Fintype.card (Alphabet k)=2 := by
  change Fintype.card Bool=2
  decide

/-- Fixed finite register space, independent of every input dimension. -/
theorem registers_card : Fintype.card Registers=6 := by decide

/-- Fixed finite control-label space. -/
theorem labels_card : Fintype.card PC=8 := by decide

/-- The five stack indices are fixed before all input dimensions. -/
theorem stacks_card : Fintype.card Stack=5 := by decide

/-- Static instruction depth includes every nested push/pop/control instruction. -/
def instructionDepth : Stmt Alphabet PC Registers → ℕ
  | .push _ _ q => 1+instructionDepth q
  | .peek _ _ q => 1+instructionDepth q
  | .pop _ _ q => 1+instructionDepth q
  | .load _ q => 1+instructionDepth q
  | .branch _ q r => 1+max (instructionDepth q) (instructionDepth r)
  | .goto _ => 1
  | .halt => 1

/-- A TM2 label contains at most eight elementary stack/control instructions. -/
theorem program_depth (pc : PC) : instructionDepth (program pc)≤8 := by
  cases pc <;> decide

/-- All jumps stay within the same fixed finite control catalogue. -/
theorem program_supports : TM2.Supports program Finset.univ := by
  constructor
  · simp
  · intro pc hpc
    cases pc <;> simp [program,copyThen,forkTasks,TM2.SupportsStmt]

/-- Both subtree scans have a linear bound in the actual literal tape length. -/
theorem scanSteps_le {n : ℕ} (table : Table n) : scanSteps table≤3*(tape table).length := by
  induction table with
  | leaf ws => simp only [scanSteps,tape,List.length_cons]; omega
  | fork low high hl hh =>
    simp only [scanSteps,tape,List.length_cons,List.length_append]
    omega

/-- The selected vector is literally contained in the serialized table. -/
theorem selected_length_le {n : ℕ} (table : Table n) (path : List Bool) :
    (vectorBits (lookup table path).words).length≤(tape table).length := by
  induction table generalizing path with
  | leaf ws => simp [lookup,SemiprimeD1JetAxes.copyVector_value,tape]
  | fork low high hl hh =>
    have hlow := hl path.tail
    have hhigh := hh path.tail
    simp only [lookup,tape,List.length_cons,List.length_append]
    split_ifs <;> omega

/-- Start by acquiring the one initial seek task on its actual data stack. -/
theorem start_step (xs path : List Bool) :
    step (cfg (some .start) (none,false) xs [] path [] [])=
      some (cfg (some .task) (none,false) xs [true] path [] []) := by
  simp [SemiprimeD1TensorTapeTreeMachine.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- Full prepared-path execution, including initial task acquisition and final copy. -/
theorem prepared_exec {n : ℕ} (table : Table n) (path tail : List Bool) :
    Executes (scanSteps table+(vectorBits (lookup table path).words).length+3)
      (cfg (some .start) (none,false) (tape table++tail) [] path [] [])
      (cfg none (none,false) tail [] (path.drop n) [] (vectorBits (lookup table path).words)) := by
  have h := Executes.next (start_step (tape table++tail) path) (lookup_exec table path tail)
  convert h using 1

/-- Actual finite-machine transition-time certificate, uniform over all depths. -/
def lookupInTime {n : ℕ} (table : Table n) (path tail : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .start) (none,false) (tape table++tail) [] path [] [])
      (some (cfg none (none,false) tail [] (path.drop n) []
        (vectorBits (lookup table path).words))) (4*(tape table).length+3) := by
  have h := prepared_exec table path tail
  have ht := scanSteps_le table
  have hv := selected_length_le table path
  refine ⟨⟨_,h.iterates⟩,?_⟩
  change scanSteps table+(vectorBits (lookup table path).words).length+3≤4*(tape table).length+3
  omega

/-- The bundled one-input machine initializes an empty path (the all-low default). -/
theorem init_eq (xs : List Bool) : Turing.initList machine xs=
    cfg (some .start) (none,false) xs [] [] [] [] := by
  unfold Turing.initList cfg
  dsimp only [machine]
  congr 1
  funext k
  cases k <;> rfl

/-- Official bundled initialization has the exact low-default lookup semantics. -/
def bundledInTime {n : ℕ} (table : Table n) (tail : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine (tape table++tail))
      (some (cfg none (none,false) tail [] [] [] (vectorBits (lookup table []).words)))
      (4*(tape table).length+3) := by
  rw [init_eq]
  simpa using lookupInTime table [] tail

/-- Explicit all-stack Boolean payload, including pending subtree tasks. -/
def cells (c : Cfg Alphabet PC Registers) : ℕ :=
  (c.stk Stack.input).length+(c.stk Stack.tasks).length+(c.stk Stack.path).length+
    (c.stk Stack.scratch).length+(c.stk Stack.output).length

/-- Every actual fixed instruction can push at most two Boolean data symbols. -/
theorem step_cells (c d : Cfg Alphabet PC Registers) (h : step c=some d) :
    cells d≤cells c+2 := by
  rcases c with ⟨pc,⟨flag,mode⟩,store⟩
  cases pc with
  | none => simp [SemiprimeD1TensorTapeTreeMachine.step,TM2.step] at h
  | some pc =>
    cases mode <;> cases pc <;>
      simp [SemiprimeD1TensorTapeTreeMachine.step,TM2.step,program,copyThen,
        forkTasks,TM2.stepAux,Bool.cond_eq_ite,Function.update] at h <;>
      (try split_ifs at h) <;> cases h <;> simp [cells,Function.update] <;> omega

/-- Every visited execution prefix has a bound on all its unbounded state. -/
theorem path_cells {n : ℕ} {c d : Cfg Alphabet PC Registers} (h : Executes n c d) :
    cells d≤cells c+2*n := by
  induction h with
  | refl => omega
  | @next n c e d hs ht ih =>
    have hh := step_cells c e hs
    omega

/-- Every lookup-prefix configuration has linear Boolean storage in tape and path. -/
theorem lookup_cells {n : ℕ} (table : Table n) (path tail : List Bool)
    (k : ℕ) (c : Cfg Alphabet PC Registers)
    (h : Executes k (cfg (some .start) (none,false) (tape table++tail) [] path [] []) c)
    (hk : k≤4*(tape table).length+3) :
    cells c≤9*(tape table).length+tail.length+path.length+6 := by
  have hh := path_cells h
  simp only [cells,cfg,contents,List.length_append,List.length_nil,Nat.add_zero] at hh
  unfold cells
  omega

end RiemannGaussian.SemiprimeD1TensorTapeTreeBounds
