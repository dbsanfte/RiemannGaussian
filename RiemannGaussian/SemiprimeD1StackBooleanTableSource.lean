/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BooleanRootTables
import RiemannGaussian.SemiprimeD1StackBytecodeBounds
/-! # Fixed literal finite-control acquisition of complete Boolean root tables
All 144 labels and their literal push bits are fixed BEFORE N. There is no
input table, predicate, coefficient getter or encoded output argument.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackBooleanTableSource
open SemiprimeD1StackBooleanEntry (Mode)
open SemiprimeD1BooleanRootTables (bytes bytes_length)
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
/-- One actual Boolean output stack; no hidden data registers. -/
abbrev Stack := Unit
/-- Fixed labels for the three literal programs, bounded by the 47-bit OR tape. -/
abbrev Label := Mode×Fin 48
/-- Every fixed local table fits the literal finite label inventory. -/
theorem bytes_le (mode : Mode) : (bytes mode).length≤47 := by cases mode <;> decide
/-- A literal finite push table. Indexing here is ONLY of fixed finite code
labels; it is not an instruction reading an input table or evaluating an entry. -/
def code (label : Label) : B.Instruction Stack Label :=
  if h : label.2.val<(bytes label.1).length then
    .push () (((bytes label.1).reverse[label.2.val]?).getD false)
      (label.1,⟨label.2.val+1,by have hb:=bytes_le label.1; omega⟩)
  else .halt
/-- Empty-data entry: there is NO supplied source/width/predicate/table answer. -/
def initial (mode : Mode) : B.State Stack Label := ⟨some (mode,0),none,fun _=>[]⟩
/-- Exact complete tagged-tree output. -/
def done (mode : Mode) : B.State Stack Label := ⟨none,none,fun _=>bytes mode⟩
/-- Every literal output bit is acquired by an actual executed push, plus halt. -/
theorem source_run (mode : Mode) :
    B.run code ((bytes mode).length+1) (initial mode)=some (done mode) := by
  cases mode <;> apply congrArg some <;> congr 1
/-- Actual fixed finite machine, with empty initial data and only literal output. -/
abbrev machine (mode : Mode) : Turing.FinTM2 :=
  SemiprimeD1StackBytecode.machine () () (mode,0) code
/-- Actual empty initialization, not a prepared encoded-tree answer. -/
theorem initial_eq (mode : Mode) :
    Turing.initList (machine mode) []=SemiprimeD1StackBytecode.configuration (initial mode) :=
  (SemiprimeD1StackBytecode.initial_correct () () (mode,0) code []).symm
/-- Genuine finite-alphabet acquisition in 48/12/24 transitions, no report premise. -/
def acquireInTime (mode : Mode) :
    StateTransition.EvalsToInTime (machine mode).step (Turing.initList (machine mode) [])
      (some (SemiprimeD1StackBytecode.configuration (done mode))) ((bytes mode).length+1) := by
  rw [initial_eq]
  apply SemiprimeD1StackBytecode.evalsCorrect () () (mode,0) code
  exact ⟨⟨(bytes mode).length+1,source_run mode⟩,Nat.le_refl _⟩
/-- Every actual source prefix has at most 48 Boolean payload cells. -/
theorem prefix_cells (mode : Mode) (fuel : ℕ) (out : B.State Stack Label)
    (hr : B.run code fuel (initial mode)=some out) : (out.store ()).length≤48 := by
  have hf:=SemiprimeD1StackBytecodeBounds.fuel_le_halt code (initial mode) (done mode) out
    ((bytes mode).length+1) fuel (source_run mode) rfl hr
  have hd:=SemiprimeD1StackBytecodeBounds.run_length code fuel (initial mode) out hr ()
  change (out.store ()).length≤0+fuel at hd
  have hb:=bytes_le mode
  omega
/-- ALL actual compiled-machine prefixes occupy at most 48 Boolean cells. -/
theorem machine_prefix_cells (mode : Mode) (fuel : ℕ) (cfg : (machine mode).Cfg)
    (hr : (fun q=>q.bind (machine mode).step)^[fuel]
      (some (Turing.initList (machine mode) []))=some cfg) : (cfg.stk ()).length≤48 := by
  have he:=SemiprimeD1StackBytecode.run_correct () () (mode,0) code fuel (initial mode)
  change (B.run code fuel (initial mode)).map SemiprimeD1StackBytecode.configuration=
    (fun q=>q.bind (machine mode).step)^[fuel]
      (some (SemiprimeD1StackBytecode.configuration (initial mode))) at he
  have hh : (B.run code fuel (initial mode)).map SemiprimeD1StackBytecode.configuration=some cfg :=
    he.trans ((congrArg (fun start:(machine mode).Cfg=>
      (fun q:Option (machine mode).Cfg=>q.bind (machine mode).step)^[fuel] (some start))
        (initial_eq mode).symm).trans hr)
  cases hrun:B.run code fuel (initial mode) with
  | none => rw [hrun] at hh; cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackBytecode.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells mode fuel out hrun

end RiemannGaussian.SemiprimeD1StackBooleanTableSource
