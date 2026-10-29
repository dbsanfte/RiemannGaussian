/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDescriptorRecordExecution
/-! # Complete loader-to-record clock and every physical source/return prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackDescriptorRecordBounds
open SemiprimeD1StackDescriptorRecord SemiprimeD1StackDescriptorRecordExecution
open SemiprimeD1StackDescriptorRecordLoadView
open SemiprimeD1StackStaticTableSpec (CheckerTrace)
open SemiprimeD1TensorTapeCodec (vectorBits)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
/-- Sum of ALL actual initial physical words, including old template bytes. -/
def inputSize (oldTemplate : K→List Bool) (fields : Fin 6→List Bool) (bank hist out : List Bool) : Nat :=
  inventory (initial s oldTemplate fields bank hist out).data
/-- Same full source clock: actual dirty-template load, concrete checker-table
clock, physical scope conversion and every literal tensor framing byte. -/
def runBound (oldTemplate : K→List Bool) (fields : Fin 6→List Bool) (words : List (List Bool))
    (budget : Nat→Nat) (M : Nat) (hist out : List Bool) : Nat :=
  prepareBound s oldTemplate fields (vectorBits words) hist out+
    SemiprimeD1StackStaticTableBounds.runBound s (selected sourceMap fields) words budget+
    110*(words.length+1)*(M+1)+21*2^words.length+22
omit [DecidableEq K] in
/-- The complete actual source's own bit clock; no native bound is transported. -/
theorem timeBound_le (oldTemplate : K→List Bool) (fields : Fin 6→List Bool) (words : List (List Bool))
    (answer : List Bool→Bool) (budget : Nat→Nat) (M : Nat) (hist out : List Bool)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound s sourceMap oldTemplate fields words answer budget hist out≤
      runBound s sourceMap oldTemplate fields words budget M hist out := by
  have h:=SemiprimeD1StackStaticRecordClock.timeBound_le s (selected sourceMap fields) words answer budget M hl hv
  unfold timeBound runBound
  omega
/-- A successful actual whole-source halt bounds every successful prefix. -/
theorem prefix_fuel_le (oldTemplate : K→List Bool) (fields : Fin 6→List Bool)
    (hraw : selected sourceMap fields s.raw=[]) (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (selected sourceMap fields) answer budget) (words : List (List Bool)) (hist out : List Bool)
    (fuel : Nat) (finish : C.State (Stack K) (Label L s.roles.length))
    (hr : C.run (program s sourceMap) fuel (initial s oldTemplate fields (vectorBits words) hist out)=some finish) :
    fuel≤timeBound s sourceMap oldTemplate fields words answer budget hist out := by
  obtain ⟨t,ht,he⟩:=source_run s sourceMap oldTemplate fields hraw answer budget hc words hist out
  have hf:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run (program s sourceMap) 1 (done s sourceMap fields words answer hist out)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every2K+35 actual Boolean data role, all shadows, six source fields,
loader scratch and every actual nested return cell at EVERY reached prefix. -/
theorem prefix_cells (oldTemplate : K→List Bool) (fields : Fin 6→List Bool)
    (hraw : selected sourceMap fields s.raw=[]) (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (selected sourceMap fields) answer budget) (words : List (List Bool)) (hist out : List Bool)
    (fuel : Nat) (finish : C.State (Stack K) (Label L s.roles.length))
    (hr : C.run (program s sourceMap) fuel (initial s oldTemplate fields (vectorBits words) hist out)=some finish) :
    (∑k:Stack K,(finish.data k).length)+finish.frames.length≤
      (2*Fintype.card K+36)*(inputSize s oldTemplate fields (vectorBits words) hist out+
        timeBound s sourceMap oldTemplate fields words answer budget hist out+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound (program s sourceMap) fuel
    (inputSize s oldTemplate fields (vectorBits words) hist out) _ finish
    (cell_le (initial s oldTemplate fields (vectorBits words) hist out).data) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound (program s sourceMap) fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hs:(∑k:Stack K,(finish.data k).length)≤
      (2*Fintype.card K+35)*(inputSize s oldTemplate fields (vectorBits words) hist out+fuel):=by
    calc
      _≤∑_k:Stack K,(inputSize s oldTemplate fields (vectorBits words) hist out+fuel):=
        Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le s sourceMap oldTemplate fields hraw answer budget hc words hist out fuel finish hr
  nlinarith
/-- Same complete bound for the genuine compiled finite machine itself. -/
theorem machine_prefix_cells [Fintype L] (oldTemplate : K→List Bool) (fields : Fin 6→List Bool)
    (hraw : selected sourceMap fields s.raw=[]) (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (selected sourceMap fields) answer budget) (words : List (List Bool)) (hist out : List Bool)
    (fuel : Nat) (cfg : (machine s sourceMap).Cfg)
    (hr : (fun q=>q.bind (machine s sourceMap).step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial s oldTemplate fields (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack K,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      (2*Fintype.card K+36)*(inputSize s oldTemplate fields (vectorBits words) hist out+
        timeBound s sourceMap oldTemplate fields words answer budget hist out+1) := by
  have he:=SemiprimeD1StackCalls.run_correct original output (.inl .start) (program s sourceMap) fuel
    (initial s oldTemplate fields (vectorBits words) hist out)
  have hh:(C.run (program s sourceMap) fuel (initial s oldTemplate fields (vectorBits words) hist out)).map
    SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run (program s sourceMap) fuel (initial s oldTemplate fields (vectorBits words) hist out) with
  | none=>rw [hrun] at hh;cases hh
  | some finish=>
    rw [hrun] at hh
    have heq:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells s sourceMap oldTemplate fields hraw answer budget hc words hist out fuel finish hrun
/-- All actual Boolean/remembered-return flags are finite before N. -/
theorem control_finite [Fintype L] : Finite (machine s sourceMap).σ :=
  SemiprimeD1StackCalls.control_finite original output (.inl .start) (program s sourceMap)
/-- Every physical data and actual return-stack alphabet is finite. -/
theorem all_alphabets_finite [Fintype L] (k : (machine s sourceMap).K) : Finite ((machine s sourceMap).Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite original output (.inl .start) (program s sourceMap) k
/-- All actual component instructions compile to at most four primitive commands. -/
theorem compile_depth [Fintype L] (pc : Label L s.roles.length) :
    SemiprimeD1StackBytecode.statementDepth ((machine s sourceMap).m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start : Label L s.roles.length) (program s sourceMap pc)
end RiemannGaussian.SemiprimeD1StackDescriptorRecordBounds
