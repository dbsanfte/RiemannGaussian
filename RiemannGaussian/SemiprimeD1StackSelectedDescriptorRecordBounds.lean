/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordExecution
/-! # Complete physical selector/template/record clock and every actual prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordBounds
open SemiprimeD1StackSelectedDescriptorRecord SemiprimeD1StackSelectedDescriptorRecordExecution
open SemiprimeD1StackStaticTableSpec (CheckerTrace)
open SemiprimeD1TensorTapeCodec (vectorBits)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
/-- Every actual input word, old template and old selector is charged. -/
def inputSize (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (oldStage oldInverse bank hist out : List Bool) : Nat :=
  ∑k:Stack K,((initial s oldTemplate raw oldStage oldInverse bank hist out).data k).length
/-- The same complete actual source clock: real selector computation and all
metadata loading/table/serializer/logger work, physical gate and calls/returns. -/
def runBound (oldTemplate : K→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (words : List (List Bool)) (budget : Nat→Nat) (M : Nat)
    (oldStage oldInverse hist out : List Bool) : Nat :=
  SemiprimeD1StackTransformSelectorsExecution.timeBound (raw 1) (raw 2) oldStage oldInverse+
    SemiprimeD1StackDescriptorRecordBounds.runBound s sourceMap oldTemplate (fields raw [second] [inverse])
      words budget M hist out+4
omit [DecidableEq K] in
/-- No native checker report, mode evaluator or metadata-size advice enters this bound. -/
theorem timeBound_le (oldTemplate : K→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (words : List (List Bool)) (answer : List Bool→Bool) (budget : Nat→Nat) (M : Nat)
    (oldStage oldInverse hist out : List Bool)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound s sourceMap oldTemplate raw second inverse words answer budget oldStage oldInverse hist out≤
      runBound s sourceMap oldTemplate raw second inverse words budget M oldStage oldInverse hist out :=by
  have h:=SemiprimeD1StackDescriptorRecordBounds.timeBound_le s sourceMap oldTemplate (fields raw [second] [inverse])
    words answer budget M hist out hl hv
  unfold timeBound runBound
  omega
/-- A successful same-source halt bounds all successful executed prefixes. -/
theorem prefix_fuel_le (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (htag : raw 1=List.replicate tagCode.val true) (htr : raw 2=List.replicate trCode.val true)
    (hcode : SemiprimeD1StackTransformSelectors.tagDispatch tagCode=.copyTransform second)
    (hraw : SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2]) s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2])) answer budget)
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) (fuel : Nat)
    (finish : C.State (Stack K) (Label L s.roles.length))
    (hr : C.run (program s sourceMap) fuel (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out)=some finish) :
    fuel≤timeBound s sourceMap oldTemplate raw second (trCode.val==2) words answer budget oldStage oldInverse hist out :=by
  obtain ⟨t,ht,he⟩:=source_run s sourceMap oldTemplate raw tagCode trCode second htag htr hcode hraw answer budget hc
    words oldStage oldInverse hist out
  have hf:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run (program s sourceMap) 1 (done s sourceMap raw second (trCode.val==2) words answer hist out)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All2K+42 roles, every alias shadow, both original copied fields, all source
words, real selector cells, template banks and ACTUAL nested return cells. -/
theorem prefix_cells (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (htag : raw 1=List.replicate tagCode.val true) (htr : raw 2=List.replicate trCode.val true)
    (hcode : SemiprimeD1StackTransformSelectors.tagDispatch tagCode=.copyTransform second)
    (hraw : SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2]) s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2])) answer budget)
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) (fuel : Nat)
    (finish : C.State (Stack K) (Label L s.roles.length))
    (hr : C.run (program s sourceMap) fuel (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out)=some finish) :
    (∑k:Stack K,(finish.data k).length)+finish.frames.length≤
      (2*Fintype.card K+43)*(inputSize s oldTemplate raw oldStage oldInverse (vectorBits words) hist out+
        timeBound s sourceMap oldTemplate raw second (trCode.val==2) words answer budget oldStage oldInverse hist out+1) :=by
  have hi (k : Stack K) : ((initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out).data k).length≤
      inputSize s oldTemplate raw oldStage oldInverse (vectorBits words) hist out:=by
    unfold inputSize
    exact Finset.single_le_sum
      (f:=fun k:Stack K=>((initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out).data k).length)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound (program s sourceMap) fuel
    (inputSize s oldTemplate raw oldStage oldInverse (vectorBits words) hist out) _ finish hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound (program s sourceMap) fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hs:(∑k:Stack K,(finish.data k).length)≤
      (2*Fintype.card K+42)*(inputSize s oldTemplate raw oldStage oldInverse (vectorBits words) hist out+fuel):=by
    calc
      _≤∑_k:Stack K,(inputSize s oldTemplate raw oldStage oldInverse (vectorBits words) hist out+fuel):=
        Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le s sourceMap oldTemplate raw tagCode trCode second htag htr hcode hraw answer budget hc
    words oldStage oldInverse hist out fuel finish hr
  nlinarith
/-- Same complete prefix inventory for the actual compiled finite machine. -/
theorem machine_prefix_cells [Fintype L] (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (htag : raw 1=List.replicate tagCode.val true) (htr : raw 2=List.replicate trCode.val true)
    (hcode : SemiprimeD1StackTransformSelectors.tagDispatch tagCode=.copyTransform second)
    (hraw : SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2]) s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2])) answer budget)
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) (fuel : Nat) (cfg : (machine s sourceMap).Cfg)
    (hr : (fun q=>q.bind (machine s sourceMap).step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack K,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      (2*Fintype.card K+43)*(inputSize s oldTemplate raw oldStage oldInverse (vectorBits words) hist out+
        timeBound s sourceMap oldTemplate raw second (trCode.val==2) words answer budget oldStage oldInverse hist out+1) :=by
  have he:=SemiprimeD1StackCalls.run_correct (rawSource 0) output (.inl .start) (program s sourceMap) fuel
    (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out)
  have hh:(C.run (program s sourceMap) fuel (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out)).map
    SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run (program s sourceMap) fuel (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out) with
  | none=>rw [hrun] at hh;cases hh
  | some finish=>
    rw [hrun] at hh
    have heq:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells s sourceMap oldTemplate raw tagCode trCode second htag htr hcode hraw answer budget hc
      words oldStage oldInverse hist out fuel finish hrun
end RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordBounds
