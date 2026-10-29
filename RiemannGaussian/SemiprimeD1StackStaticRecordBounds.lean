/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticRecordExecution
import RiemannGaussian.SemiprimeD1StackStaticTableBounds
/-! # Complete static-record source clock and every physical prefix cell -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackStaticRecordBounds
open SemiprimeD1StackStaticRecord SemiprimeD1StackStaticRecordExecution
open SemiprimeD1StackStaticTableSpec (CheckerTrace inputBytes)
open SemiprimeD1TensorTapeCodec (vectorBits)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L)
/-- Only original template, real scope bank and caller accumulators are supplied. -/
def inputSize (template : K→List Bool) (bank hist out : List Bool) : Nat :=
  inputBytes template+bank.length+hist.length+out.length
omit [DecidableEq K] in
/-- Every actual initial role, including the three empty shadows, is bounded. -/
theorem initial_data_bound (template : K→List Bool) (bank hist out : List Bool) (k : Stack K) :
    ((initial s template bank hist out).data k).length≤ inputSize template bank hist out := by
  have ho (j : K) : (template j).length≤ inputBytes template :=
    by
      unfold inputBytes
      exact Finset.single_le_sum (f:=fun k:K=>(template k).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  rcases k with k|k
  · rcases k with k|k
    · change 0≤_;exact Nat.zero_le _
    · rcases k with k|k
      · have h:=ho k;change (template k).length≤_;unfold inputSize;omega
      · cases k with
        | inl k=>cases k <;> simp [initial,data,SemiprimeD1StackStaticTable.initial,
            SemiprimeD1StackStaticTable.data,SemiprimeD1StackStaticTable.store,
            SemiprimeD1StackDigitCount.data,inputSize]; omega
        | inr k=>cases k <;> simp [initial,data,SemiprimeD1StackStaticTable.initial,
            SemiprimeD1StackStaticTable.data,SemiprimeD1StackStaticTable.store,inputSize]
  · cases k with
    | inl k=>change 0≤_;exact Nat.zero_le _
    | inr k=>cases k <;> simp [initial,data,R.data,inputSize]; omega
/-- A successful same-source halt bounds every successful physical prefix. -/
theorem prefix_fuel_le (template : K→List Bool) (hraw : template s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat) (hc : CheckerTrace s template answer budget)
    (words : List (List Bool)) (hist out : List Bool) (fuel : Nat) (finish : C.State (Stack K) (Label L s.roles.length))
    (hr : C.run (program s) fuel (initial s template (vectorBits words) hist out)=some finish) :
    fuel≤timeBound s template words answer budget := by
  obtain ⟨t,ht,he⟩:=source_run s template hraw answer budget hc words hist out
  have hf:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run (program s) 1 (done s template words answer hist out)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All2K+28 actual Boolean roles, all alias shadows and the real return stack. -/
theorem prefix_cells (template : K→List Bool) (hraw : template s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat) (hc : CheckerTrace s template answer budget)
    (words : List (List Bool)) (hist out : List Bool) (fuel : Nat) (finish : C.State (Stack K) (Label L s.roles.length))
    (hr : C.run (program s) fuel (initial s template (vectorBits words) hist out)=some finish) :
    (∑k:Stack K,(finish.data k).length)+finish.frames.length≤
      (2*Fintype.card K+29)*(inputSize template (vectorBits words) hist out+timeBound s template words answer budget+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound (program s) fuel
    (inputSize template (vectorBits words) hist out) _ finish
    (initial_data_bound s template (vectorBits words) hist out) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound (program s) fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hs:(∑k:Stack K,(finish.data k).length)≤
      (2*Fintype.card K+28)*(inputSize template (vectorBits words) hist out+fuel):=by
    calc
      _≤∑_k:Stack K,(inputSize template (vectorBits words) hist out+fuel):=
        Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le s template hraw answer budget hc words hist out fuel finish hr
  nlinarith
/-- Same complete physical inventory at every actual compiled-machine prefix. -/
theorem machine_prefix_cells [Fintype L] (template : K→List Bool) (hraw : template s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat) (hc : CheckerTrace s template answer budget)
    (words : List (List Bool)) (hist out : List Bool) (fuel : Nat) (cfg : (machine s).Cfg)
    (hr : (fun q=>q.bind (machine s).step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial s template (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack K,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      (2*Fintype.card K+29)*(inputSize template (vectorBits words) hist out+timeBound s template words answer budget+1) := by
  have he:=SemiprimeD1StackCalls.run_correct original output (.inl .start) (program s) fuel
    (initial s template (vectorBits words) hist out)
  have hh:(C.run (program s) fuel (initial s template (vectorBits words) hist out)).map
    SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run (program s) fuel (initial s template (vectorBits words) hist out) with
  | none=>rw [hrun] at hh;cases hh
  | some finish=>
    rw [hrun] at hh
    have heq:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells s template hraw answer budget hc words hist out fuel finish hrun
/-- All finite Boolean and real return-control flags are fixed before input. -/
theorem control_finite [Fintype L] : Finite (machine s).σ :=
  SemiprimeD1StackCalls.control_finite original output (.inl .start) (program s)
/-- Every actual data and return alphabet is finite before the input. -/
theorem all_alphabets_finite [Fintype L] (k : (machine s).K) : Finite ((machine s).Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite original output (.inl .start) (program s) k
/-- Every compiled transition has at most four fundamental commands. -/
theorem compile_depth [Fintype L] (pc : Label L s.roles.length) :
    SemiprimeD1StackBytecode.statementDepth ((machine s).m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start : Label L s.roles.length) (program s pc)
end RiemannGaussian.SemiprimeD1StackStaticRecordBounds
