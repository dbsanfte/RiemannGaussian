/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordExecution
/-! # Whole same-source own clock and all1263 physical/return-cell prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordBounds
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordSpec
open SemiprimeD1StackAllDescriptorRecordExecution SemiprimeD1StackAllDescriptorRecordCleanup
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- The actual whole dispatcher clock is linear in the SAME actual component
clock and acquired physical input bytes; every1252-position drain is included. -/
theorem timeBound_linear (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) :
    timeBound code raw words hist out≤2000000*(mass (cleanData raw (vectorBits words) hist out)+
      componentClock code raw words hist out+1) :=by
  have h:=code.isLt
  unfold timeBound
  nlinarith
/-- A proved actual halt bounds every successful executed prefix of this same program. -/
theorem prefix_fuel_le (code:Fin 18) (raw:Fin 6→List Bool)
    (htag:raw 1=List.replicate code.val true)
    (h2:raw 2=SemiprimeD1StackUnaryDivmod.unary (raw 2).length)
    (h3:raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (h4:raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (htr:(code.val=1∨code.val=2∨code.val=3)→(raw 2).length<3)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) (fuel:Nat) (finish:C.State Stack Label)
    (hr:C.run program fuel (initial raw (vectorBits words) hist out)=some finish) :
    fuel≤ timeBound code raw words hist out :=by
  obtain ⟨t,ht,he⟩:=source_run code raw htag h2 h3 h4 htr hc hN words hist out
  have hf:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done code raw words hist out)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All1263 allocated data roles, inactive components and shadows, original
fields/scope/caller words, flags and real nested return cells share one own clock. -/
theorem prefix_cells (code:Fin 18) (raw:Fin 6→List Bool)
    (htag:raw 1=List.replicate code.val true)
    (h2:raw 2=SemiprimeD1StackUnaryDivmod.unary (raw 2).length)
    (h3:raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (h4:raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (htr:(code.val=1∨code.val=2∨code.val=3)→(raw 2).length<3)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) (fuel:Nat) (finish:C.State Stack Label)
    (hr:C.run program fuel (initial raw (vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      1264*(mass (cleanData raw (vectorBits words) hist out)+timeBound code raw words hist out+1) :=by
  have hi (k:Stack) : ((initial raw (vectorBits words) hist out).data k).length≤
      mass (cleanData raw (vectorBits words) hist out):=word_le_mass _ k
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (mass (cleanData raw (vectorBits words) hist out)) _ finish hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(finish.data k).length)≤1263*(mass (cleanData raw (vectorBits words) hist out)+fuel):=by
    calc
      _≤∑_k:Stack,(mass (cleanData raw (vectorBits words) hist out)+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le code raw htag h2 h3 h4 htr hc hN words hist out fuel finish hr
  nlinarith
/-- The same physical/return-cell prefix bound on the genuine compiled machine. -/
theorem machine_prefix_cells (code:Fin 18) (raw:Fin 6→List Bool)
    (htag:raw 1=List.replicate code.val true)
    (h2:raw 2=SemiprimeD1StackUnaryDivmod.unary (raw 2).length)
    (h3:raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (h4:raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (htr:(code.val=1∨code.val=2∨code.val=3)→(raw 2).length<3)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial raw (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      1264*(mass (cleanData raw (vectorBits words) hist out)+timeBound code raw words hist out+1) :=by
  have he:=SemiprimeD1StackCalls.run_correct (source 0) output (.inl .start) program fuel
    (initial raw (vectorBits words) hist out)
  have hh:(C.run program fuel (initial raw (vectorBits words) hist out)).map
      SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run program fuel (initial raw (vectorBits words) hist out) with
  | none=>rw [hrun] at hh;cases hh
  | some finish=>
    rw [hrun] at hh
    have heq:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells code raw htag h2 h3 h4 htr hc hN words hist out fuel finish hrun
/-- Every actual flag and nested return label is finite. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (source 0) output (.inl .start) program
/-- Every actual data and real return-stack alphabet is finite. -/
theorem all_alphabets_finite (k:machine.K) : Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (source 0) output (.inl .start) program k
/-- The same physical compiled instruction uses at most four fundamental commands. -/
theorem compile_depth (pc:Label) : SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start : Label) (program pc)
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordBounds
