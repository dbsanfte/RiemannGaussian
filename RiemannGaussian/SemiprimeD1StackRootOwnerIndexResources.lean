/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootOwnerIndex
import RiemannGaussian.SemiprimeD1StackRootOwnerIndexBounds
/-! # Genuine N-only owner-index initialization and all1821-role resources
Both full source banks and the two unused index-input shadows are included.
Time and prefix bounds are attached to the same actual finite caller program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootOwnerIndexResources
open SemiprimeD1StackRootOwnerIndex
open SemiprimeD1StackCalls (run configuration)
local notation "main" => (Sum.inl Control.start :Label)
/-- Both allocated source-input shadows and every other private empty index role are physically empty. -/
theorem private_empty (k:I.Stack):privateView (fun _=>[]) k=[]:=by cases k <;> rfl
/-- The actual standard source initializes exactly one original binary-N word. -/
theorem input_single (bits:List Bool):input bits=fun k=>if k=originalInput then bits else []:=by
  funext k
  rcases k with k|k
  · have h:=congrFun (SemiprimeD1StackRootNetworkRecordsResources.input_single bits) k
    simpa only [input,data,Sum.elim_inl,originalInput,rootStack,Sum.inl.injEq] using h
  · change privateView (fun _=>[]) k=[]
    exact private_empty k
/-- Every actually initialized N-only word is paid by the physical binary input length. -/
theorem initial_length (bits:List Bool) (k:Stack):((initial bits).data k).length ≤bits.length:=by
  change (input bits k).length ≤bits.length
  rw [input_single]
  by_cases hk:k=originalInput <;> simp [hk]
/-- The explicit caller-prefix front door initializes only its actual N and prescription bytes. -/
theorem initial_prefix_length (bits pre:List Bool) (k:Stack):
    ((initialPrefix bits pre).data k).length ≤bits.length+pre.length:=by
  rcases k with k|k
  · exact SemiprimeD1StackRootNetworkRecordsResources.initial_prefix_length bits pre k
  · change (privateView (fun _=>[]) k).length ≤bits.length+pre.length
    rw [private_empty,List.length_nil]
    exact Nat.zero_le _
/-- A concrete halt bounds every successful prefix of the same deterministic actual caller. -/
theorem prefix_time {start finish:C.State Stack Label} (B:Nat)
    (he:∃time ≤B,run program time start=some finish) (hh:run program 1 finish=none)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel start=some out):fuel ≤B:=by
  obtain ⟨time,ht,he⟩:=he
  have hf:fuel ≤time:=by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Genuine compiled standard initialization starts with N alone at the literal source entry. -/
theorem initial_eq (bits:List Bool):Turing.initList machine bits=configuration (initial bits):=by
  have hi:initial bits=SemiprimeD1StackCalls.initial originalInput main bits:=by
    unfold initial SemiprimeD1StackCalls.initial
    rw [input_single]
  rw [hi]
  exact (SemiprimeD1StackCalls.initial_correct originalInput output main program bits).symm
open SemiprimeD1StackRootOwnerIndexBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
attribute [local irreducible] runBound runBoundPrefix prefixPolynomial
/-- No successful N-only prefix passes the same source's actual final halt. -/
theorem prefix_fuel (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (initial bits)=some out):fuel ≤runBound bits:=
  prefix_time _ (source_run_bounded bits hc hN) rfl fuel out hr
/-- The actual prescribed bytes and retained tail use the same successful source's own bounded clock. -/
theorem prefix_fuel_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initialPrefix bits (RE.prescription bits fixed tail))=some out):
    fuel ≤runBoundPrefix bits (RE.prescription bits fixed tail).length:=
  prefix_time _ (source_run_prefix_bounded bits hc hN fixed tail) rfl fuel out hr
/-- Every1821allocated role, both empty input shadows, and all actual return cells are charged at every prefix. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (initial bits)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤1822*(bits.length+runBound bits):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ _ (initial_length bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=SemiprimeD1StackRootNetworkRecordsResources.word_sum_le out.data (bits.length+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel bits hc hN fuel out hr
  omega
/-- Caller-prefix bytes and both complete source banks remain included at every actual prefix. -/
theorem prefix_cells_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initialPrefix bits (RE.prescription bits fixed tail))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      1822*(bits.length+(RE.prescription bits fixed tail).length+
        runBoundPrefix bits (RE.prescription bits fixed tail).length):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (bits.length+(RE.prescription bits fixed tail).length) _ _
    (initial_prefix_length bits (RE.prescription bits fixed tail)) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=SemiprimeD1StackRootNetworkRecordsResources.word_sum_le out.data
    (bits.length+(RE.prescription bits fixed tail).length+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel_prefix bits hc hN fixed tail fuel out hr
  omega
/-- Genuine compiled certificate starts at true Turing.initList with binary N alone. -/
noncomputable def ownerIndexInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits):StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (configuration (X.done bits hN [] []))) (runBound bits):=by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output main program
  have h:=source_run_bounded bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine caller-prefix certificate executes the same fixed program on the actual input/tail bytes. -/
noncomputable def ownerIndexPrefixInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool):
    StateTransition.EvalsToInTime machine.step
      (configuration (initialPrefix bits (RE.prescription bits fixed tail)))
      (some (configuration (X.done bits hN fixed tail)))
      (runBoundPrefix bits (RE.prescription bits fixed tail).length):=by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output main program
  have h:=source_run_prefix_bounded bits hc hN fixed tail
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- All compiled N-only prefixes count every actual data word and real fixed-alphabet return symbol. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤1822*(bits.length+runBound bits):=by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput output main program fuel (initial bits)
  have hh:=he.trans hr
  cases hout:run program fuel (initial bits) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel out hout
/-- Explicit-prefix compiled states retain the same complete source/shadow and real-return accounting. -/
theorem machine_prefix_cells_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (configuration (initialPrefix bits (RE.prescription bits fixed tail))))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1822*(bits.length+(RE.prescription bits fixed tail).length+
        runBoundPrefix bits (RE.prescription bits fixed tail).length):=by
  have he:=SemiprimeD1StackCalls.run_correct originalInput output main program fuel
    (initialPrefix bits (RE.prescription bits fixed tail))
  have hh:=he.trans hr
  cases hout:run program fuel (initialPrefix bits (RE.prescription bits fixed tail)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells_prefix bits hc hN fixed tail fuel out hout
/-- A fixed coefficient and degree precede every original N in the actual whole-source time statement. -/
theorem source_run_monomial:∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits),∃time ≤
      coef*(bits.length+1)^degree*2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits),
        run program time (initial bits)=some (X.done bits hN [] []):=by
  obtain ⟨coef,degree,hp⟩:=polynomial_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨time,ht,hr⟩:=source_run_bounded bits hc hN
  have hb:runBound bits ≤coef*(bits.length+1)^degree*
      2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=by
    unfold runBound runBoundPrefix
    exact Nat.mul_le_mul_right _ (hp bits.length)
  exact ⟨time,ht.trans hb,hr⟩
/-- Actual prefix/tail bytes have fixed polynomial witnesses before N and every prescribed list. -/
theorem source_run_prefix_monomial:∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool),∃time ≤
      coef*(bits.length+(RE.prescription bits fixed tail).length+1)^degree*
        2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits),
      run program time (initialPrefix bits (RE.prescription bits fixed tail))=some (X.done bits hN fixed tail):=by
  obtain ⟨coef,degree,hp⟩:=prefix_polynomial_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN fixed tail
  obtain ⟨time,ht,hr⟩:=source_run_prefix_bounded bits hc hN fixed tail
  have hb:runBoundPrefix bits (RE.prescription bits fixed tail).length ≤
      coef*(bits.length+(RE.prescription bits fixed tail).length+1)^degree*
        2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=by
    unfold runBoundPrefix
    exact Nat.mul_le_mul_right _ (hp bits.length (RE.prescription bits fixed tail).length)
  exact ⟨time,ht.trans hb,hr⟩
/-- Each actual source step expands into at most four genuine fixed-machine statements. -/
theorem compile_depth (pc:Label):SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4:=
  SemiprimeD1StackCalls.compile_depth main (program pc)
/-- The complete data/return cap inherits fixed polynomial witnesses without changing its actual exponent. -/
theorem cell_cap (n P poly coef degree E:Nat) (hp:poly ≤coef*(n+P+1)^degree) (he:1 ≤E):
    1822*(n+P+poly*E) ≤1822*(1+coef)*(n+P+1)^(degree+1)*E:=by
  let S:=n+P+1
  have hs:1 ≤S:=by dsimp [S];omega
  have hd:S^degree ≤S^(degree+1):=Nat.pow_le_pow_right hs (by omega)
  have hself:S ≤S^(degree+1):=by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by omega:1 ≤degree+1)
  have hbase:n+P ≤S^(degree+1)*E:=by
    have h0:n+P ≤S^(degree+1):=(by dsimp [S];omega:n+P ≤S).trans hself
    exact h0.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S^(degree+1)) he)
  have hpoly:poly*E ≤coef*S^(degree+1)*E:=
    Nat.mul_le_mul_right E (hp.trans (Nat.mul_le_mul_left coef hd))
  change _ ≤1822*(1+coef)*S^(degree+1)*E
  calc
    _ ≤1822*(S^(degree+1)*E+coef*S^(degree+1)*E):=Nat.mul_le_mul_left 1822 (Nat.add_le_add hbase hpoly)
    _= _:=by ring
/-- Fixed monomial witnesses bound all actual N-only data/return prefixes before original N. -/
theorem prefix_monomial:∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (_hN:0 < bitValue bits) (fuel:Nat) (out:C.State Stack Label),
    run program fuel (initial bits)=some out→
      (∑k:Stack,(out.data k).length)+out.frames.length ≤coef*(bits.length+1)^degree*
        2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=by
  obtain ⟨coef,degree,hp⟩:=polynomial_monomial
  refine ⟨1822*(1+coef),degree+1,?_⟩
  intro bits hc hN fuel out hr
  have he:1 ≤2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=Nat.pow_pos (by decide)
  have hcap:1822*(bits.length+runBound bits) ≤1822*(1+coef)*(bits.length+1)^(degree+1)*
      2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=by
    unfold runBound runBoundPrefix
    simpa only [Nat.add_zero] using cell_cap bits.length 0 (prefixPolynomial bits.length 1) coef degree
      (2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits))
      (by simpa only [Nat.add_zero] using hp bits.length) he
  exact (prefix_cells bits hc hN fuel out hr).trans hcap
/-- Every actual caller-prefix byte and both complete banks obey fixed monomial prefix witnesses. -/
theorem prefix_monomial_prefix:∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (_hN:0 < bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) (fuel:Nat) (out:C.State Stack Label),
    run program fuel (initialPrefix bits (RE.prescription bits fixed tail))=some out→
      (∑k:Stack,(out.data k).length)+out.frames.length ≤
        coef*(bits.length+(RE.prescription bits fixed tail).length+1)^degree*
          2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=by
  obtain ⟨coef,degree,hp⟩:=prefix_polynomial_monomial
  refine ⟨1822*(1+coef),degree+1,?_⟩
  intro bits hc hN fixed tail fuel out hr
  have he:1 ≤2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=Nat.pow_pos (by decide)
  have hcap:1822*(bits.length+(RE.prescription bits fixed tail).length+
      runBoundPrefix bits (RE.prescription bits fixed tail).length) ≤
      1822*(1+coef)*(bits.length+(RE.prescription bits fixed tail).length+1)^(degree+1)*
        2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=by
    unfold runBoundPrefix
    exact cell_cap bits.length (RE.prescription bits fixed tail).length
      (prefixPolynomial bits.length (RE.prescription bits fixed tail).length) coef degree
      (2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits))
      (hp bits.length (RE.prescription bits fixed tail).length) he
  exact (prefix_cells_prefix bits hc hN fixed tail fuel out hr).trans hcap
end RiemannGaussian.SemiprimeD1StackRootOwnerIndexResources
