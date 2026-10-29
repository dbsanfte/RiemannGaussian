/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsBounds
/-! # Genuine root-record machine and all1804-role real-return prefix resources
The fixed monomial witnesses bound the SAME actual source trace. Caller-prefix
bytes are charged explicitly; the standard finite-machine input is N alone.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRecordsResources
open SemiprimeD1StackRootNetworkRecords SemiprimeD1StackRootNetworkRecordsExecution
open SemiprimeD1StackRootNetworkRecordsAcquisition SemiprimeD1StackRootNetworkRecordsBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
open SemiprimeD1StackCalls (run configuration)
open SemiprimeReportPolynomialGrowth (Bound constant_bound identity_bound add_bound mul_bound)
local notation "main" => (Sum.inl Control.start : Label)
attribute [local irreducible] prefixPolynomial runBound runBoundPrefix FB.runPolynomial OB.polynomial
/-- The caller's standard data store has exactly one original binary-N word. -/
theorem input_single (bits:List Bool) :input bits=fun k=>if k=originalInput then bits else []:=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Every actually initialized N-only data word fits the physical input length. -/
theorem initial_length (bits:List Bool) (k:Stack) :((initial bits).data k).length ≤ bits.length:=by
  change (input bits k).length ≤ bits.length
  rw [input_single]
  by_cases hk:k=originalInput <;> simp [hk]
/-- The alternate front door contains only the actual N and caller-prefix bytes. -/
theorem initial_prefix_length (bits pre:List Bool) (k:Stack) :
    ((initialPrefix bits pre).data k).length ≤ bits.length+pre.length:=by
  rcases k with k|k
  · exact Nat.zero_le _
  · rcases k with k|k
    · exact Nat.zero_le _
    · cases k <;> simp only [initialPrefix,data,words,Sum.elim_inr,List.length_nil] <;> omega
/-- A concrete final halt bounds every successful prefix of that SAME deterministic trace. -/
theorem prefix_time {start finish:C.State Stack Label} (B:Nat)
    (he:∃t ≤ B,run program t start=some finish) (hh:run program 1 finish=none)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel start=some out) :fuel ≤ B:=by
  obtain ⟨t,ht,he⟩:=he
  have hf:fuel ≤ t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add,
      hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- No N-only source prefix passes this actual bounded source's own final halt. -/
theorem prefix_fuel (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (initial bits)=some out) :fuel ≤ runBound bits:=
  prefix_time _ (source_run_bounded bits hc hN) rfl fuel out hr
/-- No caller-prefix execution extends beyond its same complete physical source trace. -/
theorem prefix_fuel_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initialPrefix bits (prescription bits fixed tail))=some out) :
    fuel ≤ runBoundPrefix bits (prescription bits fixed tail).length:=
  prefix_time _ (source_run_prefix_bounded bits hc hN fixed tail) rfl fuel out hr
/-- An abstract finite-role sum avoids expanding any concrete source role enumeration. -/
theorem word_sum_le {K:Type} [Fintype K] (d:K→List Bool) (n:Nat) (h:∀k,(d k).length ≤ n) :
    (∑k:K,(d k).length) ≤ Fintype.card K*n:=by
  calc
    _ ≤ ∑_k:K,n:=Finset.sum_le_sum (fun k _=>h k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- Every real N-only prefix counts all1804 data roles and every actual return cell. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤1805*(bits.length+runBound bits):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ _ (initial_length bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:=word_sum_le out.data (bits.length+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel bits hc hN fuel out hr
  omega
/-- Actual prefix input/tail bytes and both entire retained banks are counted at every prefix. -/
theorem prefix_cells_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initialPrefix bits (prescription bits fixed tail))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      1805*(bits.length+(prescription bits fixed tail).length+
        runBoundPrefix bits (prescription bits fixed tail).length):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (bits.length+(prescription bits fixed tail).length) _ _
    (initial_prefix_length bits (prescription bits fixed tail)) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:=word_sum_le out.data (bits.length+(prescription bits fixed tail).length+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel_prefix bits hc hN fixed tail fuel out hr
  omega
/-- Genuine compiled initialization agrees with the actual source's N-only initial state. -/
theorem initial_eq (bits:List Bool) :Turing.initList machine bits=configuration (initial bits):=by
  have hi:initial bits=SemiprimeD1StackCalls.initial originalInput main bits:=by
    unfold initial SemiprimeD1StackCalls.initial
    rw [input_single]
  rw [hi]
  exact (SemiprimeD1StackCalls.initial_correct originalInput output main program bits).symm
/-- Actual finite-machine certificate starts at true Turing.initList with binary N alone. -/
noncomputable def rootRecordsInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (configuration (done bits hN [] []))) (runBound bits):=by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output main program
  have h:=source_run_bounded bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Same compiled machine also certifies the actual explicit caller-prefix entry. -/
noncomputable def rootRecordsPrefixInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (initialPrefix bits (prescription bits fixed tail)))
      (some (configuration (done bits hN fixed tail))) (runBoundPrefix bits (prescription bits fixed tail).length):=by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output main program
  have h:=source_run_prefix_bounded bits hc hN fixed tail
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- All1804 physical data words and real return cells at every compiled N-only prefix. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤1805*(bits.length+runBound bits):=by
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
/-- All retained caller bytes and actual return cells are counted at every compiled explicit-prefix state. -/
theorem machine_prefix_cells_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (configuration (initialPrefix bits (prescription bits fixed tail))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1805*(bits.length+(prescription bits fixed tail).length+
        runBoundPrefix bits (prescription bits fixed tail).length):=by
  have he:=SemiprimeD1StackCalls.run_correct originalInput output main program fuel
    (initialPrefix bits (prescription bits fixed tail))
  have hh:=he.trans hr
  cases hout:run program fuel (initialPrefix bits (prescription bits fixed tail)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells_prefix bits hc hN fixed tail fuel out hout
/-- A fixed coefficient and degree bound the actual N-only width polynomial before all inputs. -/
theorem polynomial_monomial :∃A d:Nat,∀n,prefixPolynomial n 1 ≤ A*(n+1)^d:=by
  have hf:Bound FB.runPolynomial:=FB.polynomial_monomial
  have ho:Bound OB.polynomial:=OB.polynomial_monomial
  change Bound (fun n=>prefixPolynomial n 1)
  unfold prefixPolynomial
  exact mul_bound (constant_bound 128)
    (add_bound (add_bound (add_bound (add_bound identity_bound (constant_bound 1)) hf)
      (mul_bound ho (constant_bound (1+1)))) (constant_bound 1))
/-- The arbitrary-prefix width envelope has fixed coefficients in total actual input bytes. -/
theorem prefix_polynomial_monomial :∃A d:Nat,∀n P,prefixPolynomial n P ≤ A*(n+P+1)^d:=by
  obtain ⟨Af,df,hf⟩:=FB.polynomial_monomial
  obtain ⟨Ao,do_,ho⟩:=OB.polynomial_monomial
  refine ⟨128*(1+Af+Ao),df+do_+1,?_⟩
  intro n P
  let S:=n+P+1
  have hS:1 ≤ S:=by dsimp [S];omega
  have hn:n+1 ≤ S:=by dsimp [S];omega
  have hP:P+1 ≤ S:=by dsimp [S];omega
  have hdf:S^df ≤ S^(df+do_+1):=Nat.pow_le_pow_right hS (by omega)
  have hdo:S^(do_+1) ≤ S^(df+do_+1):=Nat.pow_le_pow_right hS (by omega)
  have hs:S ≤ S^(df+do_+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hS (by omega:1 ≤ df+do_+1)
  have hF:FB.runPolynomial n ≤ Af*S^(df+do_+1):=
    (hf n).trans (Nat.mul_le_mul_left Af ((Nat.pow_le_pow_left hn df).trans hdf))
  have hO0:OB.polynomial n ≤ Ao*S^do_:=
    (ho n).trans (Nat.mul_le_mul_left Ao (Nat.pow_le_pow_left hn do_))
  have hO:OB.polynomial n*(P+1) ≤ Ao*S^(df+do_+1):=by
    have h:=Nat.mul_le_mul hO0 hP
    rw [Nat.mul_assoc,←pow_succ] at h
    exact h.trans (Nat.mul_le_mul_left Ao hdo)
  have hsum:S+FB.runPolynomial n+OB.polynomial n*(P+1) ≤ (1+Af+Ao)*S^(df+do_+1):=by
    nlinarith only [hs,hF,hO]
  calc
    prefixPolynomial n P=128*(S+FB.runPolynomial n+OB.polynomial n*(P+1)):=by
      unfold prefixPolynomial
      dsimp only [S]
      ring
    _ ≤ _:=by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 128 hsum
/-- Fixed N-only witnesses bound the SAME complete original source execution. -/
theorem source_run_monomial :∃A d:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits),
    ∃t ≤ A*(bits.length+1)^d*2^(19*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits),
      run program t (initial bits)=some (done bits hN [] []):=by
  obtain ⟨A,d,ha⟩:=polynomial_monomial
  refine ⟨A,d,?_⟩
  intro bits hc hN
  obtain ⟨t,ht,hr⟩:=source_run_bounded bits hc hN
  unfold runBound runBoundPrefix at ht
  exact ⟨t,ht.trans (Nat.mul_le_mul_right _ (ha bits.length)),hr⟩
/-- Arbitrary actual prefix/tail bytes are charged in one fixed total-input monomial. -/
theorem source_run_prefix_monomial :∃A d:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool),
    ∃t ≤ A*(bits.length+(prescription bits fixed tail).length+1)^d*2^(19*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits),
      run program t (initialPrefix bits (prescription bits fixed tail))=some (done bits hN fixed tail):=by
  obtain ⟨A,d,ha⟩:=prefix_polynomial_monomial
  refine ⟨A,d,?_⟩
  intro bits hc hN fixed tail
  obtain ⟨t,ht,hr⟩:=source_run_prefix_bounded bits hc hN fixed tail
  unfold runBoundPrefix at ht
  exact ⟨t,ht.trans (Nat.mul_le_mul_right _ (ha bits.length (prescription bits fixed tail).length)),hr⟩
/-- Every compiled transition expands into at most four fundamental commands. -/
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4:=
  SemiprimeD1StackCalls.compile_depth main (program pc)
end RiemannGaussian.SemiprimeD1StackRootNetworkRecordsResources
