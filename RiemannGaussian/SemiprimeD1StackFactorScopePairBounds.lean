/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopePairExecution
/-! # Same-source polynomial clock and complete122-role/return-cell inventory -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopePairBounds
open SemiprimeD1StackFactorScopePairs SemiprimeD1FactorScopePairEncoding
open SemiprimeD1StackFactorScopePairView SemiprimeD1StackFactorScopePairScan SemiprimeD1StackFactorScopePairExecution
/-- The two selected physical fields are part of the actual nine-field payload. -/
theorem selected_mass (w : Record) : (w 2).length+(w 0).length≤ mass w := by
  have hm : mass w=(w 0).length+((w 1).length+((w 2).length+((w 3).length+((w 4).length+
      ((w 5).length+((w 6).length+((w 7).length+((w 8).length+0)))))))) := rfl
  omega
/-- Physical output payload never exceeds its acquired input inventory. -/
theorem raw_length (rows : List Record) : (raw rows).length≤(stream rows []).length := by
  induction rows with
  | nil=>rfl
  | cons w ws ih=>
    have h:=selected_mass w
    change (row w++raw ws).length≤(record w (stream ws [])).length
    rw [List.length_append,record_length]
    simp only [row,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    omega
/-- All nine parser calls and all nine payload erasures have a linear stream allowance. -/
theorem loopTime_le (rows : List Record) : loopTime rows≤100*(stream rows []).length+1 := by
  induction rows with
  | nil=>decide
  | cons w ws ih=>
    have h:=selected_mass w
    change rowTime w+loopTime ws≤100*(record w (stream ws [])).length+1
    rw [record_length]
    unfold rowTime
    omega
/-- Final tag, literal reversal and final halt are included. -/
theorem totalTime_le (rows : List Record) : totalTime rows≤102*(stream rows []).length+8 := by
  have hl:=loopTime_le rows
  have hr:=raw_length rows
  unfold totalTime
  omega
/-- The original-N source physically acquired all source bytes; its own prefix
certificate bounds the retained actual stream, with no count or size advice. -/
theorem stream_length (bits : List Bool) (hb : bits≠[]) :
    (stream (rows bits) []).length≤10^114*(bits.length+1)^30 := by
  obtain ⟨t,_,hr⟩:=SemiprimeD1StackPortScopeBounds.source_run_polynomial bits hb
  have hs:=SemiprimeD1StackPortScopeBounds.prefix_cells bits hb t _ hr
  change (∑k:S.Stack,(base bits k).length)+0≤10^114*(bits.length+1)^30 at hs
  have ho:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset S.Stack))=>Nat.zero_le ((base bits k).length))
    (Finset.mem_univ (SemiprimeD1StackPortScopeRecords.aux .output))
  have he:=congrArg List.length (source_output bits)
  change (base bits (SemiprimeD1StackPortScopeRecords.aux .output)).length=(stream (rows bits) []).length at he
  omega
/-- One fixed original-binary-width polynomial for the actual complete source. -/
def runBound (bits : List Bool) : Nat :=10^118*(bits.length+1)^30
/-- The physical original-N source, preserving copy, nine-field scan and pair
materialization obey their own whole-clock polynomial. -/
theorem timeBound_le (bits : List Bool) (hb : bits≠[]) : timeBound bits≤runBound bits := by
  have hl:=stream_length bits hb
  have ht:=totalTime_le (rows bits)
  have hp:1≤(bits.length+1)^30:=Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos _))
  unfold timeBound runBound
  omega
/-- No row list, M, factor count, decoded ordinal, evaluator or elapsed clock input. -/
theorem source_run_polynomial (bits : List Bool) (hb : bits≠[]) :
    ∃t≤runBound bits,C.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hb
  exact ⟨t,ht.trans (timeBound_le bits hb),hr⟩
/-- Genuine complete binary-N-only fixed finite machine certificate. -/
noncomputable def machinePairs (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (runBound bits) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (aux .output) (.local .main) program
  let h:=source_run_polynomial bits hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Successful source prefixes cannot pass the actual final halt. -/
theorem prefix_fuel_le (bits : List Bool) (hb : bits≠[]) (fuel : Nat) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) : fuel≤runBound bits := by
  obtain ⟨t,ht,he⟩:=source_run_polynomial bits hb
  have hf:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every original source, copy, reader, nine cache and frame role, including
all real return-label cells, is counted at every actual prefix. -/
theorem prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : Nat) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤123*(bits.length+runBound bits) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    change (input bits k).length≤bits.length
    rw [input_eq]
    dsimp only
    split <;> simp) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤122*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  omega
/-- Same complete physical inventory for every compiled original-N machine prefix. -/
theorem machine_prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤123*(bits.length+runBound bits) := by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput (aux .output) (.local .main) program fuel (initial bits)
  have hh:=he.trans hr
  cases hs:C.run program fuel (initial bits) with
  | none=>rw [hs] at hh;cases hh
  | some out=>
    rw [hs] at hh
    have hc:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hs
end RiemannGaussian.SemiprimeD1StackFactorScopePairBounds
