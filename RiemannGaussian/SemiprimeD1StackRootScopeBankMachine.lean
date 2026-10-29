/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScopeBankBounds
/-! # Actual finite-machine root occurrence-bank acquisition from N alone -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackRootScopeBankMachine
open SemiprimeD1StackRootScopeBank SemiprimeD1StackRootScopeBankExecution
open SemiprimeD1StackRootScopeBankBounds
open SemiprimeBitArithmetic (bitValue)

/-- There is no initially supplied count, width, scope bank or graph. -/
theorem initial_eq (bits : List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs : initial bits=SemiprimeD1StackCalls.initial originalInput (.inl .start) bits := by
    unfold initial input SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with k|k
    · rcases k with k|k
      · simp [data,E.input,SemiprimeD1StackEdgeCatalogue.input,originalInput,edgeStack,E.catStack,
          SemiprimeD1StackEdgeCatalogueExecution.cat_input]
      · simp [data,E.input,SemiprimeD1StackEdgeCatalogue.input,originalInput,edgeStack,E.catStack]
    · simp [data,originalInput,edgeStack]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct originalInput ids (.inl .start) program bits).symm

/-- Original-N-only finite-alphabet execution, all source/count/range calls paid. -/
noncomputable def rootScopeInTime (bits : List Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (polynomial bits.length) := by
  rw [initial_eq bits]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput ids (.inl .start) program
  let cert:=source_run_polynomial bits hc hN
  let m:=Classical.choose cert
  have hs:=Classical.choose_spec cert
  exact ⟨⟨m,hs.2⟩,hs.1⟩

/-- Every actually executed prefix ends no later than this program's own halt. -/
theorem prefix_fuel_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    fuel≤polynomial bits.length := by
  obtain ⟨time,ht,he⟩:=source_run_polynomial bits hc hN
  have hf : fuel≤time := by
    by_contra hn
    have h : fuel=time+(1+(fuel-(time+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : SemiprimeD1StackCalls.run program 1 (done bits)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht

/-- All eighty-three Boolean data registers and real return frames at EVERY prefix. -/
theorem prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤
      84*(bits.length+polynomial bits.length+1) := by
  have hi : ∀k:Stack,(input bits k).length≤bits.length := by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · change (SemiprimeD1StackVertexCatalogue.input bits k).length≤bits.length
        rw [SemiprimeD1StackEdgeCatalogueExecution.cat_input]
        split <;> simp
      · exact Nat.zero_le _
    · rcases k with k|k <;> exact Nat.zero_le _
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length)≤83*(bits.length+fuel) := by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by
        have hcard : Fintype.card Stack=83 := by decide
        simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hcard]
  have ht:=prefix_fuel_le bits hc hN fuel out hr
  omega


/-- Every actual compiled-machine prefix counts all Boolean data and encoded
return-address cells; the bound is closed in original input width alone. -/
theorem machine_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      84*(bits.length+polynomial bits.length+1) := by
  have he:=SemiprimeD1StackCalls.run_correct originalInput ids (.inl .start) program fuel (initial bits)
  change (SemiprimeD1StackCalls.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh : (SemiprimeD1StackCalls.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg :=
    he.trans ((congrArg (fun start:machine.Cfg=>
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel] (some start)) (initial_eq bits).symm).trans hr)
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial bits) with
  | none => rw [hrun] at hh; cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel out hrun

end RiemannGaussian.SemiprimeD1StackRootScopeBankMachine
