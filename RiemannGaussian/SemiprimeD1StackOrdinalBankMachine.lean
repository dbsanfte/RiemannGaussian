/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOrdinalBankLoop
/-! # Actual tally-only ordinal-bank machine and every-prefix storage -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackOrdinalBankMachine
open SemiprimeD1StackOrdinalBank SemiprimeD1StackOrdinalBankLoop

/-- The ready supplier has ONLY its physically acquired marker tally as input. -/
theorem initial_eq (tally : List Bool) :
    Turing.initList machine tally=SemiprimeD1StackCalls.configuration (initial tally) := by
  have hs : initial tally=SemiprimeD1StackCalls.initial count (.inl .start) tally := by
    unfold initial SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with k|k <;> cases k <;> simp [data,count,SemiprimeD1StackAssignmentLoop.data]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct count ids (.inl .start) program tally).symm

/-- Real finite-alphabet execution, with no M/cardinality/width/ID answer input. -/
noncomputable def bankInTime (tally : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine tally)
      (some (SemiprimeD1StackCalls.configuration (done tally))) (1000*(tally.length+1)^2) := by
  rw [initial_eq tally]
  apply SemiprimeD1StackCalls.evalsCorrect count ids (.inl .start) program
  let cert:=source_run tally
  let m:=Classical.choose cert
  have hs:=Classical.choose_spec cert
  exact ⟨⟨m,hs.2⟩,hs.1⟩

/-- All actual prefixes are bounded by this program's own executed halt. -/
theorem prefix_fuel_le (tally : List Bool) (fuel : ℕ)
    (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial tally)=some out) :
    fuel≤1000*(tally.length+1)^2 := by
  obtain ⟨time,ht,he⟩:=source_run tally
  have hf : fuel≤time := by
    by_contra hn
    have h : fuel=time+(1+(fuel-(time+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : SemiprimeD1StackCalls.run program 1 (done tally)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht

/-- Every visited configuration counts all nine Boolean stacks and real returns. -/
theorem prefix_cells (tally : List Bool) (fuel : ℕ)
    (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial tally)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤
      10*(tally.length+1000*(tally.length+1)^2+1) := by
  have hi : ∀k:Stack,((initial tally).data k).length≤tally.length := by
    intro k
    rcases k with k|k <;> cases k <;> simp [initial,data,SemiprimeD1StackAssignmentLoop.data]
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel tally.length _ out hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length)≤9*(tally.length+fuel) := by
    calc
      _≤∑_k:Stack,(tally.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by
        have hcard : Fintype.card Stack=9 := by decide
        simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hcard]
  have ht:=prefix_fuel_le tally fuel out hr
  omega

/-- Same closed bound for all prefixes of the actual compiled FinTM2. -/
theorem machine_prefix_cells (tally : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine tally))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      10*(tally.length+1000*(tally.length+1)^2+1) := by
  have he:=SemiprimeD1StackCalls.run_correct count ids (.inl .start) program fuel (initial tally)
  change (SemiprimeD1StackCalls.run program fuel (initial tally)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial tally))) at he
  have hh : (SemiprimeD1StackCalls.run program fuel (initial tally)).map SemiprimeD1StackCalls.configuration=some cfg :=
    he.trans ((congrArg (fun start:machine.Cfg=>
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel] (some start)) (initial_eq tally).symm).trans hr)
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial tally) with
  | none => rw [hrun] at hh; cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells tally fuel out hrun

end RiemannGaussian.SemiprimeD1StackOrdinalBankMachine
