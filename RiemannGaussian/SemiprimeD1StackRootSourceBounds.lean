/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSourceOriginal
/-! # N-only root/normalization source acquisition time and all-prefix storage
The original public preprocessing call, marker copies/pops, BOTH actual powers,
all literal pushes and actual work/return cleanup are counted independently.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackRootSourceBounds
open SemiprimeD1StackRootSources SemiprimeD1StackRootSourceExecution SemiprimeD1StackRootSourceOriginal
/-- Fixed body time is linear in the ACTUAL acquired modulus-word and exponent
cache lengths, never the numeric modulus or an advised exponent value. -/
theorem bodyTime_le (cache : P.Stack→List Bool) :
    bodyTime cache ≤ 300*((cache modulusKey).length+(cache exponentKey).length+1) := by
  have hr : (rootMarkers cache).length ≤ (cache modulusKey).length := by
    simp only [rootMarkers,List.length_tail];omega
  have hn : (normalMarkers cache).length ≤ (cache modulusKey).length := by
    simp only [normalMarkers,List.length_drop,List.length_tail];omega
  have h0 : (literalCode 0).length=9 := by decide
  have h1 : (literalCode 1).length=7 := by decide
  have h2 : (literalCode 2).length=9 := by decide
  have h3 : (literalCode 3).length=5 := by decide
  have h4 : (literalCode 4).length=5 := by decide
  unfold bodyTime
  rw [SemiprimeD1StackExprPowerBounds.totalTime_eq,SemiprimeD1StackExprPowerBounds.totalTime_eq,h0,h1,h2,h3,h4]
  omega
/-- Original-input physical modulus/exponent word lengths are polynomially
bounded before construction; these are actual acquired cache identities. -/
theorem acquired_lengths (bits : List Bool) :
    (actualCache bits modulusKey).length ≤ 64*bits.length+2 ∧
    (actualCache bits exponentKey).length ≤ 64*bits.length+1 := by
  have hR:=(SemiprimeD1StackTransformArithmetic.prefix_powers bits.length
    (SemiprimeMacroParameters.transformExponent bits.length) (le_refl _)).1
  have hE:=SemiprimeD1StackTransformArithmetic.exponent_bound bits.length
  rw [modulus_length,exponent_length]
  change 2^SemiprimeMacroParameters.transformExponent bits.length+1 ≤ 64*bits.length+2 ∧ _
  omega
/-- One fixed quadratic transition bound before ALL original binary inputs. -/
def timeBound (bits : List Bool) : ℕ := 10000000*(bits.length+1)^2
/-- The actual whole original-input program has a closed transition bound.
No exponent, source syntax, supplied intermediate, source size or clock premise. -/
theorem source_run_bounded (bits : List Bool) (hb : bits≠[]) :
    ∃t ≤ timeBound bits,C.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hb
  have hB:=bodyTime_le (actualCache bits)
  have hA:=acquired_lengths bits
  refine ⟨t,ht.trans ?_,hr⟩
  change SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+bodyTime (actualCache bits)+2 ≤ timeBound bits
  unfold SemiprimeD1BinaryPublicAcquisitionExecution.timeBound timeBound
  nlinarith [Nat.zero_le (bits.length^2)]
/-- Proof-side choice of a proved actual run; the executable table has no choice. -/
noncomputable def sourceBuild (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits) (some (done bits)) (timeBound bits) := by
  let h:=source_run_bounded bits hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Original BINARY N is genuinely the only initial tape/stack payload. -/
theorem initial_configuration (bits : List Bool) :
    SemiprimeD1StackCalls.configuration (initial bits)=Turing.initList machine bits := by
  have hs : initial bits=SemiprimeD1StackCalls.initial
      (.inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))) Label.start bits := by
    unfold initial input store SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k <;> rfl
      · rcases k with k|k <;> rfl
    · cases k <;> rfl
  rw [hs]
  exact SemiprimeD1StackCalls.initial_correct _ (.inr .root) Label.start program bits
/-- Genuine fixed finite-machine acquisition from original N ONLY, returning
actual old inverse-root source and retaining the other three codes/all caches. -/
noncomputable def machineBuild (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (timeBound bits) := by
  rw [←initial_configuration]
  exact SemiprimeD1StackCalls.evalsCorrect
    (.inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))) (.inr .root)
    Label.start program _ _ _ (sourceBuild bits hb)
/-- No successful prefix can continue past the actual completed whole halt. -/
theorem prefix_fuel_le (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) : fuel ≤ timeBound bits := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded bits hb
  have hf : fuel ≤ t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All THIRTY-SIX Boolean data stacks AND real return-label cells, at EVERY
reached prefix; repeated powers/copies and every emitted code cell are included. -/
theorem prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 1000000000*(bits.length+1)^2 := by
  have hdata : ∀k,((initial bits).data k).length ≤ bits.length := by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp only [initial,input,store,P.input,SemiprimeD1BinaryPublicAcquisition.store,
            SemiprimeD1BinaryPublicAcquisition.Digits.input,SemiprimeD1BinaryDigitAcquisition.store,
            SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil] <;> omega
        · rcases k with k|k <;> exact Nat.zero_le _
      · rcases k with k|k <;> exact Nat.zero_le _
    · cases k <;> exact Nat.zero_le _
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out hdata hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 36*(bits.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(bits.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  unfold timeBound at ht
  nlinarith [Nat.zero_le (bits.length^2)]
/-- Same complete all-prefix inventory for the genuine original-input FinTM2. -/
theorem machine_prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000000*(bits.length+1)^2 := by
  rw [←initial_configuration] at hr
  have he:=SemiprimeD1StackCalls.run_correct
    (.inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))) (.inr .root)
    Label.start program fuel (initial bits)
  have hh:=he.trans hr
  cases hc : C.run program fuel (initial bits) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hc
end RiemannGaussian.SemiprimeD1StackRootSourceBounds
