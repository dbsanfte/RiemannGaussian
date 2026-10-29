/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCartesian4Execution

/-! # Closed internal Cartesian machine time
This is an internal physically prepared primitive. The final original graph
supplier acquires limits/tag by actual instructions; this module makes no
original-input graph-acquisition claim on its own.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCartesian4Bounds
open SemiprimeD1StackCartesian4 SemiprimeD1StackCartesian4Components SemiprimeD1StackCartesian4Execution
open SemiprimeD1StackProcedureFragments (At Runs)

/-- All actual index work counters are initially empty. -/
def emptyIndices : Fin 4→List Bool := fun _=>[]
/-- Actual internal prepared entry, with no caller return frames. -/
def initial (limits:Fin 4→List Bool) (tag output:List Bool) : C.State Stack Label :=
  ⟨some (.inl .main),none,none,store limits emptyIndices tag output,[]⟩
/-- Actual whole four-product return payload, retaining all acquired source words. -/
def done (dims:Fin 4→ℕ) (limits:Fin 4→List Bool) (tag output:List Bool) : C.State Stack Label :=
  ⟨none,none,none,store limits emptyIndices tag (box0 dims emptyIndices tag output),[]⟩

/-- The concrete four-level clock is a fixed-degree polynomial. -/
theorem stageBudget_le (D T n:ℕ) : stageBudget D T n≤40*(D+T+1)^(n+1) := by
  induction n with
  | zero =>
    simp only [stageBudget,Nat.zero_add,pow_one]
    omega
  | succ n ih =>
    have hp:(D+T+1)≤(D+T+1)^(n+1):=by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1≤D+T+1 by omega) (show 1≤n+1 by omega)
    have hm:=Nat.mul_le_mul_left D ih
    simp only [stageBudget,pow_succ] at *
    nlinarith [Nat.zero_le ((D+T+1)^n*T)]

/-- The actual closed engine runs all four loops and literal field calls; there is no body advice. -/
theorem source_run (dims:Fin 4→ℕ) (limits:Fin 4→List Bool) (tag output:List Bool) (D:ℕ)
    (hl:∀j,limits j=List.replicate (dims j) true) (hd:∀j,dims j≤D) :
    ∃m≤stageBudget D tag.length 4+3,C.run program m (initial limits tag output)=some (done dims limits tag output) := by
  obtain ⟨m,hm,hbody⟩:=level0_run dims limits emptyIndices tag output D hl hd
    (by intro j;simp [emptyIndices]) (by intro j _;rfl)
  have h:=SemiprimeD1StackLocalCall.call_run program (.inl .main) (.inl (.entry 0)) (.inl .ret) (.inl .halt)
    _ _ m rfl rfl hbody
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial limits tag output) ⟨rfl,rfl,rfl⟩
  refine ⟨(m+2)+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done dims limits tag output)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done]

/-- Fixed polynomial transition cap, with all actual Copy/Frame work retained. -/
theorem source_run_polynomial (dims:Fin 4→ℕ) (limits:Fin 4→List Bool) (tag output:List Bool) (D:ℕ)
    (hl:∀j,limits j=List.replicate (dims j) true) (hd:∀j,dims j≤D) :
    ∃m≤43*(D+tag.length+1)^5,C.run program m (initial limits tag output)=some (done dims limits tag output) := by
  obtain ⟨m,hm,hr⟩:=source_run dims limits tag output D hl hd
  refine ⟨m,hm.trans ?_,hr⟩
  have h:=stageBudget_le D tag.length 4
  change stageBudget D tag.length 4≤40*(D+tag.length+1)^5 at h
  have hpos:0<(D+tag.length+1)^5:=by positivity
  have hp:1≤(D+tag.length+1)^5:=hpos
  omega

/-- Actual finite-machine certificate from physically prepared internal source words. -/
noncomputable def preparedInTime (dims:Fin 4→ℕ) (limits:Fin 4→List Bool) (tag output:List Bool) (D:ℕ)
    (hl:∀j,limits j=List.replicate (dims j) true) (hd:∀j,dims j≤D) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial limits tag output))
      (some (SemiprimeD1StackCalls.configuration (done dims limits tag output))) (43*(D+tag.length+1)^5) := by
  apply SemiprimeD1StackCalls.evalsCorrect (limitStack 0) (aux 2) (.inl .main) program
  let cert:=source_run_polynomial dims limits tag output D hl hd
  let m:=Classical.choose cert
  have hs:=Classical.choose_spec cert
  exact ⟨⟨m,hs.2⟩,hs.1⟩
end RiemannGaussian.SemiprimeD1StackCartesian4Bounds
