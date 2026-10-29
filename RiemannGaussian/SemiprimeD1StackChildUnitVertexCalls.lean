/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildUnitVertex
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual context acquisition followed by literal unit-source acquisition
Shared acquired rank and precision are read in place; displaced unit cache
shadows stay empty. Neither cache is supplied as an extra runtime operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildUnitVertexCalls
open SemiprimeD1StackChildUnitVertex SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace UC
export SemiprimeD1StackJetUnit (bank initial)
end UC
/-- The physically included unit projection uses the context's actual shared cache words. -/
theorem bank_unit (j : J.Stack→List Bool) (u : U.Stack→List Bool) (record scratch : List Bool)
    (hw : j J.widthCache=u U.widthCache) (hr : j J.rankCache=u U.rankCache) (k : U.Stack) :
    bank j u record scratch (unit k)=u k := by
  by_cases hW : k=U.widthCache
  · subst k
    exact hw
  · by_cases hR : k=U.rankCache
    · rw [unit,ite_eq_right hW,ite_eq_left hR]
      change j J.rankCache=u k
      rw [hR]
      exact hr
    · rw [unit,ite_eq_right hW,ite_eq_right hR]
      change (if k=U.widthCache ∨ k=U.rankCache then [] else u k)=u k
      rw [ite_eq_right (not_or_intro hW hR)]
/-- A unit entry has no non-cache input payload. -/
theorem unit_initial_empty (width rank : List Bool) (k : U.Stack) (hw : k≠U.widthCache) (hr : k≠U.rankCache) :
    UC.bank width rank [] [] [] k=[] := by
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · cases k <;> first | rfl | exact (hw rfl).elim
  · cases k <;> first | rfl | exact (hr rfl).elim
/-- The proof view may name the already acquired caches without filling either physical displaced shadow. -/
theorem bank_initial (j : J.Stack→List Bool) :
    bank j (fun _=>[]) [] []=bank j (UC.bank (j J.widthCache) (j J.rankCache) [] [] []) [] [] := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · change (if k=U.widthCache ∨ k=U.rankCache then [] else [])=
        (if k=U.widthCache ∨ k=U.rankCache then [] else UC.bank (j J.widthCache) (j J.rankCache) [] [] [] k)
      split
      · rfl
      · next h=>rw [unit_initial_empty _ _ k (fun hk=>h (Or.inl hk)) (fun hk=>h (Or.inr hk))]
    · rfl
/-- The actual context source runs from original two-header bytes and acquires both cache words. -/
theorem context_call (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    ∃t≤1000*(SemiprimeD1StackJetContextBounds.resource axes precision+1)^2+1,
      Runs program t (.local .start) (initial (vectorBits (axes.map unary)) precision).data (.local .unit)
        (bank (SemiprimeD1StackJetContextCorrectness.finalData axes precision) (fun _=>[]) [] []) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackJetContextBounds.source_run_polynomial axes hp precision
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program context Label.context context_injective
    J.program .start (fun _=>rfl) (.local .start) (.local .unit) rfl t _ _ _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Exact actual acquired context bank, used only to describe source boundaries. -/
def contextData (axes : List ℕ) (precision : List Bool) : J.Stack→List Bool :=
  SemiprimeD1StackJetContextCorrectness.finalData axes precision
/-- Physically acquired precision markers, never an independent input. -/
def width (axes : List ℕ) (precision : List Bool) : List Bool:=contextData axes precision J.widthCache
/-- Physically acquired rank markers, never an independent input. -/
def rank (axes : List ℕ) (precision : List Bool) : List Bool:=contextData axes precision J.rankCache
/-- Fixed original context denoted by the two actual headers. -/
def ctx (axes : List ℕ) (precision : List Bool) : SemiprimeD1JetAxes.Context:=⟨axes,SemiprimeBitArithmetic.bitValue precision⟩
/-- These actual precision bytes have exactly the original precision VALUE length. -/
theorem width_length (axes : List ℕ) (precision : List Bool) : (width axes precision).length=(ctx axes precision).precision:=
  SemiprimeD1StackJetContextCorrectness.width_value axes precision
/-- These actual rank bytes have exactly the original axis-product VALUE length. -/
theorem rank_length (axes : List ℕ) (precision : List Bool) : (rank axes precision).length=(ctx axes precision).rank:=
  List.length_replicate
/-- The actual whole15-role unit source executes using SAME acquired context words, including precision zero. -/
theorem unit_call (axes : List ℕ) (precision : List Bool) :
    Runs program (SemiprimeD1StackJetUnitExecution.totalTime (width axes precision) (rank axes precision)+1)
      (.local .unit) (bank (contextData axes precision) (fun _=>[]) [] []) (.local .leaf)
      (bank (contextData axes precision) (UC.bank (width axes precision) (rank axes precision) [] []
        (vectorBits (SemiprimeD1JetAffineCoefficient.one (ctx axes precision)).words)) [] []) := by
  rw [bank_initial]
  have hr:=SemiprimeD1StackJetUnitExecution.source_run (ctx axes precision)
    (width axes precision) (rank axes precision) (width_length axes precision) (rank_length axes precision)
  apply SemiprimeD1StackProcedureCallsTrace.included_call program unit Label.unit unit_injective
    U.program .seed0 (fun _=>rfl) (.local .unit) (.local .leaf) rfl _ _ _ _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k
      exact bank_unit _ _ [] [] rfl rfl k
    · intro k _;rfl
  · constructor
    · intro k
      exact bank_unit _ _ [] [] rfl rfl k
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · by_cases hw : k=U.widthCache
          · subst k;rfl
          · by_cases hr : k=U.rankCache
            · subst k;rfl
            · exact (hk k (by rw [unit,ite_eq_right hw,ite_eq_right hr];rfl)).elim
        · rfl
end RiemannGaussian.SemiprimeD1StackChildUnitVertexCalls
