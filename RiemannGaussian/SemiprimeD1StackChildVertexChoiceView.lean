/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexChoice
/-! # Complete physical banks for the literal activity caller
The overlay is a proof-side description of the stopped bank, never an executed
lookup or an operand of the finite source. All four displaced roles remain real.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexChoiceView
open SemiprimeD1StackChildVertexChoice
namespace M
export SemiprimeD1StackMultiplierLink (DataRel)
end M
/-- Complete stopped active bank, including every inactive allocation. -/
def activeResult (a : A.Stack→List Bool) : Stack→List Bool:=bank a (fun _=>[]) []
/-- Proof-side exact replacement of the inactive image; every other word is retained. -/
noncomputable def inactiveResult (a : A.Stack→List Bool) (u : U.Stack→List Bool) : Stack→List Bool:=
  fun k=>if h:∃i,inactive i=k then u (Classical.choose h) else activeResult a k
/-- Every actual inactive source word has exactly its acquired stopped value. -/
theorem inactive_project (a : A.Stack→List Bool) (u : U.Stack→List Bool) (i : U.Stack) :
    inactiveResult a u (inactive i)=u i := by
  unfold inactiveResult
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  exact inactive_injective (Classical.choose_spec (show ∃j,inactive j=inactive i from ⟨i,rfl⟩))
/-- The complete inactive result retains every physical word outside its literal image. -/
theorem inactive_outside (a : A.Stack→List Bool) (u : U.Stack→List Bool) (k : Stack)
    (hk : ∀i,inactive i≠k) : inactiveResult a u k=activeResult a k := by
  unfold inactiveResult
  rw [dite_eq_right (by rintro ⟨i,hi⟩;exact hk i hi)]
/-- The stopped bank satisfies the full component relation, including all foreign words. -/
theorem inactive_rel (a : A.Stack→List Bool) (u : U.Stack→List Bool) :
    M.DataRel inactive (activeResult a) u (inactiveResult a u) :=
  ⟨inactive_project a u,inactive_outside a u⟩
/-- Active inclusion retains all inactive private/shadow cells and the consumed activity cell. -/
theorem active_rel (a b : A.Stack→List Bool) :
    M.DataRel active (activeResult a) b (activeResult b) := by
  constructor
  · intro k;rfl
  · intro k hk
    rcases k with k|k
    · exact (hk k rfl).elim
    · rfl
/-- Physically removing the singleton activity changes exactly its actual tape. -/
theorem pop_activity (a : A.Stack→List Bool) (bit : Bool) :
    Function.update (bank a (fun _=>[]) [bit]) activity []=activeResult a := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k;rfl
/-- The only original inactive input words are its two original headers. -/
theorem unit_initial_only (axes precision : List Bool) (k : U.Stack)
    (ha : k≠U.context J.axesCache) (hp : k≠U.context J.precisionBits) :
    (SemiprimeD1StackChildUnitVertex.initial axes precision).data k=[] := by
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · fin_cases k <;> simp_all [SemiprimeD1StackChildUnitVertex.initial,
          SemiprimeD1StackChildUnitVertex.bank,SemiprimeD1StackChildUnitVertex.context,
          SemiprimeD1StackJetContext.initial,SemiprimeD1StackJetContext.bank,
          SemiprimeD1StackJetContext.cached,SemiprimeD1StackJetContext.axesCache,
          SemiprimeD1StackJetContext.precisionBits,J.axesCache,J.precisionBits,U.context]
  · rcases k with k|k
    · change (if _ then [] else ([] : List Bool))=[]
      split <;> rfl
    · cases k <;> rfl
/-- The two inactive header aliases read the actual retained new-context inputs. -/
theorem initial_headers (parent order oldAxes oldp axes precision scope : List Bool) :
    (A.initial parent order oldAxes oldp axes precision scope).data newAxes=axes ∧
    (A.initial parent order oldAxes oldp axes precision scope).data newPrecision=precision := ⟨rfl,rfl⟩
/-- Exact entire inactive entry projection; no pre-acquired rank or precision markers are supplied. -/
theorem inactive_initial (parent order oldAxes oldp axes precision scope : List Bool) :
    ∀k,activeResult (A.initial parent order oldAxes oldp axes precision scope).data (inactive k)=
      (SemiprimeD1StackChildUnitVertex.initial axes precision).data k := by
  intro k
  by_cases h0:k=U.context J.axesCache
  · subst k;rfl
  by_cases h1:k=U.context J.precisionBits
  · subst k;rfl
  by_cases h2:k=U.aux .record
  · subst k;rfl
  by_cases h3:k=U.aux .scratch
  · subst k;rfl
  rw [unit_initial_only axes precision k h0 h1]
  simp [activeResult,bank,inactive,shared,h0,h1,h2,h3,inactiveWork]
/-- All169 actual source words have the same prepared initial bank. -/
theorem initial_data (parent order oldAxes oldp axes precision scope : List Bool) (bit : Bool) :
    (initial parent order oldAxes oldp axes precision scope [bit]).data=
      bank (A.initial parent order oldAxes oldp axes precision scope).data (fun _=>[]) [bit] := rfl
end RiemannGaussian.SemiprimeD1StackChildVertexChoiceView
