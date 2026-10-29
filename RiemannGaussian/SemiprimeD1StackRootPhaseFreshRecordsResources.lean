/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsExecution
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsValues
/-! # Actual physical word,85-frame and345-cell envelopes for the same row program -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
set_option exponentiation.threshold 4096
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsResources
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsRows SemiprimeD1StackRootPhaseFreshRecordsSource
open SemiprimeD1StackRootPhaseFreshRecordsBinding
attribute [local irreducible] SemiprimeD1StackPhaseCacheFreshExecution.runBound
/-- Every physical included-source input cell is paid by the honest heap/header/VALUE resource. -/
theorem client_initial (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (i:Fin bs.length) (a u edges:Nat) (t:List Bool) (k:Q.Stack) :
    ((E.source bs i []).data k).length ≤
      SemiprimeD1StackPhaseCacheFreshBounds.resource bs i a u edges t [false,true] [] :=by
  have h:=SemiprimeD1StackPhaseCacheFreshBounds.initial_bound (E.heap bs)
    (List.replicate bs.length true) (List.replicate i.val true) [false] k
  change ((E.source bs i []).data k).length ≤
    SemiprimeD1StackPhaseBankRestoreBounds.inputSize bs i+1 at h
  unfold SemiprimeD1StackPhaseCacheFreshBounds.resource
  exact h.trans (by omega)
/-- Generic actual client clock bound from the VALUE-inclusive resource. -/
theorem client_time (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (i:Fin bs.length) (a u edges:Nat) (t:List Bool) (B:Nat) (hB:1 ≤ B)
    (hc:SemiprimeD1StackPhaseCacheFreshBounds.resource bs i a u edges t [false,true] [] ≤ B) :
    E.runBound bs i a u edges t [false,true] [] ≤ 10^14*B^2 :=by
  have h:=SemiprimeD1StackPhaseCacheFreshBounds.run_polynomial bs i a u edges t [false,true] []
    (by intro x hx;cases hx)
  have hc':SemiprimeD1StackPhaseCacheFreshBounds.resource bs i a u edges t [false,true] []+1 ≤ 2*B:=by omega
  have hh:=h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc' 2))
  change _ ≤ 10^12*(2*B)^2 at hh
  have he:10^12*(2*B)^2=4*10^12*B^2:=by ring
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_right _ (by norm_num))
/-- Every stopped client word is bounded from its OWN actual successful source execution. -/
theorem client_word (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (i:Fin bs.length) (a u edges:Nat) (t:List Bool) (B:Nat) (hB:1 ≤ B)
    (hc:SemiprimeD1StackPhaseCacheFreshBounds.resource bs i a u edges t [false,true] [] ≤ B)
    (hb:bs[i.val]=SemiprimeD1StackPhaseCacheFreshComponents.phase a u edges t [false,true]) (k:Q.Stack) :
    ((E.done bs i a u edges t [false,true] []).data k).length ≤ 10^15*B^2 :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseCacheFreshExecution.source_run bs i a u edges t [false,true] []
    (by intro x hx;cases hx) hb
  have hi:∀j,((E.source bs i []).data j).length ≤ B:=fun j=>(client_initial bs i a u edges t j).trans hc
  have hd:=SemiprimeD1StackReturnLink.run_data_bound Q.program q B _ _ hi hr
  have ht:=client_time bs i a u edges t B hB hc
  have h1:B ≤ B^2:=Nat.le_pow (by decide)
  have hk:=hd k
  omega
/-- Physical85field framing charges every actual source byte and delimiter. -/
theorem record_length (bank:F.Stack→List Bool) (B:Nat) (h:∀k,(bank k).length ≤ B) :
    (freshRecord bank).length ≤ 85*(2*B+1) :=by
  have hlist:∀ks:List F.Stack,
      (ks.foldr (fun k tail=>SemiprimeSourceHistogramKeyBits.frame (bank k) tail) []).length ≤ ks.length*(2*B+1):=by
    intro ks
    induction ks with
    | nil=>simp only [List.foldr_nil,List.length_nil,Nat.zero_mul,le_refl]
    | cons k ks ih=>
      have hk:=h k
      simp only [List.foldr_cons,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      nlinarith
  have hh:=hlist SemiprimeD1StackRootPhaseFreshRecordsInventory.roles
  rw [SemiprimeD1StackRootPhaseFreshRecordsInventory.roles_length] at hh
  exact hh
/-- An actual row's complete cache record is bounded from its actual client's complete stopped bank. -/
theorem row_record (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (i:Fin bs.length) (a u edges:Nat) (t:List Bool) (B:Nat) (hB:1 ≤ B)
    (hc:SemiprimeD1StackPhaseCacheFreshBounds.resource bs i a u edges t [false,true] [] ≤ B)
    (hb:bs[i.val]=SemiprimeD1StackPhaseCacheFreshComponents.phase a u edges t [false,true]) :
    (record a u edges t).length ≤ 10^18*B^2 :=by
  have hw:∀k:F.Stack,(freshResult a u edges t k).length ≤ 10^15*B^2:=by
    intro k
    have hh:=client_word bs i a u edges t B hB hc hb (Q.freshStack k)
    change (SemiprimeD1StackPhaseCacheFreshComponents.completed _ _ _ _ _ _ _ _ _ (Q.freshStack k)).length ≤ _ at hh
    unfold SemiprimeD1StackPhaseCacheFreshComponents.completed at hh
    rw [SemiprimeD1StackPhaseCacheFreshComponents.fresh_data] at hh
    exact hh
  have h:=record_length (freshResult a u edges t) (10^15*B^2) hw
  have hp:1 ≤ B^2:=one_le_pow₀ hB
  change (record a u edges t).length ≤ _ at h
  omega
/-- Literal alias view counts every physical role; raw shadows remain counted even when empty. -/
theorem view_word (root:R.Stack→List Bool) (q:Q.Stack→List Bool) (w:Aux→List Bool) (B:Nat)
    (hr:∀k,(root k).length ≤ B) (hq:∀k,(q k).length ≤ B) (hw:∀k,(w k).length ≤ B) (k:Stack) :
    (view root q w k).length ≤ B :=by
  rcases k with k|k
  · rcases k with k|k
    · exact hr _
    · rcases k with k|k
      · exact hr _
      · cases k <;> first | exact hr _ | exact hq _
  · rcases k with k|k
    · change (if k=I.sourceHeap ∨ k=I.sourceCounter ∨ k=I.sourceReference then [] else q k).length ≤ B
      split
      · exact Nat.zero_le _
      · exact hq k
    · cases k <;> first | exact hw _ | exact hq _
/-- All345 actual physical words are summed, without quotienting aliases or dropping shadows. -/
theorem mass_le (bank:Stack→List Bool) (B:Nat) (hb:∀k,(bank k).length ≤ B) :
    SemiprimeD1StackRootPhaseFreshRecordsCleanup.mass bank ≤ 345*B :=by
  calc
    _ ≤ ∑_k:Stack,B:=Finset.sum_le_sum (fun k _=>hb k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- The85serializer source fields are charged at their actual physical address. -/
theorem freshMass_le (bank:Stack→List Bool) (B:Nat) (hb:∀k,(bank k).length ≤ B) :
    SemiprimeD1StackRootPhaseFreshRecordsSerialize.freshMass bank ≤ 85*B :=by
  calc
    _ ≤ ∑_k:F.Stack,B:=Finset.sum_le_sum (fun k _=>hb (freshStack k))
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,SemiprimeD1StackPhaseChildContextFresh.stack_card,smul_eq_mul]
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsResources
