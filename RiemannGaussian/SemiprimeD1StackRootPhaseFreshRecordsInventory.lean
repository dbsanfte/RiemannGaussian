/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseCacheFreshOriginal
/-! # Fixed complete fresh85 serialization and cache143 cleanup inventories -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsInventory
namespace P
export SemiprimeD1StackPhaseWorkingPrecision (Stack)
end P
namespace PI
export SemiprimeD1StackRootPhaseParametersInventory (roles roles_length roles_nodup roles_complete)
end PI
namespace F
export SemiprimeD1StackPhaseChildContextFresh (Stack contextStack aux)
end F
namespace H
export SemiprimeD1StackPhaseChildContext (phaseStack oldStack childStack aux)
end H
namespace J
export SemiprimeD1StackJetContext (Stack axesCache)
end J
namespace Q
export SemiprimeD1StackPhaseCacheFresh (Stack restoreStack freshStack)
end Q
namespace Restore
export SemiprimeD1StackPhaseBankRestore (phaseStack heapStack)
end Restore
/-- All eight actual suffix/rank/axis registers of one context cache. -/
def suffixRoles : List SemiprimeD1StackJetSuffix.Stack :=[.axes,.reverseAxes,.axis,.radix,.product,.records,.scratch,.valid]
/-- Every15-role context cache, including all VALUE-decoder work and retained inputs. -/
def jetRoles : List J.Stack :=suffixRoles.map Sum.inl++
  SemiprimeD1StackRootPhaseParametersInventory.subtraction.map (fun k=>.inr (.inl k))++
  (List.finRange 3).map (fun k=>.inr (.inr k))
/-- Two actual child-header helper roles. -/
def headerAux : List SemiprimeD1StackPhaseChildContext.Aux :=[.valid,.scratch]
/-- Five actual fresh coefficient-vector allocator words. -/
def freshAux : List SemiprimeD1StackPhaseChildContextFresh.Aux :=[.remaining,.skip,.history,.output,.scratch]
/-- Fixed85-role logical Fresh order; P48 is the ACTUAL shared restored bank. -/
def roles : List F.Stack :=
  PI.roles.map (F.contextStack ∘ H.phaseStack)++jetRoles.map (F.contextStack ∘ H.oldStack)++
  jetRoles.map (F.contextStack ∘ H.childStack)++headerAux.map (F.contextStack ∘ H.aux)++freshAux.map F.aux
/-- Every ten-word physical heap-read register, including parser scratch and validity. -/
def heapRoles : List SemiprimeD1StackHeapRead.Stack :=
  [.heap,.counter,.reference,.reader,.depth,.referenceWork,.temporary,.fieldScratch,.output,.valid]
/-- ALL143 allocated cache-client roles, including every48unused private P48 shadow. -/
def cacheRoles : List Q.Stack :=PI.roles.map (Q.restoreStack ∘ Restore.phaseStack)++
  heapRoles.map (Q.restoreStack ∘ Restore.heapStack)++roles.map Sum.inr
/-- Literal actual source-heap input, aliased by the whole caller to its retained source heap. -/
def sourceHeap : Q.Stack :=Q.restoreStack (Restore.heapStack .heap)
/-- Literal actual source allocation counter, retained by every consumer call. -/
def sourceCounter : Q.Stack :=Q.restoreStack (Restore.heapStack .counter)
/-- Literal actual issued-reference input, physically acquired by the caller's field parser. -/
def sourceReference : Q.Stack :=Q.restoreStack (Restore.heapStack .reference)
/-- The sole persistent root old-axis header, physically seeded to [false] once. -/
def oldHeader : Q.Stack :=Q.freshStack (F.contextStack (H.oldStack J.axesCache))
/-- Only140 logical client fields are drained: immutable source heap/counter
and the retained literal old header are excluded. Reference is included ONCE. -/
def clearRoles : List Q.Stack :=cacheRoles.filter
  (fun k=>decide (k≠sourceHeap ∧ k≠sourceCounter ∧ k≠oldHeader))
/-- Exactly15 complete physical context roles. -/
theorem jetRoles_length : jetRoles.length=15 :=by decide
/-- No context field is repeated. -/
theorem jetRoles_nodup : jetRoles.Nodup :=by decide
/-- Complete original VALUE/rank/header/precision context bank. -/
theorem jetRoles_complete (k:J.Stack) : k∈jetRoles :=by
  rcases k with k|k
  · cases k <;> simp [jetRoles,suffixRoles]
  · rcases k with k|k
    · cases k <;> simp [jetRoles,SemiprimeD1StackRootPhaseParametersInventory.subtraction]
    · fin_cases k <;> simp [jetRoles]
/-- Exactly85 complete logical stopped Fresh words are serialized. -/
theorem roles_length : roles.length=85 :=by
  simp only [roles,List.length_append,List.length_map,PI.roles_length,jetRoles_length]
  rfl
/-- The fixed stopped-bank field order has no duplicates. -/
theorem roles_nodup : roles.Nodup :=by decide
/-- Every actual stopped Fresh role appears, including all old/new/P48/work fields. -/
theorem roles_complete (k:F.Stack) : k∈roles :=by
  simp only [roles,List.append_assoc,List.mem_append,List.mem_map]
  rcases k with k|k
  · rcases k with k|k
    · exact Or.inl ⟨k,PI.roles_complete k,rfl⟩
    · rcases k with k|k
      · exact Or.inr (Or.inl ⟨k,jetRoles_complete k,rfl⟩)
      · rcases k with k|k
        · exact Or.inr (Or.inr (Or.inl ⟨k,jetRoles_complete k,rfl⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k,by cases k <;> simp [headerAux],rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k,by cases k <;> simp [freshAux],rfl⟩)))
/-- Finite fixed serialization role selection, absent any numeric input-dependent index. -/
def role (i:Fin 85) : F.Stack :=roles.get ⟨i.val,by simpa only [roles_length] using i.isLt⟩
/-- Literal cache-client physical inventory count, with all shadows counted. -/
theorem cacheRoles_length : cacheRoles.length=143 :=by
  simp only [cacheRoles,List.length_append,List.length_map,PI.roles_length,roles_length]
  rfl
/-- Every allocated client role is unique in the cleanup catalogue. -/
theorem cacheRoles_nodup : cacheRoles.Nodup :=by decide
/-- Every allocated client role is represented, including all inactive shadows. -/
theorem cacheRoles_complete (k:Q.Stack) : k∈cacheRoles :=by
  simp only [cacheRoles,List.append_assoc,List.mem_append,List.mem_map]
  rcases k with k|k
  · rcases k with k|k
    · exact Or.inl ⟨k,PI.roles_complete k,rfl⟩
    · exact Or.inr (Or.inl ⟨k,by cases k <;> simp [heapRoles],rfl⟩)
  · exact Or.inr (Or.inr ⟨k,roles_complete k,rfl⟩)
/-- Three protected logical words are excluded from the actual physical drain sites. -/
theorem clearRoles_length : clearRoles.length=140 :=by decide
/-- No logical drain site occurs twice. -/
theorem clearRoles_nodup : clearRoles.Nodup :=List.Nodup.filter _ cacheRoles_nodup
/-- Exactly the source heap, source counter and persistent old header are protected. -/
theorem clearRoles_mem (k:Q.Stack) : k∈clearRoles ↔ k≠sourceHeap ∧ k≠sourceCounter ∧ k≠oldHeader :=by
  simp only [clearRoles,List.mem_filter,decide_eq_true_eq,cacheRoles_complete,true_and]
/-- Fixed finite selection of one of140 logical cleanup addresses. -/
def clearRole (i:Fin 140) : Q.Stack :=clearRoles.get ⟨i.val,by simpa only [clearRoles_length] using i.isLt⟩
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsInventory
