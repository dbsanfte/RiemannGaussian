/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ParentTagOrder

/-! # Exact enumeration transport for literal nested finite lists
Only derived finite shape equalities are used. Factor and local indices keep
their literal values and their exact enumeration order; no inverse or entry
value is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 80000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1NestedPositions

/-- Computable identity-index transport through finite row-shape equality. -/
def shapeEquiv {F G : ℕ} (a : Fin F→ℕ) (b : Fin G→ℕ) (h : F=G)
    (ha : ∀e,a e=b ((finCongr h) e)) :
    ((e : Fin F)×Fin (a e)) ≃ ((e : Fin G)×Fin (b e)) :=
  Equiv.sigmaCongr (finCongr h) (fun e => finCongr (ha e))

/-- Shape transport keeps the actual factor number. -/
theorem shapeEquiv_fst {F G : ℕ} (a : Fin F→ℕ) (b : Fin G→ℕ) (h : F=G)
    (ha : ∀e,a e=b ((finCongr h) e)) (i : (e : Fin F)×Fin (a e)) :
    (shapeEquiv a b h ha i).1.val=i.1.val := rfl

/-- Shape transport keeps the actual local port number. -/
theorem shapeEquiv_snd {F G : ℕ} (a : Fin F→ℕ) (b : Fin G→ℕ) (h : F=G)
    (ha : ∀e,a e=b ((finCongr h) e)) (i : (e : Fin F)×Fin (a e)) :
    (shapeEquiv a b h ha i).2.val=i.2.val := rfl

/-- The transported original sigma enumeration has EXACTLY the same order. -/
theorem enumeration_shape {F G : ℕ} (a : Fin F→ℕ) (b : Fin G→ℕ) (h : F=G)
    (ha : ∀e,a e=b ((finCongr h) e)) :
    (SemiprimeFiniteEnumerations.indexedIncidences F a).values.map (shapeEquiv a b h ha)=
      (SemiprimeFiniteEnumerations.indexedIncidences G b).values := by
  cases h
  have hab : a=b:=funext ha
  cases hab
  have hid : (shapeEquiv a a rfl ha : ((e : Fin F)×Fin (a e))→((e : Fin F)×Fin (a e)))=id := by
    funext i
    rcases i with ⟨e,j⟩
    rfl
  rw [hid,List.map_id]

/-- Literal dependent positions of a nested list. -/
abbrev Position {A : Type} (xs : List (List A)) := (e : Fin xs.length)×Fin (xs[e.val]).length

/-- Actual nested-list read at a typed position. -/
def read {A : Type} (xs : List (List A)) (i : Position xs) : A := xs[i.1.val][i.2.val]

/-- Reading the complete original dependent enumeration gives the literal flattened list. -/
theorem enumeration_read {A : Type} (xs : List (List A)) :
    ((SemiprimeFiniteEnumerations.indexedIncidences xs.length (fun e => (xs[e.val]).length)).values.map
      (read xs))=xs.flatten := by
  simp only [SemiprimeFiniteEnumerations.indexedIncidences,SemiprimeFiniteEnumerations.sigma,
    SemiprimeFiniteEnumerations.fin,List.map_flatMap,List.map_map,Function.comp_def]
  have h (e : Fin xs.length) :
      (List.finRange (xs[e.val]).length).map (fun j => read xs ⟨e,j⟩)=xs[e.val] :=
    SemiprimeD1ParentTagOrder.map_fin_reads _
  simp_rw [h]
  rw [List.flatMap_def,SemiprimeD1ParentTagOrder.map_fin_reads]
end RiemannGaussian.SemiprimeD1NestedPositions
