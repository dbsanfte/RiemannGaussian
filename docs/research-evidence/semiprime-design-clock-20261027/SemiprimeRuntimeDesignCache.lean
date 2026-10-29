/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRuntimeDesignAcquisition

/-!
# Materializing runtime design accessors
Both grouping directions, bounds, assignments and integer entries are cached.
Shape functions retain their original types; their finite metadata evaluation
is a separate bounded scalar-read stage, not a free arbitrary callback claim.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeRuntimeDesignCache
open SemiprimeNodeArrayExecution

/-- Acquire an entire finite function once; later calls read its actual array. -/
def function {n : ℕ} {A : Type*} (f : Fin n → A) : Fin n → A :=
  let entries := Array.ofFn f
  fun i => entries[i.val]'(by simp [entries])

/-- A cached finite function retains its exact values. -/
theorem function_eq {n : ℕ} {A : Type*} (f : Fin n → A) : function f=f := by
  funext i
  simp only [function,Array.getElem_ofFn]

/-- Cache both directions of an explicitly supplied finite grouping equivalence. -/
def grouping {n r : ℕ} {h : Fin r → ℕ} (e : Fin n ≃ ((g : Fin r) × Fin (h g))) :
    Fin n ≃ ((g : Fin r) × Fin (h g)) := by
  let forwards := Array.ofFn e
  let backwards := Array.ofFn (fun g : Fin r => Array.ofFn (fun i : Fin (h g) => e.symm ⟨g,i⟩))
  let f := fun i : Fin n => forwards[i.val]'(by simp [forwards])
  let b := fun p : (g : Fin r) × Fin (h g) =>
    (backwards[p.1.val]'(by simp [backwards]))[p.2.val]'(by simp [backwards])
  have hf : f=e := by funext i; simp only [f,forwards,Array.getElem_ofFn]
  have hb : b=e.symm := by
    funext p
    rcases p with ⟨g,i⟩
    simp only [b,backwards,Array.getElem_ofFn]
  exact { toFun := f, invFun := b
          left_inv := by intro i; rw [hf,hb]; exact e.symm_apply_apply i
          right_inv := by intro p; rw [hf,hb]; exact e.apply_symm_apply p }

/-- Grouping acquisition changes neither direction's values. -/
theorem grouping_eq {n r : ℕ} {h : Fin r → ℕ} (e : Fin n ≃ ((g : Fin r) × Fin (h g))) : grouping e=e := by
  apply Equiv.ext
  intro i
  simp only [grouping,Array.getElem_ofFn]
  rfl

/-- Cache finite value accessors and both grouping directions. Shape fields are
unchanged; they carry no row selection and are charged as metadata separately. -/
def acquire {n F : ℕ} (d : RuntimeDesign n F) : RuntimeDesign n F :=
  let ws := function d.W
  let assigned := function d.assigned
  let grp := grouping d.grouping
  let values := Array.ofFn (fun g : Fin d.r => Array.ofFn (fun j : Fin (d.m g) =>
    Array.ofFn (fun v : Fin (d.h g) => d.C g j v)))
  { d with W := ws, grouping := grp, assigned := assigned
           C := fun g j v => ((values[g.val]!)[j.val]!)[v.val]! }

/-- Cached accessors give EXACT original design values. -/
theorem acquire_eq {n F : ℕ} (d : RuntimeDesign n F) : acquire d=d := by
  simp [acquire,function_eq,grouping_eq]

end RiemannGaussian.SemiprimeRuntimeDesignCache
