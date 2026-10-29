/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRuntimeDesignAcquisition
import RiemannGaussian.SemiprimePaddedConstraintSpan

/-!
# Proof-only bridge from source row matches to the pure runtime design

The algorithm is RuntimeDesignAcquisition.build on raw integer input. Layout.Data
occurs only in validity and rank theorems, never as an argument of that algorithm.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeSourceRuntimeDesignBridge
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LayoutExactBuckets
open SemiprimeRuntimeDesignAcquisition SemiprimeRowSelectionExecution

/-- Integer-kernel locality is unchanged by an explicitly identified coordinate order. -/
theorem killsIntegerKernel_equiv {V W I : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (C : I → W → ℤ) (a : W → ℚ) (h : KillsIntegerKernel a C) :
    KillsIntegerKernel (fun v => a (e v)) (fun i v => C i (e v)) := by
  intro z hz
  change (∑ v, a (e v)*(z v : ℚ))=0
  have hold (i : I) : ∑ w, C i w*z (e.symm w)=0 := by
    calc
      _ = ∑ v, C i (e v)*z (e.symm (e v)) := (e.sum_comp _).symm
      _ = 0 := by simpa only [signature, Equiv.symm_apply_apply] using hz i
  have ha := h (fun w => z (e.symm w)) hold
  calc
    _ = ∑ w, a w*(z (e.symm w) : ℚ) := by
      simpa only [Equiv.symm_apply_apply] using e.sum_comp (fun w => a w*(z (e.symm w) : ℚ))
    _ = 0 := ha

variable {I : Type} {n F Q R : ℕ}
variable {owner : I → Fin n} {factor : I → Fin F}

/-- The actual head sets agree by their public coordinate labels. -/
def headEquiv (d : RawDesign n F)
    (L : Layout.Data (O := ℚ) (G := Fin d.r) owner factor Q R) (t : Fin Q)
    (hhead : ∀ v, d.head v=L.head t v) (g : Fin d.r) :
    {v : Fin n // d.head v=g} ≃ {v : Fin n // L.head t v=g} where
  toFun v := ⟨v.val,by rw [← hhead]; exact v.property⟩
  invFun v := ⟨v.val,by rw [hhead]; exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Complete old-row coverage gives native locality for the raw constraints.
No raw locality conclusion or selected native-span premise is supplied. -/
theorem raw_locality (d : RawDesign n F)
    (L : Layout.Data (O := ℚ) (G := Fin d.r) owner factor Q R) (t : Fin Q)
    (hhead : ∀ v, d.head v=L.head t v)
    (hassigned : ∀ e, d.assigned e=L.color e t)
    (arity : Fin F → ℕ) (incidence : (e : Fin F) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i)=e)
    (hold : ∀ (g : Fin d.r) (j : Fin (L.rowCount t g)),
      ∃ k : Fin (d.count g), ∀ v : {v : Fin n // L.head t v=g},
        d.rows g k v.val=L.constraints t g j v)
    (e : Fin F) (i : Fin (arity e)) (g : Fin d.r) (hg : g ≠ d.assigned e) :
    KillsIntegerKernel
      (fun v : {v : Fin n // d.head v=g} => (L.row (incidence e i) v.val).eval (L.node t))
      (fun j (v : {v : Fin n // d.head v=g}) => d.rows g j v.val) := by
  have hne : g ≠ L.color (factor (incidence e i)) t := by
    simpa only [hfactor, ← hassigned] using hg
  have hl := L.locality t (incidence e i) g hne
  have hcoverage : ∀ j : Fin (L.rowCount t g),
      ∃ k : Fin (d.count g),
        (fun v : {v : Fin n // L.head t v=g} => d.rows g k v.val)=L.constraints t g j := by
    intro j
    obtain ⟨k,hk⟩ := hold g j
    exact ⟨k,funext hk⟩
  have hraw := SemiprimePaddedConstraintSpan.killsIntegerKernel_of_complete
    (L.constraints t g) (fun j (v : {v : Fin n // L.head t v=g}) => d.rows g j v.val)
    hcoverage (fun v => (L.row (incidence e i) v.val).eval (L.node t)) hl
  exact killsIntegerKernel_equiv (headEquiv d L t hhead g) _ _ hraw

/-- Padding by old rows and zeros preserves the exact acquired selected count. -/
theorem selected_count_source (d : RawDesign n F)
    (L : Layout.Data (O := ℚ) (G := Fin d.r) owner factor Q R) (t : Fin Q)
    (hhead : ∀ v, d.head v=L.head t v)
    (hnew : ∀ (g : Fin d.r) (k : Fin (d.count g)),
      (∀ v : {v : Fin n // L.head t v=g}, d.rows g k v.val=0) ∨
      ∃ j : Fin (L.rowCount t g), ∀ v : {v : Fin n // L.head t v=g},
        d.rows g k v.val=L.constraints t g j v)
    (hold : ∀ (g : Fin d.r) (j : Fin (L.rowCount t g)),
      ∃ k : Fin (d.count g), ∀ v : {v : Fin n // L.head t v=g},
        d.rows g k v.val=L.constraints t g j v) (g : Fin d.r) :
    (build d).m g=LayoutRank.rowRank (L.constraints t g) := by
  let rawOld : Fin (d.count g) → {v : Fin n // L.head t v=g} → ℤ := fun j v => d.rows g j v.val
  let rawNew : Fin (d.count g) → {v : Fin n // d.head v=g} → ℤ := fun j v => d.rows g j v.val
  have hcolNew := rank_column_equiv rawNew (columns d g)
  have hcolOld := rank_column_equiv rawOld ((columns d g).trans (headEquiv d L t hhead g))
  have heq : LayoutRank.rowRank rawNew=LayoutRank.rowRank rawOld := hcolNew.symm.trans hcolOld
  have hp := SemiprimePaddedConstraintSpan.rowRank_eq_of_padding (L.constraints t g) rawOld
    (fun k => by
      rcases hnew g k with hz|⟨j,hj⟩
      · exact Or.inl (funext hz)
      · exact Or.inr ⟨j,funext hj⟩)
    (fun j => by obtain ⟨k,hk⟩ := hold g j; exact ⟨k,funext hk⟩)
  exact (SemiprimeRuntimeDesignAcquisition.selected_count d g).trans (heq.trans hp)

/-- Native source validity of the pure acquired design, derived from row matches. -/
def sourceCertificate (d : RawDesign n F)
    (L : Layout.Data (O := ℚ) (G := Fin d.r) owner factor Q R) (t : Fin Q)
    (hhead : ∀ v, d.head v=L.head t v)
    (hassigned : ∀ e, d.assigned e=L.color e t)
    (arity : Fin F → ℕ) (incidence : (e : Fin F) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i)=e)
    (hW : ∀ g j v, |d.rows g j v|≤(d.W g : ℤ))
    (hold : ∀ (g : Fin d.r) (j : Fin (L.rowCount t g)),
      ∃ k : Fin (d.count g), ∀ v : {v : Fin n // L.head t v=g},
        d.rows g k v.val=L.constraints t g j v) :
    SemiprimeIndexedNodeCertificate.Data arity (SemiprimeLayoutSelection.nodeRows L arity incidence t) :=
  certify d arity (SemiprimeLayoutSelection.nodeRows L arity incidence t) hW
    (raw_locality d L t hhead hassigned arity incidence hfactor hold)

/-- Proof-only source validity erases to the polynomial-free integer-row algorithm. -/
theorem sourceCertificate_runtime (d : RawDesign n F)
    (L : Layout.Data (O := ℚ) (G := Fin d.r) owner factor Q R) (t : Fin Q)
    (hhead : ∀ v, d.head v=L.head t v)
    (hassigned : ∀ e, d.assigned e=L.color e t)
    (arity : Fin F → ℕ) (incidence : (e : Fin F) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i)=e)
    (hW : ∀ g j v, |d.rows g j v|≤(d.W g : ℤ))
    (hold : ∀ (g : Fin d.r) (j : Fin (L.rowCount t g)),
      ∃ k : Fin (d.count g), ∀ v : {v : Fin n // L.head t v=g},
        d.rows g k v.val=L.constraints t g j v) :
    SemiprimeNodeArrayExecution.runtimeDesign
      (rows := fun e i v => L.row (incidence e i) v) (t := L.node t)
      (sourceCertificate d L t hhead hassigned arity incidence hfactor hW hold)=build d := rfl

end RiemannGaussian.SemiprimeSourceRuntimeDesignBridge
