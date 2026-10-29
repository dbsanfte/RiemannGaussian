/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootEntrySemantics

/-! # Original root owner-copy semantics on actual canonical fibres
Every local equality scan is the complete original owner fibre. Prefix tests
retain duplicate and conflicting records; empty fibres preserve two choices.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1RootOwnerSemantics
open scoped BigOperators
open SemiprimeD1RootOwnerTables SemiprimeD1RootCopyContraction
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A literal Boolean conjunction contributes its exact zero/one scalar. -/
theorem bitNat_and {R : Type*} [CommSemiring R] (p q : Bool) :
    (SemiprimeBitArithmetic.bitNat (p&&q):R)=if p=true ∧ q=true then 1 else 0 := by
  cases p <;> cases q <;> simp [SemiprimeBitArithmetic.bitNat]

/-- The executed owner weight is the sum of its two actual allowed copy values. -/
theorem weight_sum {R : Type*} [CommSemiring R] {n : ℕ}
    (fixed : List (Fin n×Bool)) (v : Fin n) (bits : List Bool) :
    (weight fixed v bits:R)=∑b : Bool,
      if allowed fixed v b=true ∧ bits.all (fun x => decide (x=b))=true then 1 else 0 := by
  unfold weight
  rw [Nat.cast_add,bitNat_and,bitNat_and,Fintype.sum_bool]
  exact add_comm _ _

/-- A complete canonical port read compares all and only that owner's original
incidence bits; no equality/truth certificate is supplied at the root endpoint. -/
theorem all_reads_iff {M n : ℕ} (owner : Fin M→Fin n) (v : Fin n) (ports : List ℕ)
    (hb : ∀p∈ports,p<M) (hf : ∀j : Fin M,j.val∈ports ↔ owner j=v)
    (a : Fin M→Bool) (b : Bool) :
    ((ports.map (fun p => ((List.ofFn a)[p]?).getD false)).all (fun x => decide (x=b))=true) ↔
      ∀j,owner j=v → a j=b := by
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    have hp := (hf j).mpr hj
    have ht := h _ (List.mem_map.mpr ⟨j.val,hp,rfl⟩)
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using j.isLt)] at ht
    simpa only [List.getElem_ofFn,Option.getD_some,decide_eq_true_eq] using ht
  · intro h x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    have hlt := hb p hp
    have hv := h ⟨p,hlt⟩ ((hf ⟨p,hlt⟩).mp hp)
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hlt)]
    simpa only [List.getElem_ofFn,Option.getD_some,decide_eq_true_eq] using hv

/-- Actual complete owner-fibre scans are exactly the copy weights contracted
by RootCopyContraction, with both original prefix-compatible Boolean choices. -/
theorem weight_fibre {R : Type*} [CommSemiring R] {M n : ℕ}
    (owner : Fin M→Fin n) (fixed : List (Fin n×Bool)) (v : Fin n) (ports : List ℕ)
    (hb : ∀p∈ports,p<M) (hf : ∀j : Fin M,j.val∈ports ↔ owner j=v) (a : Fin M→Bool) :
    (weight fixed v (ports.map (fun p => ((List.ofFn a)[p]?).getD false)):R)=
      copyWeight owner (fun v b => allowed fixed v b=true) a v := by
  rw [weight_sum]
  unfold copyWeight
  apply Finset.sum_congr rfl
  intro b _
  have hi := all_reads_iff owner v ports hb hf a b
  by_cases h : allowed fixed v b=true ∧
      (ports.map (fun p => ((List.ofFn a)[p]?).getD false)).all (fun x => decide (x=b))=true
  · have hr : allowed fixed v b=true ∧ ∀j,owner j=v → a j=b := ⟨h.1,hi.mp h.2⟩
    exact (ite_eq_left h).trans (ite_eq_left hr).symm
  · have hr : ¬(allowed fixed v b=true ∧ ∀j,owner j=v → a j=b) := by
      intro hr
      exact h ⟨hr.1,hi.mpr hr.2⟩
    exact (ite_eq_right h).trans (ite_eq_right hr).symm

/-- The conjunction of all owner prefix checks is precisely the original
finite prefix restriction, including duplicate/conflicting records. -/
theorem prefix_allowed_iff {n : ℕ} (fixed : List (Fin n×Bool)) (bits : Fin n→Bool) :
    (∀v,allowed fixed v (bits v)=true) ↔ fixed.all (fun p => bits p.1 == p.2)=true := by
  simp only [allowed,List.all_eq_true,decide_eq_true_eq,beq_iff_eq]
  constructor
  · intro h p hp
    exact ((h p.1 p hp).resolve_left (fun he => he rfl)).symm
  · intro h v p hp
    by_cases he : p.1=v
    · right
      have hh := (h p hp).symm
      simpa only [he] using hh
    · exact Or.inl he

end
end RiemannGaussian.SemiprimeD1RootOwnerSemantics
