import RiemannGaussian.SemiprimeD1BoundaryAddresses
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Ordered concrete Boolean catalogues enumerate each incident TRUE subset once. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryCatalogue
open scoped BigOperators
open SemiprimeD1BoundaryRecords
variable {E R : Type*} [DecidableEq E]

/-- TRUE subset encoded by a concrete ordered address. -/
def selected : List E → List Bool → Finset E
  | [],_ => ∅
  | _::_,[] => ∅
  | p::ps,b::bs => if b then insert p (selected ps bs) else selected ps bs

theorem selected_subset (ports : List E) (bits : List Bool) :
    selected ports bits ⊆ ports.toFinset := by
  induction ports generalizing bits with
  | nil => simp [selected]
  | cons p ps ih =>
    cases bits with
    | nil => simp [selected]
    | cons b bs =>
      cases b
      · simpa only [selected,List.toFinset_cons,Bool.false_eq_true,ite_false] using
          (ih bs).trans (Finset.subset_insert p ps.toFinset)
      · simpa only [selected,List.toFinset_cons,ite_true] using
          Finset.insert_subset_insert p (ih bs)

/-- No address multiplicity is introduced by the executed false-first catalogue. -/
theorem assignments_selected_sum [AddCommMonoid R] (ports : List E) (hn : ports.Nodup)
    (F : Finset E → R) :
    ((assignments ports.length).value.map (fun bits => F (selected ports bits))).sum =
      ∑ z ∈ ports.toFinset.powerset, F z := by
  induction ports generalizing F with
  | nil => simp [assignments,selected]
  | cons p ps ih =>
    have hp := List.nodup_cons.mp hn
    simp only [List.length_cons,assignments,List.map_append,List.sum_append,List.map_map,
      Function.comp_def,selected,Bool.false_eq_true,ite_false,ite_true]
    rw [ih hp.2 F,ih hp.2 (fun z => F (insert p z))]
    rw [List.toFinset_cons,Finset.sum_powerset_insert (by simpa using hp.1)]

/-- Full finite Boolean assignment syntax is equivalent to the TRUE-subset sum. -/
theorem finite_selected_sum [AddCommMonoid R] (ports : List E) (hn : ports.Nodup)
    (F : Finset E → R) :
    (∑ bits : Fin ports.length → Bool, F (selected ports (List.ofFn bits))) =
      ∑ z ∈ ports.toFinset.powerset, F z := by
  exact (SemiprimeD1BoundaryAddresses.assignments_sum ports.length
    (fun bits => F (selected ports bits))).symm.trans
      (assignments_selected_sum ports hn F)

theorem selected_read (ports : List E) (hn : ports.Nodup) (bits : List Bool)
    (hl : bits.length = ports.length) (p : E) (hp : p ∈ ports) :
    decide (p ∈ selected ports bits) = (bits[ports.idxOf p]?).getD false := by
  induction ports generalizing bits with
  | nil => simp at hp
  | cons q qs ih =>
    have hq := List.nodup_cons.mp hn
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      have hlen : bs.length = qs.length := Nat.succ.inj hl
      by_cases he : p = q
      · subst p
        have hnsel : q ∉ selected qs bs := fun h => hq.1
          (List.mem_toFinset.mp (selected_subset qs bs h))
        cases b <;> simp [selected,hnsel]
      · have hpt : p ∈ qs := (List.mem_cons.mp hp).resolve_left he
        have ht := ih hq.2 bs hlen hpt
        cases b <;> simpa [selected,List.idxOf_cons,he,eq_comm] using ht

theorem address_eq_iff (ports : List E) (x y : Finset E) :
    ports.map (fun p => decide (p ∈ x)) = ports.map (fun p => decide (p ∈ y)) ↔
      x ∩ ports.toFinset = y ∩ ports.toFinset := by
  constructor
  · intro h
    ext p
    by_cases hp : p ∈ ports
    · obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
      have he := congrArg (fun l : List Bool => l[i]?) h
      simp only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
        Option.some.injEq,decide_eq_decide] at he
      simp only [Finset.mem_inter,List.mem_toFinset,hp,and_true]
      exact hpi ▸ he
    · simp [hp]
  · intro h
    apply List.map_congr_left
    intro p hp
    have he := Finset.ext_iff.mp h p
    simpa only [Finset.mem_inter,List.mem_toFinset,hp,and_true,decide_eq_decide] using he

end RiemannGaussian.SemiprimeD1BoundaryCatalogue

namespace RiemannGaussian.SemiprimeD1BoundaryCatalogue
open scoped BigOperators

theorem project_selected (source target : List Nat) (hn : source.Nodup)
    (bits : List Bool) (hl : bits.length = source.length)
    (ht : ∀ p ∈ target, p ∈ source) :
    (SemiprimeD1BoundaryRecords.project bits source target).value =
      target.map (fun p => decide (p ∈ selected source bits)) := by
  rw [SemiprimeD1BoundaryRecordsLookup.project_value]
  apply List.map_congr_left
  intro p hp
  exact (selected_read source hn bits hl p (ht p hp)).symm

/-- Interpret original natural-number occurrence identifiers as finite edges. -/
def lift (m : Nat) (s : Finset Nat) : Finset (Fin m) :=
  Finset.univ.filter (fun e => e.val ∈ s)

@[simp] theorem mem_lift (m : Nat) (s : Finset Nat) (e : Fin m) :
    e ∈ lift m s ↔ e.val ∈ s := by simp [lift]

theorem lift_image (m : Nat) (s : Finset (Fin m)) : lift m (s.image Fin.val) = s := by
  ext e
  simp only [mem_lift,Finset.mem_image,Fin.val_inj,exists_eq_right]

theorem image_lift (m : Nat) (s : Finset Nat) (h : ∀ p ∈ s, p < m) :
    (lift m s).image Fin.val = s := by
  ext p
  simp only [Finset.mem_image,mem_lift]
  constructor
  · rintro ⟨e,he,rfl⟩
    exact he
  · intro hp
    exact ⟨⟨p,h p hp⟩,hp,rfl⟩

theorem lift_inter (m : Nat) (x y : Finset Nat) :
    lift m (x ∩ y) = lift m x ∩ lift m y := by
  ext e
  simp

theorem lift_eq_iff (m : Nat) (x y : Finset Nat)
    (hx : ∀ p ∈ x, p < m) (hy : ∀ p ∈ y, p < m) :
    lift m x = lift m y ↔ x = y := by
  constructor
  · intro h
    have he := congrArg (Finset.image Fin.val) h
    simpa only [image_lift m x hx,image_lift m y hy] using he
  · rintro rfl
    rfl

theorem sum_lift_powerset {R : Type*} [AddCommMonoid R] (m : Nat) (s : Finset Nat)
    (h : ∀ p ∈ s, p < m) (F : Finset (Fin m) → R) :
    (∑ z ∈ s.powerset, F (lift m z)) = ∑ z ∈ (lift m s).powerset, F z := by
  classical
  apply Finset.sum_bij (fun z _ => lift m z)
  · intro z hz
    apply Finset.mem_powerset.mpr
    intro e he
    exact (mem_lift m s e).mpr (Finset.mem_powerset.mp hz ((mem_lift m z e).mp he))
  · intro z hz y hy he
    have hz' := image_lift m z (fun p hp => h p (Finset.mem_powerset.mp hz hp))
    have hy' := image_lift m y (fun p hp => h p (Finset.mem_powerset.mp hy hp))
    rw [←hz',←hy',he]
  · intro z hz
    refine ⟨z.image Fin.val,?_,lift_image m z⟩
    apply Finset.mem_powerset.mpr
    intro p hp
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
    exact (mem_lift m s e).mp (Finset.mem_powerset.mp hz he)
  · intro z _
    rfl

theorem sum_constrained_lift {R : Type*} [AddCommMonoid R] (m : Nat)
    (source target : Finset Nat) (hs : ∀ p ∈ source, p < m) (ht : ∀ p ∈ target, p < m)
    (x : Finset (Fin m)) (F : Finset (Fin m) → R) :
    (∑ z ∈ source.powerset, if z ∩ target = x.image Fin.val ∩ target then F (lift m z) else 0) =
      ∑ z ∈ (lift m source).powerset,
        if z ∩ lift m target = x ∩ lift m target then F z else 0 := by
  classical
  have hcond (z : Finset Nat) : (z ∩ target = x.image Fin.val ∩ target) ↔
      (lift m z ∩ lift m target = x ∩ lift m target) := by
    have hh := (lift_eq_iff m (z ∩ target) (x.image Fin.val ∩ target)
      (fun p hp => ht p (Finset.mem_inter.mp hp).2)
      (fun p hp => ht p (Finset.mem_inter.mp hp).2)).symm
    rw [lift_inter,lift_inter,lift_image m x] at hh
    exact hh
  simp_rw [hcond]
  exact sum_lift_powerset m source hs (fun z =>
    if z ∩ lift m target = x ∩ lift m target then F z else 0)

end RiemannGaussian.SemiprimeD1BoundaryCatalogue
