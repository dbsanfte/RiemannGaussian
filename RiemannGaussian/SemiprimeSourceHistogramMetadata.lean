/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdMetadata

/-! # Original source ports and indices without the quadratic score menu
Forward finite-index construction avoids repeated successor maps. Only actual
vertices, factors, incidences, coordinates and variable indices are acquired.
The report counts native finite metadata/control and list operations explicitly;
it is not a complete primitive-bit input decoder.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeSourceHistogramMetadata
open scoped BigOperators
open SemiprimeMaterializedSourceUniversal
open SemiprimePaidFiniteEnumerationLists

/-- Emit a bounded ascending finite-index segment using one new cell per step. -/
def finFrom (n : ℕ) : (m start : ℕ) → start+m ≤ n → Run (List (Fin n))
  | 0,_,_ => ⟨[],1⟩
  | m+1,start,h =>
    let rest := finFrom n m (start+1) (by omega)
    ⟨⟨start,by omega⟩::rest.value,rest.work+4⟩

/-- Actual emitted numeric indices are the literal ascending segment. -/
theorem finFrom_values (n m start : ℕ) (h : start+m ≤ n) :
    ((finFrom n m start h).value.map Fin.val)=List.range' start m := by
  induction m generalizing start with
  | zero => rfl
  | succ m ih =>
    simp only [finFrom,List.map_cons,ih]
    rfl

/-- Every segment step retains its finite-counter and constructor work. -/
theorem finFrom_work (n m start : ℕ) (h : start+m ≤ n) :
    (finFrom n m start h).work=4*m+1 := by
  induction m generalizing start with
  | zero => rfl
  | succ m ih => simp only [finFrom,ih];omega

/-- Acquire the full original index list without quadratic successor maps. -/
def finFast (n : ℕ) : Run (List (Fin n)) := finFrom n n 0 (by omega)

/-- Exact original ordered finite enumeration. -/
theorem finFast_value (n : ℕ) : (finFast n).value=List.finRange n := by
  apply ((List.map_injective_iff (f := fun i : Fin n => i.val)).mpr Fin.val_injective)
  change (finFrom n n 0 _).value.map Fin.val=_
  rw [finFrom_values,List.map_coe_finRange,List.range_eq_range']

/-- Actual finite construction is linear in its native dimension. -/
theorem finFast_work (n : ℕ) : (finFast n).work=4*n+1 := finFrom_work n n 0 _

/-- One factor's actual original dependent incidence list. -/
def ports {F : ℕ} (arity : Fin F → ℕ) (e : Fin F) :
    Run (List ((e : Fin F) × Fin (arity e))) :=
  let ids := finFast (arity e)
  let out := SemiprimeMaterializedSourceUniversal.collect
    (fun i => (⟨Sigma.mk e i,1⟩ : Run ((e : Fin F) × Fin (arity e)))) ids.value
  ⟨out.value,ids.work+out.work+2⟩

/-- Port values retain the exact original factor-major order and occurrences. -/
theorem ports_value {F : ℕ} (arity : Fin F → ℕ) (e : Fin F) :
    (ports arity e).value=(List.finRange (arity e)).map (Sigma.mk e) := by
  simp only [ports,SemiprimeMaterializedSourceUniversal.collect_value,finFast_value]

/-- Actual port acquisition and every map cell remain linear. -/
theorem ports_work {F : ℕ} (arity : Fin F → ℕ) (e : Fin F) :
    (ports arity e).work ≤ 7*arity e+4 := by
  have h := SemiprimeMaterializedSourceUniversal.collect_work
    (fun i => (⟨Sigma.mk e i,1⟩ : Run ((e : Fin F) × Fin (arity e))))
    (finFast (arity e)).value 1 (fun _ _ => le_rfl)
  rw [finFast_value,List.length_finRange] at h
  simp only [ports,finFast_work,finFast_value]
  omega

/-- A flattened actual list report can be bounded by the sum of child sizes,
without multiplying the largest child by every factor. -/
theorem flat_work_sum {α β : Type*} (f : α → Run (List β)) (xs : List α)
    (g : α → ℕ) (C D : ℕ)
    (hc : ∀ a∈xs,(f a).work ≤ C*g a+D) (hl : ∀ a∈xs,(f a).value.length ≤ g a) :
    (flat f xs).work ≤ (C+1)*(xs.map g).sum+(D+2)*xs.length+1 := by
  induction xs with
  | nil => simp [flat]
  | cons a xs ih =>
    have ha := hc a List.mem_cons_self
    have hla := hl a List.mem_cons_self
    have ht := ih (fun a h => hc a (List.mem_cons_of_mem _ h))
      (fun a h => hl a (List.mem_cons_of_mem _ h))
    simp only [flat,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- The original graph metadata actually consumed by sparse source queries. -/
structure Metadata (n F Q : ℕ) (arity : Fin F → ℕ) where
  /-- Original vertex order. -/
  vertices : List (Fin n)
  /-- Original factor order. -/
  factors : List (Fin F)
  /-- All original ports, retaining their dependent factor/slot keys. -/
  incidences : List ((e : Fin F) × Fin (arity e))
  /-- All original colour coordinates. -/
  coordinates : List (Fin Q)
  /-- Original left-variable/right-factor index order. -/
  indices : List (Fin n ⊕ Fin F)
  /-- Actual native metadata, list and finite-control work. -/
  clock : ℕ

/-- Acquire original sparse metadata directly; no score-pair or word menu is built. -/
def acquire (n F Q : ℕ) (arity : Fin F → ℕ) : Metadata n F Q arity :=
  let vs := finFast n
  let fs := finFast F
  let qs := finFast Q
  let is := flat (ports arity) fs.value
  let ids := SemiprimePaidFiniteEnumerationLists.sum vs.value fs.value
  ⟨vs.value,fs.value,is.value,qs.value,ids.value,vs.work+fs.work+qs.work+is.work+ids.work+5⟩

/-- The acquired graph/index fields equal the previous original constructor. -/
theorem original_fields (n F Q : ℕ) (arity : Fin F → ℕ) :
    (acquire n F Q arity).incidences=(SemiprimeSourceWordIdMetadata.acquire n F Q arity).incidences ∧
      (acquire n F Q arity).indices=(SemiprimeSourceWordIdMetadata.acquire n F Q arity).indices := by
  constructor
  · simp only [acquire,SemiprimeSourceWordIdMetadata.acquire,flat_value,finFast_value,ports_value,
      SemiprimePaidFiniteEnumerations.incidences,fin_value,
      SemiprimePaidFiniteEnumerations.ports_value]
  · simp only [acquire,SemiprimeSourceWordIdMetadata.acquire,sum_value,finFast_value,fin_value]

/-- All original input dimensions are obtained from literal acquired lists. -/
theorem sizes (n F Q : ℕ) (arity : Fin F → ℕ) :
    (acquire n F Q arity).vertices.length=n ∧ (acquire n F Q arity).factors.length=F ∧
      (acquire n F Q arity).incidences.length=(∑ e,arity e) ∧
      (acquire n F Q arity).coordinates.length=Q ∧ (acquire n F Q arity).indices.length=n+F := by
  have hs := SemiprimeSourceWordIdMetadata.sizes n F Q arity
  have hf := original_fields n F Q arity
  exact ⟨by simp [acquire,finFast_value],by simp [acquire,finFast_value],
    by rw [hf.1];exact hs.1,by simp [acquire,finFast_value],by rw [hf.2];exact hs.2.2⟩

/-- Original complete index certificate follows from the actual acquired data. -/
theorem indices_certificate (n F Q : ℕ) (arity : Fin F → ℕ) :
    (acquire n F Q arity).indices.Nodup ∧ ∀ z,z∈(acquire n F Q arity).indices := by
  rw [(original_fields n F Q arity).2]
  exact SemiprimeSourceWordIdMetadata.indices_certificate n F Q arity

/-- Linear native metadata envelope, with total port count M, not M squared. -/
def budget (n F Q M : ℕ) : ℕ := 8*n+14*F+4*Q+8*M+13

/-- Every acquired port, original index and coordinate is paid once. -/
theorem acquire_clock (n F Q : ℕ) (arity : Fin F → ℕ) :
    (acquire n F Q arity).clock ≤ budget n F Q (∑ e,arity e) := by
  have hs : ((finFast F).value.map arity).sum=∑ e,arity e := by
    rw [finFast_value,← List.ofFn_eq_map]
    exact List.sum_ofFn
  have hp := flat_work_sum (ports arity) (finFast F).value arity 7 4
    (fun e _ => ports_work arity e)
    (fun e _ => by simp [ports_value])
  rw [hs,finFast_value,List.length_finRange] at hp
  have hi := SemiprimePaidFiniteEnumerationLists.sum_work (finFast n).value (finFast F).value
  rw [finFast_value,finFast_value,List.length_finRange,List.length_finRange] at hi
  unfold acquire budget
  dsimp only
  simp only [finFast_work,finFast_value]
  omega

end RiemannGaussian.SemiprimeSourceHistogramMetadata
