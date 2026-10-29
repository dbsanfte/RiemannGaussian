import RiemannGaussian.SemiprimeD1BoundaryLeafCorrectness

/-! Exact finite Boolean address enumeration of the executed boundary source. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryAddresses
open scoped BigOperators
open SemiprimeD1BoundaryRecords

theorem assignments_mem (n : Nat) (bits : List Bool) :
    bits ∈ (assignments n).value ↔ bits.length = n := by
  induction n generalizing bits with
  | zero => simp [assignments]
  | succ n ih =>
    cases bits with
    | nil => simp [assignments]
    | cons b bs =>
      cases b <;> simp [assignments, ih]

theorem assignments_nodup (n : Nat) : (assignments n).value.Nodup := by
  induction n with
  | zero => simp [assignments]
  | succ n ih =>
    simp only [assignments, List.nodup_append]
    refine ⟨ih.map (by intro a b h; exact List.cons.inj h |>.2),
      ih.map (by intro a b h; exact List.cons.inj h |>.2), ?_⟩
    simp

/-- The false-first catalogue sums each finite assignment once. -/
theorem assignments_sum {R : Type*} [AddCommMonoid R]
    (n : Nat) (F : List Bool → R) :
    ((assignments n).value.map F).sum = ∑ bits : Fin n → Bool, F (List.ofFn bits) := by
  induction n generalizing F with
  | zero => simp [assignments]
  | succ n ih =>
    simp only [assignments, List.map_append, List.sum_append, List.map_map]
    rw [ih, ih]
    rw [← (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool)))]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.consEquiv_apply,
      List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def]
    exact add_comm _ _

open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryLeafCorrectness
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1JetInterpretation (interpret)
open SemiprimeD1JetAxes (Context)

/-- The actual bucket sums exactly its incident assignments, with unit seed
eliminated in the current quotient ring, including precision zero. -/
theorem bucket_finite_sum (ctx : Context) (hp : ctx.Positive)
    (g : SemiprimeD1BoundaryPlan.Graph) (vertices : List Vertex)
    (colours : List Nat) (c : Nat) (key : List Bool) :
    weighted ctx (bucket ctx g vertices colours c).value.entries key =
      ∑ bits : Fin (classPorts g colours c).1.length → Bool,
        if (project (List.ofFn bits) (classPorts g colours c).1
          (classPorts g colours c).2).value = key then
          ((classVertices vertices colours c).map (fun v =>
            interpret ctx (SemiprimeD1TensorTables.lookup v.table
              (project (List.ofFn bits) (classPorts g colours c).1 v.ports).value).words)).prod
        else 0 := by
  rw [bucket_weighted ctx hp]
  simp only [seed, List.map_map, Function.comp_def,
    SemiprimeD1JetAffineCoefficient.interpret_one ctx hp, one_mul]
  exact assignments_sum _ _

end RiemannGaussian.SemiprimeD1BoundaryAddresses
