/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdMetadata
import RiemannGaussian.SemiprimeMaterializedSourceWords

/-! # The two original incidence equalities have disjoint variable namespaces
Original owners are left indices and factors are right indices. Completeness
of the actually acquired index list proves every cross-namespace inequality;
this is not an added restriction on the original source family.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceIncidenceNamespaces
open OAI.Algorithms.SubexponentialSAT.LocalExpectation
open SemiprimeMaterializedScoreEnvironment

/-- The owner-equality endpoints are disjoint from the factor-equality endpoints. -/
def Separated {Q : ℕ} : ScoreProgram Q → Prop
  | .incidence a b c d => a≠b ∧ a≠d ∧ c≠b ∧ c≠d
  | .head _ _ _ => True

/-- Original complete index scans distinguish left and right source variables. -/
theorem indexCode_cross {V E : Type*} [DecidableEq V] [DecidableEq E]
    (indices : List (V ⊕ E)) (hc : ∀ z,z∈indices) (v : V) (e : E) :
    indexCode indices (.inl v)≠indexCode indices (.inr e) := by
  let : BEq (V ⊕ E) := ⟨fun x y => decide (x=y)⟩
  have : LawfulBEq (V ⊕ E) := {
    eq_of_beq := of_decide_eq_true
    rfl := of_decide_eq_self_eq_true _ }
  intro h
  have he := (List.idxOf_inj (hc (.inl v))).mp h
  cases he

/-- Every original incidence descriptor has independent variable namespaces. -/
theorem descriptor_separated {I V E : Type*} [DecidableEq V] [DecidableEq E]
    {Q : ℕ} (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (hc : ∀ z,z∈indices)
    (z : OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.ScoreTerm I V Q) :
    Separated (SemiprimeMaterializedSourceWords.descriptor owner factor indices z) := by
  cases z with
  | inl pair =>
    rcases pair with ⟨i,j⟩
    exact ⟨indexCode_cross indices hc (owner i) (factor i),
      indexCode_cross indices hc (owner i) (factor j),
      indexCode_cross indices hc (owner j) (factor i),
      indexCode_cross indices hc (owner j) (factor j)⟩
  | inr head => trivial

/-- Actual descriptor compilation preserves this original structural property. -/
theorem compileAll_separated {I V E : Type*} [DecidableEq V] [DecidableEq E]
    {Q : ℕ} (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (hc : ∀ z,z∈indices)
    (terms : List (OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.ScoreTerm I V Q)) :
    ∀ p∈(SemiprimeMaterializedSourceWords.compileAll owner factor indices terms).value,
      Separated p := by
  rw [SemiprimeMaterializedSourceWords.compileAll_value]
  intro p hp
  rcases List.mem_map.mp hp with ⟨z,_,rfl⟩
  exact descriptor_separated owner factor indices hc z

/-- The original indexed caller itself supplies all namespace conditions. -/
theorem indexed_programs_separated (n F Q : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    let metadata := SemiprimeSourceWordIdMetadata.acquire n F Q arity
    ∀ p∈(SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst metadata.indices metadata.terms).value,
      Separated p := by
  exact compileAll_separated owner Sigma.fst _
    (SemiprimeSourceWordIdMetadata.indices_certificate n F Q arity).2 _

end RiemannGaussian.SemiprimeSourceIncidenceNamespaces
