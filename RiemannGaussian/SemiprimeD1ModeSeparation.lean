/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1AcquiredModeSum

/-! # D.16 finite algebra over the actual acquired mode menu

Every mode has one target row family and one source bit family. The requested
coefficient separates over targets; monomial substitution separates over sources;
the independent bit sums then factor. The actual physical child graph, packet
entry recipe and creator-context joins remain separate from this algebraic law.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1ModeSeparation
open scoped BigOperators
open SemiprimeD1WeightedPolynomial SemiprimeD1SeparatedCoefficient
variable {G R : Type*} [CommRing R] [Fintype G]
variable {Bits : G→Type*}
attribute [local instance] Classical.propDecidable

/-- One group's exact coefficient and source-power factor for the acquired tuple. -/
noncomputable def groupTerm (A : (g : G)→Bits g→R)
    (Q : (g : G)→Bits g→MvPolynomial ℕ R)
    (target source : ℕ→G) (L : (g : G)→ℕ→Bits g→R)
    (beta : List ℕ) (g : G) (bits : Bits g) : R :=
  A g bits*(Q g bits).coeff (restrict {j|target j=g} beta.toFinsupp)*
    (beta.toFinsupp.prod fun j n => if source j=g then L g j bits^n else 1)

/-- Monomial substitution distributes exactly over the UNIQUE source of each mode. -/
theorem source_factor (source : ℕ→G) (L : (g : G)→ℕ→Bits g→R)
    (e : ℕ→₀ℕ) (bits : (g : G)→Bits g) :
    (∏ g,e.prod fun j n => if source j=g then L g j (bits g)^n else 1)=
      e.prod (fun j n => L (source j) j (bits (source j))^n) := by
  classical
  unfold Finsupp.prod
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  exact Fintype.prod_ite_eq (source j) (fun g => L g j (bits g)^e j)

/-- A single acquired mode term factors before any parent assignment sum or matrix. -/
theorem term_factor (A : (g : G)→Bits g→R)
    (Q : (g : G)→Bits g→MvPolynomial ℕ R)
    (target source : ℕ→G) (L : (g : G)→ℕ→Bits g→R)
    (howner : ∀g b,On {j|target j=g} (Q g b))
    (beta : List ℕ) (bits : (g : G)→Bits g) :
    (∏ g,A g (bits g))*(∏ g,Q g (bits g)).coeff beta.toFinsupp*
      (beta.toFinsupp.prod fun j n => L (source j) j (bits (source j))^n)=
        ∏ g,groupTerm A Q target source L beta g (bits g) := by
  classical
  rw [coefficient_all_owners target (fun g => Q g (bits g)) (fun g => howner g (bits g)),
    ←source_factor source L beta.toFinsupp bits]
  simp only [groupTerm,Finset.prod_mul_distrib]

variable [∀g,Fintype (Bits g)]

/-- ORIGINAL acquired tuples suffice for the complete finite separated contraction.
This is a universal ring identity, not an implementation or runtime oracle for
the original graph's tensor entries or child contractions. -/
theorem contraction (ws : List ℕ) (hw : ∀w∈ws,0<w) (p : ℕ) (hp : 0<p)
    (f : ZMod (2^p)→+*R) (A : (g : G)→Bits g→R)
    (Q : (g : G)→Bits g→MvPolynomial ℕ R)
    (target source : ℕ→G) (L : (g : G)→ℕ→Bits g→R)
    (hweight : ∀g b,Weighted (SemiprimeD1AcquiredModeSum.weight ws) (Q g b))
    (hfinite : ∀g b,On {j|j<ws.length} (Q g b))
    (howner : ∀g b,On {j|target j=g} (Q g b)) :
    (∑ bits : (g : G)→Bits g,(∏ g,A g (bits g))*
      MvPolynomial.eval (fun j => L (source j) j (bits (source j))) (∏ g,Q g (bits g)))=
        ((SemiprimeD1WeightedTuples.acquire ws (p-1)).values.map fun beta =>
          ∏ g,∑ bits : Bits g,groupTerm A Q target source L beta g bits).sum := by
  classical
  let modes := (SemiprimeD1WeightedTuples.acquire ws (p-1)).values
  have hn : modes.Nodup := by
    change (SemiprimeD1WeightedTuples.acquire ws (p-1)).values.Nodup
    rw [SemiprimeD1WeightedTuples.acquire_values]
    exact SemiprimeD1WeightedTuples.nodup _ _
  have hpoint (bits : (g : G)→Bits g) :
      (∏ g,A g (bits g))*
        MvPolynomial.eval (fun j => L (source j) j (bits (source j))) (∏ g,Q g (bits g))=
      ∑ beta∈modes.toFinset,∏ g,groupTerm A Q target source L beta g (bits g) := by
    have he := SemiprimeD1AcquiredModeSum.eval_acquired ws hw p hp (∏ g,Q g (bits g))
      (weighted_prod _ _ _ (fun g _ => hweight g (bits g)))
      (on_prod _ _ _ (fun g _ => hfinite g (bits g))) f
      (fun j => L (source j) j (bits (source j)))
    change MvPolynomial.eval _ _=(modes.map _).sum at he
    rw [←List.sum_toFinset _ hn] at he
    rw [he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro beta _
    simpa only [mul_assoc] using term_factor A Q target source L howner beta bits
  calc
    _ = ∑ bits : (g : G)→Bits g,∑ beta∈modes.toFinset,
          ∏ g,groupTerm A Q target source L beta g (bits g) :=
      Finset.sum_congr rfl (fun bits _ => hpoint bits)
    _ = ∑ beta∈modes.toFinset,∑ bits : (g : G)→Bits g,
          ∏ g,groupTerm A Q target source L beta g (bits g) := Finset.sum_comm
    _ = ∑ beta∈modes.toFinset,∏ g,∑ bits : Bits g,
          groupTerm A Q target source L beta g bits := by
      apply Finset.sum_congr rfl
      intro beta _
      exact (Fintype.prod_sum (fun g bits => groupTerm A Q target source L beta g bits)).symm
    _ = _ := List.sum_toFinset _ hn

end RiemannGaussian.SemiprimeD1ModeSeparation
