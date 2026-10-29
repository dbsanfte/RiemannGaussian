/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PublicCounter

/-! # The concrete public search and decoder from exact actual prefix counts
These semantic assembly lemmas concern the fixed executed counter and search.
The exact-count proposition is proof-side only; the following public-correctness
module discharges it from the actual recursive counter and original root tables.
No runtime count function, layout or factor supplier is introduced here.
-/
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PublicCountConsequences
open SemiprimePublicAcquiredExecution SemiprimeCountRecovery SemiprimeCounterSearch
open SemiprimeMacroGraphSemantics
noncomputable section
attribute [local irreducible] SemiprimePublicAcquiredExecution.indexedPredicate
  SemiprimePublicAcquiredExecution.decodeOperand

/-- All original-prefix queries of the fixed actual new counter are exact.
This proposition is never an input to any executed public routine. -/
def ExactCounts (N : ℕ) (hN : 0 < N) : Prop :=
  ∀ fixed : List (Fin (wireCount N) × Bool),
    SemiprimeD1PublicCounter.prefixCount N hN fixed =
      acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed)

/-- The actual selected prefix has one common ORIGINAL accepted assignment. -/
theorem search_sound (N : ℕ) (hN : 0 < N) (hcount : ExactCounts N hN)
    (values : List (Fin (wireCount N) × Bool))
    (h : (SemiprimeD1PublicCounter.search N hN).values = some values) :
    values.map Prod.fst = List.finRange (wireCount N) ∧
      ∃ x,indexedPredicate N hN x = true ∧ ∀ pair ∈ values,assignmentBit x pair.1 = pair.2 := by
  exact SemiprimeCountRecovery.search_some_sound (SemiprimeD1PublicCounter.prefixCount N hN)
    assignmentBit (indexedPredicate N hN) hcount (List.finRange (wireCount N)) values h

/-- The fixed literal decoder recovers a true ordinary factor pair from the
actual new search result, with no modular-only factor interpretation. -/
theorem selected_factor_pair (N : ℕ) (hN : 0 < N) (hcount : ExactCounts N hN)
    (values : List (Fin (wireCount N) × Bool))
    (h : (SemiprimeD1PublicCounter.search N hN).values = some values) :
    2 ≤ decodeOperand N values 0 ∧ 2 ≤ decodeOperand N values 1 ∧
      decodeOperand N values 0 * decodeOperand N values 1 = N := by
  obtain ⟨hindices,x,hx,hbits⟩ := search_sound N hN hcount values h
  have hcover (i : Fin (wireCount N)) : ∃ pair ∈ values,pair.1 = i := by
    have hi : i ∈ values.map Prod.fst := by
      rw [hindices]
      exact List.mem_finRange i
    exact List.mem_map.mp hi
  have heq : SemiprimeAcquiredPrefixSearch.selectedBits values = assignmentBit x := by
    funext i
    exact SemiprimeAcquiredPrefixSearch.selectedBits_eq values _ hcover hbits i
  have hp := subdivided_factor_pair (SemiprimePublicFactorCount.publicConfig N hN) _
    (indexed_to_public N hN x hx)
  have hdec (side : Fin 2) : decodeOperand N values side =
      sourceOperand (SemiprimePublicFactorCount.publicConfig N hN)
        (fun signal => assignmentBit x ((edgeEnumeration N).equivFin.symm (signal,false))) side := by
    have he : (fun signal => SemiprimeAcquiredPrefixSearch.selectedBits values
        ((edgeEnumeration N).equivFin.symm (signal,false))) =
        (fun signal => assignmentBit x ((edgeEnumeration N).equivFin.symm (signal,false))) := by
      funext signal
      exact congrFun heq _
    exact (decodeOperand_eq N hN values side).trans
      (congrArg (fun input => sourceOperand (SemiprimePublicFactorCount.publicConfig N hN) input side) he)
  refine ⟨hp.1.trans_eq (hdec 0).symm,hp.2.1.trans_eq (hdec 1).symm,?_⟩
  exact ((congrArg₂ (fun a b : ℕ => a*b) (hdec 0) (hdec 1)).trans hp.2.2).trans
    (SemiprimePublicFactorCount.public_target_value N hN)

/-- Every actual semiprime has an accepted original arithmetic-checker assignment,
including the repeated-prime case. No assignment is supplied to the algorithm. -/
theorem semiprime_accepted_nonempty (N p q : ℕ) (hN : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N = p*q) : ∃ x,indexedPredicate N hN x = true := by
  have hpN : p ≤ N := by
    have hm := Nat.mul_le_mul_left p (show 1 ≤ q by have := hq.two_le;omega)
    simpa only [Nat.mul_one,← hsem] using hm
  have hqN : q ≤ N := by
    have hm := Nat.mul_le_mul_right q (show 1 ≤ p by have := hp.two_le;omega)
    simpa only [Nat.one_mul,← hsem] using hm
  let pair : SemiprimePublicFactorCount.OrdinaryFactors N :=
    ⟨(⟨p,by omega⟩,⟨q,by omega⟩),hp.two_le,hq.two_le,hsem.symm⟩
  apply (acceptedCount_pos_iff (indexedPredicate N hN)).mp
  rw [indexed_factor_count N hN]
  exact Fintype.card_pos_iff.mpr ⟨pair⟩

/-- The fixed actual new search cannot fail on a semiprime once its own prefix
counts are exact. Only a proof proposition, not a runtime count, is assumed. -/
theorem search_exists (N p q : ℕ) (hN : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N = p*q) (hcount : ExactCounts N hN) :
    ∃ values,(SemiprimeD1PublicCounter.search N hN).values = some values := by
  have hs := SemiprimeCountRecovery.search_none_iff (SemiprimeD1PublicCounter.prefixCount N hN)
    assignmentBit (indexedPredicate N hN) hcount (List.finRange (wireCount N))
  have he := semiprime_accepted_nonempty N p q hN hp hq hsem
  cases hv : (SemiprimeD1PublicCounter.search N hN).values with
  | none => exact False.elim ((hs.mp hv) he)
  | some values => exact ⟨values,rfl⟩

/-- Actual search, integer decoding and validation return one of the two prime
factors. The later closed theorem supplies ExactCounts from the recursive run. -/
theorem factor_complete (N p q : ℕ) (hN : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N = p*q) (hcount : ExactCounts N hN) :
    ∃ d,SemiprimeD1PublicCounter.factor N = some d ∧
      2 ≤ d ∧ d < N ∧ N%d = 0 ∧ (d = p ∨ d = q) := by
  obtain ⟨values,hvalues⟩ := search_exists N p q hN hp hq hsem hcount
  obtain ⟨hle,hright,hprod⟩ := selected_factor_pair N hN hcount values hvalues
  let d := decodeOperand N values 0
  have hlt : d < N := by dsimp only [d];nlinarith
  have hdvd : d ∣ N := ⟨decodeOperand N values 1,hprod.symm⟩
  have hmod : N%d = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hprime : d = p ∨ d = q := SemiprimeD1SemiprimePrefix.left_factor_eq p q d
    (decodeOperand N values 1) hp hq hle hright (hprod.trans hsem)
  refine ⟨d,?_,hle,hlt,hmod,hprime⟩
  unfold SemiprimeD1PublicCounter.factor
  rw [dite_eq_left hN,hvalues]
  exact ite_eq_left ⟨hle,hlt,hmod⟩

end
end RiemannGaussian.SemiprimeD1PublicCountConsequences
