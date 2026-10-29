/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1GridHistogram

/-! # Original signed-grid valuation sum as an exact translated residue sum -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1GridRawSum
open scoped BigOperators
open SemiprimeD1GridValuation SemiprimeD1GridResidue SemiprimeD1GridHistogram
  SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid

/-- Literal complete residue grid with the actual zero/own node removed. -/
def residueOthers (k : ℕ) (t : ZMod (2^k)) : Finset (ZMod (2^k)) :=
  (Finset.univ.erase 0).erase t

/-- Translated exact raw valuation sum, with the original taper. -/
def residueValuation (k h u : ℕ) (t : ZMod (2^k)) : ℤ :=
  ∑ x∈residueOthers k t,(multiplicity h u (order k x):ℤ)*
    ((order k x:ℤ)-(order k (t-x):ℤ))

/-- Actual original raw grid and residue sums agree by an explicit finite bijection. -/
theorem original_raw_sum (a h u : ℕ) (t : Fin (size a)) :
    rawValuation a h u t.val=residueValuation (a+1) h u (gridEquiv a t) := by
  unfold rawValuation residueValuation
  let idx := fun (q:ℕ) (hq:q∈others a t.val) =>
    (⟨q,Finset.mem_range.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).2⟩:Fin (size a))
  apply Finset.sum_bij (fun q hq => gridEquiv a (idx q hq))
  · intro q hq
    have hmem := (original_membership a t (idx q hq)).mp hq
    exact Finset.mem_erase.mpr ⟨hmem.2,Finset.mem_erase.mpr ⟨hmem.1,Finset.mem_univ _⟩⟩
  · intro q hq r hr he
    exact congrArg Fin.val ((gridEquiv a).injective he)
  · intro x hx
    let q := (gridEquiv a).symm x
    have hq : q.val∈others a t.val := by
      apply (original_membership a t q).mpr
      change gridEquiv a ((gridEquiv a).symm x)≠0 ∧ gridEquiv a ((gridEquiv a).symm x)≠gridEquiv a t
      rw [Equiv.apply_symm_apply]
      exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1,(Finset.mem_erase.mp hx).1⟩
    refine ⟨q.val,hq,?_⟩
    have he : idx q.val hq=q := Fin.ext rfl
    rw [he]
    exact (gridEquiv a).apply_symm_apply x
  · intro q hq
    have hqc : q≠center a := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    have hqt : idx q hq≠t := by intro he;exact (Finset.mem_erase.mp hq).1 (congrArg Fin.val he)
    rw [original_order a (idx q hq) hqc,original_difference_order a t (idx q hq) hqt]
    rfl

/-- Every original residue raw sum is supported on genuine nonzero values. -/
theorem residue_membership (k : ℕ) (t x : ZMod (2^k)) :
    x∈residueOthers k t ↔ x≠0 ∧ x≠t := by
  simp only [residueOthers,Finset.mem_erase,Finset.mem_univ,and_true]
  tauto

/-- The ORIGINAL own/zero-node exclusion is preserved by literal reflection. -/
theorem residue_reflect (k : ℕ) (t x : ZMod (2^k)) :
    x∈residueOthers k t ↔ (t-x)∈residueOthers k t := by
  rw [residue_membership,residue_membership]
  exact reflect_membership k t x

end RiemannGaussian.SemiprimeD1GridRawSum
