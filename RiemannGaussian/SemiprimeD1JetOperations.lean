/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetInterpretation

/-! # Executed word operations preserve the concrete nilpotent quotient algebra
No caller-provided algebra or operation-refinement oracle is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1JetOperations
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetBoxIndex SemiprimeD1JetInterpretation
open SemiprimeBitArithmetic
noncomputable section

/-- Actual output addition coefficient, from literal cached output reads. -/
theorem add_coefficient (ctx : Context) (a b : List (List Bool)) (i : ℕ) (hi : i<ctx.rank) :
    SemiprimeD1JetRingBits.coefficient ctx (SemiprimeD1JetRingBits.add ctx a b).words i=
      SemiprimeD1JetRingBits.coefficient ctx a i+SemiprimeD1JetRingBits.coefficient ctx b i := by
  simpa only [SemiprimeD1JetRingBits.coefficient,SemiprimeD1JetRingBits.add,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some] using
      SemiprimeD1JetRingBits.addAt_value ctx a b i

/-- Actual output product coefficient, from literal cached output reads. -/
theorem mul_coefficient (ctx : Context) (a b : List (List Bool)) (i : ℕ) (hi : i<ctx.rank) :
    SemiprimeD1JetRingBits.coefficient ctx (SemiprimeD1JetRingBits.mul ctx a b).words i=
      SemiprimeD1JetRingBits.convolution ctx a b i := by
  simpa only [SemiprimeD1JetRingBits.coefficient,SemiprimeD1JetRingBits.mul,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some] using
      SemiprimeD1JetRingBits.mulAt_value ctx a b i

/-- Concrete quotient-basis insertion is an actual additive homomorphism. -/
def basisAdd (ctx : Context) (i : ℕ) : ZMod (2^ctx.precision)→+Carrier ctx :=
  (SemiprimeD1JetAlgebra.project (R:=ZMod (2^ctx.precision)) (dims ctx.axes)).toAddMonoidHom.comp
    (MvPowerSeries.monomial (R:=ZMod (2^ctx.precision)) (exponent ctx.axes i)).toAddMonoidHom

/-- Additive basis insertion is the literal original monomial interpretation. -/
theorem basisAdd_apply (ctx : Context) (i : ℕ) (c : ZMod (2^ctx.precision)) :
    basisAdd ctx i c=basis ctx i c := rfl

/-- Zero coefficients produce quotient zero. -/
theorem basis_zero (ctx : Context) (i : ℕ) : basis ctx i 0=0 := (basisAdd ctx i).map_zero

/-- Basis insertion preserves all finite acquired coefficient sums. -/
theorem basis_sum {I : Type*} (ctx : Context) (i : ℕ) (is : Finset I)
    (f : I→ZMod (2^ctx.precision)) : basis ctx i (∑j∈is,f j)=∑j∈is,basis ctx i (f j) :=
  map_sum (basisAdd ctx i) f is

/-- Native context routing is exactly multiplication of concrete quotient monomials. -/
theorem basis_product (ctx : Context) (hpos : ∀q∈ctx.axes,0<q) (i j : ℕ)
    (hi : i<ctx.rank) (hj : j<ctx.rank) (a b : ZMod (2^ctx.precision)) :
    basis ctx i a*basis ctx j b=
      if SemiprimeD1JetRouting.admissible ctx.axes i j then
        basis ctx (SemiprimeD1JetRouting.sumIndex ctx.axes i j) (a*b) else 0 := by
  classical
  change SemiprimeD1JetAlgebra.project (dims ctx.axes) (MvPowerSeries.monomial (exponent ctx.axes i) a)*
    SemiprimeD1JetAlgebra.project (dims ctx.axes) (MvPowerSeries.monomial (exponent ctx.axes j) b)=_
  rw [←map_mul,MvPowerSeries.monomial_mul_monomial]
  by_cases ha : SemiprimeD1JetRouting.admissible ctx.axes i j
  · simp only [ha,ite_true,basis,exponent_sumIndex ctx.axes i j hpos ha]
  · simp only [ha,ite_false]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    intro e he
    have hn : ¬SemiprimeD1JetAlgebra.InBox (dims ctx.axes) (exponent ctx.axes i+exponent ctx.axes j) :=
      (admissible_iff_inBox_sum ctx.axes i j hpos hi hj).not.mp ha
    have hne : e≠exponent ctx.axes i+exponent ctx.axes j := fun h=>hn (h ▸ he)
    simp only [MvPowerSeries.coeff_monomial,hne,ite_false]

/-- Concrete actual acquired addition agrees with the built quotient's addition. -/
theorem interpret_add (ctx : Context) (a b : List (List Bool)) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (SemiprimeD1JetRingBits.add ctx a b).words=interpret ctx a+interpret ctx b := by
  apply SemiprimeD1JetAlgebra.ext (dims ctx.axes)
  intro e he
  let i:=(boxEquiv ctx.axes hpos).symm ⟨e,he⟩
  have hindex : exponent ctx.axes i.val=e :=
    congrArg Subtype.val ((boxEquiv ctx.axes hpos).apply_symm_apply ⟨e,he⟩)
  have hA:=coefficient_interpret ctx (SemiprimeD1JetRingBits.add ctx a b).words hpos i.val i.isLt
  have ha:=coefficient_interpret ctx a hpos i.val i.isLt
  have hb:=coefficient_interpret ctx b hpos i.val i.isLt
  have hval:=add_coefficient ctx a b i.val i.isLt
  simp only [hindex] at hA ha hb
  rw [quotient_coefficient_add]
  exact hA.trans (hval.trans (congrArg₂ (·+·) ha.symm hb.symm))

/-- Literal range-list sums are exactly finite dense-coordinate sums. -/
theorem sum_range_list {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ→R) :
    ((List.range N).map f).sum=∑i : Fin N,f i.val := by
  rw [Fin.sum_univ_eq_sum_range]
  simpa only [List.toFinset_range] using (List.sum_toFinset f (List.nodup_range (n:=N))).symm

/-- Literal flattening of a finite list of coefficient lists preserves its sum. -/
theorem list_sum_flatMap {I R : Type*} [AddMonoid R] (xs : List I) (f : I→List R) :
    (xs.flatMap f).sum=(xs.map (fun i => (f i).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [List.flatMap_cons,List.sum_append,ih]

/-- The actual native pair plan is the complete finite two-index convolution. -/
theorem convolution_finite (ctx : Context) (a b : List (List Bool)) (k : ℕ) :
    SemiprimeD1JetRingBits.convolution ctx a b k=
      ∑i : Fin ctx.rank,∑j : Fin ctx.rank,
        if SemiprimeD1JetRouting.admissible ctx.axes i.val j.val ∧
          SemiprimeD1JetRouting.sumIndex ctx.axes i.val j.val=k then
          SemiprimeD1JetRingBits.coefficient ctx a i.val*SemiprimeD1JetRingBits.coefficient ctx b j.val else 0 := by
  unfold SemiprimeD1JetRingBits.convolution SemiprimeD1JetRingBits.plan
  simp only [List.map_flatMap,list_sum_flatMap,List.map_map,Function.comp_def]
  rw [sum_range_list]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_range_list _ _

/-- Summing the actual unique admitted destination gives the concrete basis product. -/
theorem routed_basis_sum (ctx : Context) (hpos : ∀q∈ctx.axes,0<q) (i j : Fin ctx.rank)
    (a b : ZMod (2^ctx.precision)) :
    (∑k : Fin ctx.rank,basis ctx k.val
      (if SemiprimeD1JetRouting.admissible ctx.axes i.val j.val ∧
        SemiprimeD1JetRouting.sumIndex ctx.axes i.val j.val=k.val then a*b else 0))=
      basis ctx i.val a*basis ctx j.val b := by
  classical
  rw [basis_product ctx hpos _ _ i.isLt j.isLt]
  by_cases ha : SemiprimeD1JetRouting.admissible ctx.axes i.val j.val
  · simp only [ha,true_and,ite_true]
    let target : Fin ctx.rank:=⟨SemiprimeD1JetRouting.sumIndex ctx.axes i.val j.val,
      SemiprimeD1JetRouting.sumIndex_lt ctx.axes _ _ hpos ha⟩
    rw [Finset.sum_eq_single target]
    · simp only [target,ite_true]
    · intro k _ hk
      have hn : SemiprimeD1JetRouting.sumIndex ctx.axes i.val j.val≠k.val := by
        intro he
        exact hk (Fin.ext he.symm)
      simp only [hn,ite_false,basis_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_univ target))
  · simp only [ha,false_and,ite_false,basis_zero,Finset.sum_const_zero]

/-- The actual executed truncated schoolbook product agrees with the concrete
CommRing multiplication, with every ring/route interpretation derived internally. -/
theorem interpret_mul (ctx : Context) (a b : List (List Bool)) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (SemiprimeD1JetRingBits.mul ctx a b).words=interpret ctx a*interpret ctx b := by
  classical
  have hinit : interpret ctx (SemiprimeD1JetRingBits.mul ctx a b).words=
      ∑k : Fin ctx.rank,∑i : Fin ctx.rank,∑j : Fin ctx.rank,basis ctx k.val
        (if SemiprimeD1JetRouting.admissible ctx.axes i.val j.val ∧
          SemiprimeD1JetRouting.sumIndex ctx.axes i.val j.val=k.val then
          SemiprimeD1JetRingBits.coefficient ctx a i.val*SemiprimeD1JetRingBits.coefficient ctx b j.val else 0) := by
    unfold interpret
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_coefficient ctx a b k.val k.isLt,convolution_finite,basis_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact basis_sum _ _ _ _
  rw [hinit,Finset.sum_comm]
  calc
    _ = ∑i : Fin ctx.rank,∑j : Fin ctx.rank,∑k : Fin ctx.rank,basis ctx k.val
        (if SemiprimeD1JetRouting.admissible ctx.axes i.val j.val ∧
          SemiprimeD1JetRouting.sumIndex ctx.axes i.val j.val=k.val then
          SemiprimeD1JetRingBits.coefficient ctx a i.val*SemiprimeD1JetRingBits.coefficient ctx b j.val else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑i : Fin ctx.rank,∑j : Fin ctx.rank,
        basis ctx i.val (SemiprimeD1JetRingBits.coefficient ctx a i.val)*
          basis ctx j.val (SemiprimeD1JetRingBits.coefficient ctx b j.val) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact routed_basis_sum ctx hpos i j _ _
    _ = interpret ctx a*interpret ctx b := by
      rw [interpret,interpret,Finset.sum_mul_sum]

end
end RiemannGaussian.SemiprimeD1JetOperations
