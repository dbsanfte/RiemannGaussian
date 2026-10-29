/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetOperations

/-! # Actual same-precision outer-axis word embedding
All old coordinates survive. No upward-precision ring homomorphism is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace RiemannGaussian.SemiprimeD1JetEmbedding
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetBoxIndex SemiprimeD1JetInterpretation
noncomputable section

/-- Positive outer radices split the actual dense extent. -/
theorem rank_split (q n : ℕ) (hq : 0<q) : q*n=n+n*(q-1) := by
  have h := Nat.sub_add_cancel hq
  nlinarith


/-- The runtime axis-list dimensions agree with the quotient's fresh-axis dimensions. -/
theorem dims_cons (q : ℕ) (axes : List ℕ) :
    dims (q::axes)=SemiprimeD1JetAlgebra.outerDims q (dims axes) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;> rfl

/-- Every old dense index has zero fresh exponent and all original exponents. -/
theorem exponent_shift (q : ℕ) (axes : List ℕ) (i : ℕ) (hi : i<axes.prod) :
    exponent (q::axes) i=Finsupp.embDomain (SemiprimeD1JetAlgebra.axisShift axes.length)
      (exponent axes i) := by
  ext j
  refine Fin.cases ?_ (fun k=>?_) j
  · have hz : (Finsupp.embDomain (SemiprimeD1JetAlgebra.axisShift axes.length)
        (exponent axes i)) 0=0 := by
      apply Finsupp.embDomain_of_notMem_range
      rintro ⟨k,hk⟩
      exact Fin.succ_ne_zero k hk
    simp only [exponent_apply,digitFn,Fin.cases_zero,Nat.div_eq_of_lt hi,hz]
  · change digitFn axes (i%axes.prod) k=
      (Finsupp.embDomain (SemiprimeD1JetAlgebra.axisShift axes.length) (exponent axes i))
        ((SemiprimeD1JetAlgebra.axisShift axes.length) k)
    rw [Finsupp.embDomain_apply_self,Nat.mod_eq_of_lt hi]
    rfl

/-- Literal finite-series representative of the acquired dense words. -/
def series (ctx : Context) (ws : List (List Bool)) :
    MvPowerSeries (Fin ctx.axes.length) (ZMod (2^ctx.precision)) :=
  ∑i : Fin ctx.rank,MvPowerSeries.monomial (exponent ctx.axes i)
    (SemiprimeD1JetRingBits.coefficient ctx ws i.val)

/-- Actual interpretation projects its literal finite acquired series. -/
theorem interpret_series (ctx : Context) (ws : List (List Bool)) :
    interpret ctx ws=SemiprimeD1JetAlgebra.project (dims ctx.axes) (series ctx ws) := by
  simp only [interpret,series,map_sum,basis]

/-- Actual appended zero words extend the finite series by variable renaming only. -/
theorem series_zero_extend (ctx : Context) (ws : List (List Bool)) (q : ℕ) (hq : 0<q)
    (hshape : ws.length=ctx.rank) :
    series ⟨q::ctx.axes,ctx.precision⟩ (ws++List.replicate (ctx.rank*(q-1)) [])=
      MvPowerSeries.rename (SemiprimeD1JetAlgebra.axisShift ctx.axes.length)
        (series ctx ws) := by
  classical
  change (∑i : Fin (q*ctx.rank),
      MvPowerSeries.monomial (exponent (q::ctx.axes) i.val)
        (SemiprimeD1JetRingBits.coefficient ⟨q::ctx.axes,ctx.precision⟩
          (ws++List.replicate (ctx.rank*(q-1)) []) i.val))=_
  rw [Fin.sum_univ_eq_sum_range (fun i=>
    MvPowerSeries.monomial (exponent (q::ctx.axes) i)
      (SemiprimeD1JetRingBits.coefficient ⟨q::ctx.axes,ctx.precision⟩
        (ws++List.replicate (ctx.rank*(q-1)) []) i)) (q*ctx.rank)]
  have hsplit : q*ctx.rank=ctx.rank+ctx.rank*(q-1) := by
    exact rank_split q ctx.rank hq
  rw [hsplit,Finset.sum_range_add]
  have hz : (∑x∈Finset.range (ctx.rank*(q-1)),
      MvPowerSeries.monomial (exponent (q::ctx.axes) (ctx.rank+x))
        (SemiprimeD1JetRingBits.coefficient ⟨q::ctx.axes,ctx.precision⟩
          (ws++List.replicate (ctx.rank*(q-1)) [])
          (ctx.rank+x)))=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [SemiprimeD1JetRingBits.coefficient,List.getElem?_append,hshape]
    simp [SemiprimeBitArithmetic.bitValue]
  rw [hz,add_zero]
  simp only [series,map_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i=>
    MvPowerSeries.rename (SemiprimeD1JetAlgebra.axisShift ctx.axes.length)
      (MvPowerSeries.monomial (exponent ctx.axes i)
        (SemiprimeD1JetRingBits.coefficient ctx ws i))) ctx.rank]
  apply Finset.sum_congr rfl
  intro i hi
  have hir : i<ctx.rank := Finset.mem_range.mp hi
  rw [MvPowerSeries.rename_monomial]
  have he : Finsupp.mapDomain (SemiprimeD1JetAlgebra.axisShift ctx.axes.length)
      (exponent ctx.axes i)=
      Finsupp.embDomain (SemiprimeD1JetAlgebra.axisShift ctx.axes.length)
        (exponent ctx.axes i) := (Finsupp.embDomain_eq_mapDomain _ _).symm
  rw [he,←exponent_shift q ctx.axes i hir]
  congr 1
  simp only [SemiprimeD1JetRingBits.coefficient]
  rw [List.getElem?_append_left (by omega : i<ws.length)]

/-- Equal dimension functions induce the identical quotient projection. -/
theorem project_heq {σ R : Type*} [CommRing R] (a b : σ→ℕ) (h : a=b)
    (f : MvPowerSeries σ R) :
    HEq (SemiprimeD1JetAlgebra.project a f) (SemiprimeD1JetAlgebra.project b f) := by
  cases h
  rfl

/-- The concrete actual vector embedding is the SAME-precision quotient ring map.
HEq records only the propositionally equal list/finite-function dimension types. -/
theorem embed_interpret (entry : Tagged) (q : ℕ) (hq : 0<q)
    (hshape : entry.coefficients.length=entry.current.rank) :
    HEq (interpret (embed entry [q] entry.current.precision).value.current
      (embed entry [q] entry.current.precision).value.coefficients)
      (SemiprimeD1JetAlgebra.outerEmbedding q (dims entry.current.axes)
        (interpret entry.current entry.coefficients)) := by
  have hc : (embed entry [q] entry.current.precision).value.current=
      ⟨q::entry.current.axes,entry.current.precision⟩ := rfl
  rw [hc,embed_coefficients]
  simp only [List.prod_cons,List.prod_nil,Nat.mul_one]
  rw [interpret_series,series_zero_extend entry.current entry.coefficients q hq hshape,
    interpret_series,SemiprimeD1JetAlgebra.outerEmbedding_project]
  change HEq (SemiprimeD1JetAlgebra.project (dims (q::entry.current.axes)) _)
    (SemiprimeD1JetAlgebra.project
      (SemiprimeD1JetAlgebra.outerDims q (dims entry.current.axes)) _)
  exact project_heq _ _ (dims_cons q entry.current.axes) _

end
end RiemannGaussian.SemiprimeD1JetEmbedding
