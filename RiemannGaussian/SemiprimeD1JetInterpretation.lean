/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetBoxIndex
import RiemannGaussian.SemiprimeD1JetRingBits
import RiemannGaussian.SemiprimeSourceCompactWordIds

/-! # Actual acquired coefficient vectors in the concrete multijet quotient
Interpretation is proof-side only. The executed backend reads/operates on words.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetInterpretation
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetBoxIndex
open SemiprimeBitArithmetic
noncomputable section

/-- Concrete modular quotient associated with the actual runtime context. -/
abbrev Carrier (ctx : Context) :=
  SemiprimeD1JetAlgebra.Algebra (dims ctx.axes) (ZMod (2^ctx.precision))

/-- Below-box coefficients preserve the concrete quotient's actual addition. -/
theorem quotient_coefficient_add {σ R : Type*} [CommRing R] (dim : σ→ℕ)
    (e : σ→₀ℕ) (he : SemiprimeD1JetAlgebra.InBox dim e)
    (f g : SemiprimeD1JetAlgebra.Algebra dim R) :
    SemiprimeD1JetAlgebra.coefficient dim e he (f+g)=
      SemiprimeD1JetAlgebra.coefficient dim e he f+SemiprimeD1JetAlgebra.coefficient dim e he g := by
  induction f using Quotient.inductionOn with
  | h f =>
    induction g using Quotient.inductionOn with
    | h g =>
      change SemiprimeD1JetAlgebra.coefficient dim e he
        (SemiprimeD1JetAlgebra.project dim f+SemiprimeD1JetAlgebra.project dim g)=_
      rw [←map_add,SemiprimeD1JetAlgebra.coefficient_project]
      rfl

/-- Actual quotient zero has all bounded coefficients zero. -/
theorem quotient_coefficient_zero {σ R : Type*} [CommRing R] (dim : σ→ℕ)
    (e : σ→₀ℕ) (he : SemiprimeD1JetAlgebra.InBox dim e) :
    SemiprimeD1JetAlgebra.coefficient dim e he (0:SemiprimeD1JetAlgebra.Algebra dim R)=0 := by
  change MvPowerSeries.coeff e (0:MvPowerSeries σ R)=0
  simp

/-- Finite acquired sums retain their literal below-box coefficient sums. -/
theorem quotient_coefficient_sum {σ R I : Type*} [CommRing R] (dim : σ→ℕ)
    (e : σ→₀ℕ) (he : SemiprimeD1JetAlgebra.InBox dim e) (is : Finset I)
    (f : I→SemiprimeD1JetAlgebra.Algebra dim R) :
    SemiprimeD1JetAlgebra.coefficient dim e he (∑i∈is,f i)=
      ∑i∈is,SemiprimeD1JetAlgebra.coefficient dim e he (f i) := by
  classical
  induction is using Finset.induction_on with
  | empty => simp [quotient_coefficient_zero]
  | @insert i is hi ih => simp only [Finset.sum_insert hi,quotient_coefficient_add,ih]

/-- Quotient image of one original dense-index monomial. -/
def basis (ctx : Context) (i : ℕ) (c : ZMod (2^ctx.precision)) : Carrier ctx :=
  SemiprimeD1JetAlgebra.project (dims ctx.axes) (MvPowerSeries.monomial (exponent ctx.axes i) c)

/-- Actual acquired word vector interpreted by its finite original coordinate list. -/
def interpret (ctx : Context) (ws : List (List Bool)) : Carrier ctx :=
  ∑i : Fin ctx.rank,basis ctx i.val (SemiprimeD1JetRingBits.coefficient ctx ws i.val)

/-- Native exponent encoding is injective throughout the actual dense index range. -/
theorem exponent_injective (axes : List ℕ) (hpos : ∀q∈axes,0<q)
    (i j : ℕ) (hi : i<axes.prod) (hj : j<axes.prod) (he : exponent axes i=exponent axes j) : i=j := by
  have hsub : boxEquiv axes hpos ⟨i,hi⟩=boxEquiv axes hpos ⟨j,hj⟩ := Subtype.ext he
  exact congrArg Fin.val ((boxEquiv axes hpos).injective hsub)

/-- The concrete quotient's canonical coefficient is EXACTLY the actual word read. -/
theorem coefficient_interpret (ctx : Context) (ws : List (List Bool))
    (hpos : ∀q∈ctx.axes,0<q) (i : ℕ) (hi : i<ctx.rank) :
    SemiprimeD1JetAlgebra.coefficient (dims ctx.axes) (exponent ctx.axes i)
      (exponent_inBox ctx.axes i hpos hi) (interpret ctx ws)=
      SemiprimeD1JetRingBits.coefficient ctx ws i := by
  classical
  rw [interpret,quotient_coefficient_sum]
  let index : Fin ctx.rank:=⟨i,hi⟩
  rw [Finset.sum_eq_single index]
  · simp only [basis,SemiprimeD1JetAlgebra.coefficient_project,MvPowerSeries.coeff_monomial,
      ite_true,index]
  · intro j _ hj
    have hn : exponent ctx.axes i≠exponent ctx.axes j.val := by
      intro he
      have hij:=exponent_injective ctx.axes hpos i j.val hi j.isLt he
      exact hj (Fin.ext hij.symm)
    simp only [basis,SemiprimeD1JetAlgebra.coefficient_project,MvPowerSeries.coeff_monomial,hn,ite_false]
  · intro hn
    exact False.elim (hn (Finset.mem_univ index))

/-- Concrete quotient equality is exactly equality of the actual residue coefficients. -/
theorem interpret_eq_iff (ctx : Context) (a b : List (List Bool)) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx a=interpret ctx b ↔
      ∀i,i<ctx.rank→SemiprimeD1JetRingBits.coefficient ctx a i=SemiprimeD1JetRingBits.coefficient ctx b i := by
  constructor
  · intro h i hi
    have he:=congrArg (SemiprimeD1JetAlgebra.coefficient (dims ctx.axes) (exponent ctx.axes i)
      (exponent_inBox ctx.axes i hpos hi)) h
    rw [coefficient_interpret ctx a hpos i hi,coefficient_interpret ctx b hpos i hi] at he
    exact he
  · intro h
    apply SemiprimeD1JetAlgebra.ext (dims ctx.axes)
    intro e he
    let i := (boxEquiv ctx.axes hpos).symm ⟨e,he⟩
    have hindex : exponent ctx.axes i.val=e :=
      congrArg Subtype.val ((boxEquiv ctx.axes hpos).apply_symm_apply ⟨e,he⟩)
    have hc:=h i.val i.isLt
    have ha:=coefficient_interpret ctx a hpos i.val i.isLt
    have hb:=coefficient_interpret ctx b hpos i.val i.isLt
    have ha' : SemiprimeD1JetAlgebra.coefficient (dims ctx.axes) e he (interpret ctx a)=
        SemiprimeD1JetRingBits.coefficient ctx a i.val := by simpa only [hindex] using ha
    have hb' : SemiprimeD1JetAlgebra.coefficient (dims ctx.axes) e he (interpret ctx b)=
        SemiprimeD1JetRingBits.coefficient ctx b i.val := by simpa only [hindex] using hb
    exact ha'.trans (hc.trans hb'.symm)

/-- Canonical bounded acquired words are faithfully represented by the concrete quotient. -/
theorem interpret_injective (ctx : Context) (a b : List (List Bool))
    (hpos : ∀q∈ctx.axes,0<q) (ha : a.length=ctx.rank) (hb : b.length=ctx.rank)
    (hca : ∀w∈a,SemiprimeSourceCompactBits.Compact w)
    (hcb : ∀w∈b,SemiprimeSourceCompactBits.Compact w)
    (hwa : ∀w∈a,w.length≤ctx.precision) (hwb : ∀w∈b,w.length≤ctx.precision)
    (he : interpret ctx a=interpret ctx b) : a=b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro i hi hj
  have hir : i<ctx.rank := by omega
  have hc := (interpret_eq_iff ctx a b hpos).mp he i hir
  simp only [SemiprimeD1JetRingBits.coefficient,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.getD_some] at hc
  have hma := hwa a[i] (List.getElem_mem hi)
  have hmb := hwb b[i] (List.getElem_mem hj)
  have hva : bitValue a[i]<2^ctx.precision :=
    (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) hma)
  have hvb : bitValue b[i]<2^ctx.precision :=
    (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) hmb)
  have hv := congrArg ZMod.val hc
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hva,Nat.mod_eq_of_lt hvb] at hv
  exact SemiprimeSourceCompactWordIds.compact_value_injective _ _
    (hca _ (List.getElem_mem hi)) (hcb _ (List.getElem_mem hj)) hv

end
end RiemannGaussian.SemiprimeD1JetInterpretation
