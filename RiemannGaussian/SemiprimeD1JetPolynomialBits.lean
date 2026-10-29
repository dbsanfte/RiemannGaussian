/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetAffineCoefficient
import RiemannGaussian.SemiprimeEncodedRowSelection

/-! # Concrete acquired scalar vectors and finite physical jet polynomial loops
Signed source acquisition and inverse acquisition are attached separately. All
arithmetic here is the existing concrete jet backend, not generic ring advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1JetPolynomialBits
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Actual p-stage source digit acquisition gives exactly the residue, without a fit premise. -/
theorem digits_mod (p n : ℕ) :
    bitValue (SemiprimeEncodedRowSelection.digits p n).bits=n%2^p := by
  induction p generalizing n with
  | zero => simp only [SemiprimeEncodedRowSelection.digits,bitValue,Nat.pow_zero,Nat.mod_one]
  | succ p ih =>
    have hsplit:=Nat.mod_add_div (n%(2*2^p)) 2
    have hrem:=Nat.mod_mul_right_mod n 2 (2^p)
    have hdiv:=Nat.mod_mul_right_div_self n 2 (2^p)
    simp only [SemiprimeEncodedRowSelection.digits,bitValue,
      SemiprimeEncodedRowSelection.remainder_bit,ih]
    rw [pow_succ']
    omega

/-- Source integer magnitudes are read in exactly p actual div/rem stages. -/
def magnitude (p n : ℕ) : SemiprimeSourceCompactBits.Report :=
  let ds:=SemiprimeEncodedRowSelection.digits p n
  let out:=SemiprimeSourceCompactBits.trim ds.bits
  ⟨out.bits,ds.work+out.clock+3⟩

/-- Source magnitude acquisition is the correct modular scalar, without a requested word. -/
theorem magnitude_value (p n : ℕ) :
    (bitValue (magnitude p n).bits:ZMod (2^p))=(n:ZMod (2^p)) := by
  simp only [magnitude,SemiprimeSourceCompactBits.trim_value,digits_mod,ZMod.natCast_mod]

/-- Allocate a copied scalar as the constant coordinate, all other coordinates zero. -/
def scalar (ctx : Context) (bits : List Bool) : JetRun :=
  let cache:=SemiprimeSourceCompactBits.copy bits
  ⟨(List.range ctx.rank).map (fun i=>if i=0 then cache.bits else []),
    cache.clock+3*ctx.rank+3⟩

/-- The actual dense scalar acquisition is the concrete quotient's constant map. -/
theorem scalar_value (ctx : Context) (bits : List Bool) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (scalar ctx bits).words=
      SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
        (bitValue bits:ZMod (2^ctx.precision)) := by
  classical
  have hn : 0<ctx.rank := List.prod_pos hpos
  let z : Fin ctx.rank:=⟨0,hn⟩
  unfold interpret
  rw [Finset.sum_eq_single z]
  · simp only [scalar,SemiprimeD1JetRingBits.coefficient,List.getElem?_map,
      List.getElem?_range z.isLt,Option.map_some,Option.getD_some,z,ite_true,
      SemiprimeSourceCompactBits.copy_bits,basis,SemiprimeD1JetAffineCoefficient.exponent_zero,
      MvPowerSeries.monomial_zero_eq_C_apply,SemiprimeD1JetAlgebra.constants,RingHom.comp_apply]
  · intro i _ hiz
    have hi : i.val≠0 := fun h=>hiz (Fin.ext h)
    simp [scalar,SemiprimeD1JetRingBits.coefficient,hi,basis,bitValue]
  · intro h
    exact False.elim (h (Finset.mem_univ z))

/-- Acquire a physical finite power, retaining every previous report once. -/
def power (ctx : Context) (z : List (List Bool)) : ℕ→JetRun
  | 0 => SemiprimeD1JetAffineCoefficient.one ctx
  | n+1 =>
    let old:=power ctx z n
    let out:=SemiprimeD1JetRingBits.mul ctx z old.words
    ⟨out.words,old.clock+out.clock+3⟩

/-- The actual finite power is the original concrete ring power. -/
theorem power_value (ctx : Context) (z : List (List Bool)) (n : ℕ)
    (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (power ctx z n).words=(interpret ctx z)^n := by
  induction n with
  | zero => simpa only [power,pow_zero] using SemiprimeD1JetAffineCoefficient.interpret_one ctx hpos
  | succ n ih =>
    change interpret ctx (SemiprimeD1JetRingBits.mul ctx z (power ctx z n).words).words=_
    rw [SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,ih,pow_succ']

/-- Actual ordered acquired vector product, with every child report retained. -/
def product (ctx : Context) : List JetRun→JetRun
  | [] => SemiprimeD1JetAffineCoefficient.one ctx
  | x::xs =>
    let tail:=product ctx xs
    let out:=SemiprimeD1JetRingBits.mul ctx x.words tail.words
    ⟨out.words,x.clock+tail.clock+out.clock+3⟩

/-- The concrete acquired product has the literal ordered finite interpretation. -/
theorem product_value (ctx : Context) (xs : List JetRun) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (product ctx xs).words=(xs.map (fun x=>interpret ctx x.words)).prod := by
  induction xs with
  | nil => exact SemiprimeD1JetAffineCoefficient.interpret_one ctx hpos
  | cons x xs ih =>
    change interpret ctx (SemiprimeD1JetRingBits.mul ctx x.words (product ctx xs).words).words=_
    rw [SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,ih]
    rfl

/-- Horner evaluation of actual ascending acquired scalar coefficients. -/
def horner (ctx : Context) (z : List (List Bool)) : List (List Bool)→JetRun
  | [] => SemiprimeD1JetAffineCoefficient.zero ctx
  | c::cs =>
    let tail:=horner ctx z cs
    let constant:=scalar ctx c
    let term:=SemiprimeD1JetRingBits.mul ctx z tail.words
    let out:=SemiprimeD1JetRingBits.add ctx constant.words term.words
    ⟨out.words,tail.clock+constant.clock+term.clock+out.clock+5⟩

/-- Concrete Horner execution interprets the literal acquired coefficient list. -/
theorem horner_value (ctx : Context) (z : List (List Bool)) (cs : List (List Bool))
    (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (horner ctx z cs).words=
      cs.foldr (fun c tail=>SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
        (bitValue c:ZMod (2^ctx.precision))+interpret ctx z*tail) 0 := by
  induction cs with
  | nil => exact SemiprimeD1JetAffineCoefficient.interpret_zero ctx
  | cons c cs ih =>
    change interpret ctx (SemiprimeD1JetRingBits.add ctx (scalar ctx c).words
      (SemiprimeD1JetRingBits.mul ctx z (horner ctx z cs).words).words).words=_
    rw [SemiprimeD1JetOperations.interpret_add ctx _ _ hpos,
      SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,scalar_value ctx c hpos,ih]
    rfl

/-- Finite ascending Horner arithmetic is the literal coefficient-power sum. -/
theorem foldr_sum {A : Type*} [CommRing A] (cs : List A) (z : A) :
    cs.foldr (fun c tail=>c+z*tail) 0=
      ∑r∈Finset.range cs.length,cs.getD r 0*z^r := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldr_cons,List.length_cons,Finset.sum_range_succ',
      List.getD_cons_succ,List.getD_cons_zero,pow_zero,mul_one,ih]
    rw [Finset.mul_sum]
    have he : (∑r∈Finset.range cs.length,z*(cs.getD r 0*z^r))=
        ∑r∈Finset.range cs.length,cs.getD r 0*z^(r+1) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_succ]
      ring
    rw [he,add_comm]

/-- Actual Horner output is the explicit finite acquired coefficient-power sum. -/
theorem horner_sum (ctx : Context) (z : List (List Bool)) (cs : List (List Bool))
    (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (horner ctx z cs).words=
      ∑r∈Finset.range cs.length,
        SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
          (bitValue (cs.getD r []):ZMod (2^ctx.precision))*(interpret ctx z)^r := by
  rw [horner_value ctx z cs hpos]
  have hfold := foldr_sum
    (cs.map (fun c=>SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
      (bitValue c:ZMod (2^ctx.precision)))) (interpret ctx z)
  rw [List.foldr_map] at hfold
  rw [hfold]
  simp only [List.length_map]
  apply Finset.sum_congr rfl
  intro r hr
  have hir : r<cs.length := Finset.mem_range.mp hr
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem hir,Option.map_some,Option.getD_some]

end RiemannGaussian.SemiprimeD1JetPolynomialBits
