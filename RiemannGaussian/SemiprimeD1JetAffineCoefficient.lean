/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetEmbedding
import RiemannGaussian.SemiprimeD1AffineCoefficientBounds

/-! # Physical acquired single coefficient over the actual modular jet algebra
Only concrete word vectors and the original finite tuple execute. Semantic
polynomials and the quotient interpretation occur in proofs only.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1JetAffineCoefficient
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetBoxIndex SemiprimeD1JetInterpretation
open SemiprimeBitArithmetic
/-- Concrete physical vector report. -/
abbrev JetRun := SemiprimeD1JetRingBits.Run

/-- Actual affine row data, without polynomial or semantic ring fields. -/
structure Row where
  /-- Actual constant-coefficient words. -/
  base : List (List Bool)
  /-- Actual mode coefficient word vectors in literal order. -/
  coefficients : List (List (List Bool))

/-- Allocate every zero coefficient cell. -/
def zero (ctx : Context) : JetRun := ⟨List.replicate ctx.rank [],ctx.rank+1⟩

/-- Acquire scalar one modulo the original precision once, then allocate dense cells. -/
def one (ctx : Context) : JetRun :=
  let scalar:=SemiprimeD1JetScalarBits.reduce ctx.precision [true]
  ⟨(List.range ctx.rank).map (fun i=>if i=0 then scalar.bits else []),
    scalar.clock+3*ctx.rank+3⟩

/-- Cache each acquired branch, adding actual vectors and retaining all reports. -/
def sumRuns (ctx : Context) : List JetRun→JetRun
  | [] => zero ctx
  | r::rs =>
    let tail:=sumRuns ctx rs
    let out:=SemiprimeD1JetRingBits.add ctx r.words tail.words
    ⟨out.words,r.clock+tail.clock+out.clock+3⟩

/-- Actual requested-coefficient recursion, with concrete physical jet operations. -/
def evaluate (ctx : Context) (K : ℕ) : List Row→List ℕ→JetRun
  | [],beta =>
    let test:=SemiprimeD1AffineCoefficient.zeroTest beta
    let out:=if test.1 then one ctx else zero ctx
    ⟨out.words,test.2+out.clock+3⟩
  | row::rows,beta =>
    let zeros:=zero ctx
    let base:=evaluate ctx K rows beta
    let branches:=(List.range K).map (fun i=>
      let exponent:=SemiprimeD1AffineCoefficient.read 0 beta i
      if exponent.1=0 then ⟨zeros.words,exponent.2+3⟩
      else
        let target:=SemiprimeD1AffineCoefficient.decrement beta i
        let child:=evaluate ctx K rows target.1
        let coeff:=SemiprimeD1AffineCoefficient.read zeros.words row.coefficients i
        let out:=SemiprimeD1JetRingBits.mul ctx coeff.1 child.words
        ⟨out.words,exponent.2+target.2+child.clock+coeff.2+out.clock+5⟩)
    let total:=sumRuns ctx branches
    let product:=SemiprimeD1JetRingBits.mul ctx row.base base.words
    let out:=SemiprimeD1JetRingBits.add ctx product.words total.words
    ⟨out.words,zeros.clock+base.clock+total.clock+product.clock+out.clock+10*K+8⟩

noncomputable section
/-- Mathematical row interpretation, never called by the runtime. -/
def rowValue (ctx : Context) (row : Row) : SemiprimeD1AffineCoefficient.Row (Carrier ctx) :=
  ⟨interpret ctx row.base,row.coefficients.map (interpret ctx)⟩

/-- Every zero word coefficient has zero modular interpretation. -/
theorem interpret_zero (ctx : Context) : interpret ctx (zero ctx).words=0 := by
  classical
  unfold interpret
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val<ctx.rank := i.isLt
  simp [zero,SemiprimeD1JetRingBits.coefficient,hi,
    basis,SemiprimeBitArithmetic.bitValue]

/-- Dense index zero is the constant monomial in every actual axis list. -/
theorem exponent_zero (axes : List ℕ) : exponent axes 0=0 := by
  apply Finsupp.ext
  intro j
  simp only [exponent_apply,Finsupp.zero_apply]
  induction axes with
  | nil => exact Fin.elim0 j
  | cons q qs ih =>
    refine Fin.cases ?_ (fun k=>?_) j
    · simp [digitFn]
    · simpa only [digitFn,Fin.cases_succ,Nat.zero_mod] using ih k

/-- The acquired scalar-one word has exactly residue one, even at precision zero. -/
theorem one_scalar (ctx : Context) :
    (bitValue (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).bits:
      ZMod (2^ctx.precision))=1 := by
  rw [SemiprimeD1JetScalarBits.reduce_value,ZMod.natCast_mod]
  simp [bitValue,bitNat]

/-- The actual dense scalar-one allocation represents the quotient unit. -/
theorem interpret_one (ctx : Context) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (one ctx).words=1 := by
  classical
  have hn : 0<ctx.rank := List.prod_pos hpos
  let z : Fin ctx.rank:=⟨0,hn⟩
  unfold interpret
  rw [Finset.sum_eq_single z]
  · simp only [one,SemiprimeD1JetRingBits.coefficient,List.getElem?_map,
      List.getElem?_range z.isLt,Option.map_some,Option.getD_some,z,ite_true]
    rw [one_scalar]
    simp only [basis,exponent_zero]
    rw [MvPowerSeries.monomial_zero_one,map_one]
  · intro i _ hiz
    have hi : i.val≠0 := fun h=>hiz (Fin.ext h)
    simp [one,SemiprimeD1JetRingBits.coefficient,hi,basis,bitValue]
  · intro h
    exact False.elim (h (Finset.mem_univ z))

/-- Concrete cached accumulation agrees with the literal sum of acquired values. -/
theorem sumRuns_value (ctx : Context) (rs : List JetRun) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (sumRuns ctx rs).words=(rs.map (fun r=>interpret ctx r.words)).sum := by
  induction rs with
  | nil => exact interpret_zero ctx
  | cons r rs ih =>
    change interpret ctx (SemiprimeD1JetRingBits.add ctx r.words (sumRuns ctx rs).words).words=_
    rw [SemiprimeD1JetOperations.interpret_add ctx _ _ hpos,ih]
    rfl

/-- Cached coefficient reads commute with interpretation, including missing modes. -/
theorem read_interpret (ctx : Context) (ws : List (List (List Bool))) (i : ℕ) :
    interpret ctx (SemiprimeD1AffineCoefficient.read (zero ctx).words ws i).1=
      (SemiprimeD1AffineCoefficient.read 0 (ws.map (interpret ctx)) i).1 := by
  induction ws generalizing i with
  | nil => exact interpret_zero ctx
  | cons w ws ih => cases i <;> simp only [SemiprimeD1AffineCoefficient.read,List.map_cons,ih]

/-- Every actually executed branch equals the generic recurrence in the concrete ring. -/
theorem evaluate_value (ctx : Context) (K : ℕ) (rows : List Row) (beta : List ℕ)
    (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (evaluate ctx K rows beta).words=
      (SemiprimeD1AffineCoefficient.evaluate K (rows.map (rowValue ctx)) beta).value := by
  classical
  induction rows generalizing beta with
  | nil =>
    simp only [evaluate,List.map_nil,SemiprimeD1AffineCoefficient.evaluate]
    split <;> rename_i h
    · exact interpret_one ctx hpos
    · exact interpret_zero ctx
  | cons row rows ih =>
    change interpret ctx (SemiprimeD1JetRingBits.add ctx
      (SemiprimeD1JetRingBits.mul ctx row.base (evaluate ctx K rows beta).words).words
      (sumRuns ctx ((List.range K).map (fun i=>
        let exponent:=SemiprimeD1AffineCoefficient.read 0 beta i
        if exponent.1=0 then ⟨(zero ctx).words,exponent.2+3⟩
        else
          let target:=SemiprimeD1AffineCoefficient.decrement beta i
          let child:=evaluate ctx K rows target.1
          let coeff:=SemiprimeD1AffineCoefficient.read (zero ctx).words row.coefficients i
          let out:=SemiprimeD1JetRingBits.mul ctx coeff.1 child.words
          ⟨out.words,exponent.2+target.2+child.clock+coeff.2+out.clock+5⟩))).words).words=_
    rw [SemiprimeD1JetOperations.interpret_add ctx _ _ hpos,
      SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,ih,sumRuns_value ctx _ hpos]
    simp only [List.map_cons,SemiprimeD1AffineCoefficient.evaluate,
      SemiprimeD1AffineCoefficient.sumRuns_value,List.map_map,Function.comp_def,rowValue]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro i _
    split
    · exact interpret_zero ctx
    · rw [SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,ih,read_interpret]

/-- The physical concrete backend supplies the requested original polynomial coefficient. -/
theorem evaluate_coefficient (ctx : Context) (K : ℕ) (rows : List Row) (beta : List ℕ)
    (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (evaluate ctx K rows beta).words=
      (SemiprimeD1AffineCoefficient.polynomial K (rows.map (rowValue ctx))).coeff beta.toFinsupp := by
  rw [evaluate_value ctx K rows beta hpos,SemiprimeD1AffineCoefficient.evaluate_value]

end
end RiemannGaussian.SemiprimeD1JetAffineCoefficient
