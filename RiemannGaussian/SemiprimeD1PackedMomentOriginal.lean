/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedMomentDigits

/-! # Actual local weighted contraction equals the factor-pair first moment
Every mark is read locally; the explicit accepted-assignment equivalences
preserve the decoded operand. No count, factor sum or satisfying model is
an algorithm input. This finite identity alone asserts no acquisition time.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedMomentOriginal
open scoped BigOperators
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroGraphExtension
open SemiprimeD1PackedMomentAlgebra SemiprimeD1PackedMomentDigits SemiprimePublicFactorCount
attribute [local instance] Classical.propDecidable

/-- Only literal original checker entries of value one are marked. -/
def markedTable {R : Type*} [CommSemiring R] (p : Config) (b : R)
    (v : SubdividedVertex p.r p.t p.digits) (input : Fin (subdividedArity v)→Bool) : R :=
  if subdividedTable p v input then 1+b*(localMark p v input : R) else 0

/-- Full ordered graph contraction, retaining both halves of every original
wire, all equality vertices and every accepted assignment with multiplicity. -/
def contraction {R : Type*} [CommSemiring R] (p : Config) (b : R) : R :=
  ∑a : Edge p.r p.t p.digits→Bool,
    ∏v : SubdividedVertex p.r p.t p.digits,
      markedTable p b v (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩))

/-- Boolean equality constraints give an explicit accepted subdivision
bijection that preserves the complete shared signal assignment. -/
def sharedEquiv (p : Config) :
    {a : Edge p.r p.t p.digits→Bool // SubdividedAccepted p a} ≃ Accepted p where
  toFun a := ⟨fun signal => a.val (signal,false),subdivided_original p a.val a.property⟩
  invFun a := ⟨fun e => a.val e.1,by
    apply (subdivided_tables_iff p _).mpr
    constructor
    · intro signal
      rfl
    · intro v
      exact a.property v⟩
  left_inv a := by
    apply Subtype.ext
    funext e
    rcases e with ⟨signal,side⟩
    cases side
    · rfl
    · exact ((subdivided_tables_iff p a.val).mp a.property).1 signal
  right_inv a := by
    apply Subtype.ext
    rfl

/-- Weighted summation restricts to the accepted subtype without losing
weights; mere equality of cardinalities would not justify this step. -/
theorem accepted_sum {X R : Type*} [Fintype X] [AddCommMonoid R]
    (P : X→Prop) (f : X→R) :
    (∑x,if P x then f x else 0)=∑x : {x // P x},f x.val := by
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro x;simp only [Finset.mem_filter,Finset.mem_univ,true_and]) f

/-- Actual local marked entries have exactly the decoded operand as their
first moment on accepted assignments and zero otherwise. -/
theorem assignment_product {R : Type*} [CommSemiring R] (p : Config) (b : R)
    (hb : b*b=0) (a : Edge p.r p.t p.digits→Bool) :
    (∏v : SubdividedVertex p.r p.t p.digits,
      markedTable p b v (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩)))=
      if SubdividedAccepted p a then
        1+b*(sourceOperand p (fun signal => a (signal,false)) 0 : R) else 0 := by
  have h := checked_product
    (fun v : SubdividedVertex p.r p.t p.digits =>
      subdividedTable p v (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩)))
    b hb (fun v => (localMark p v (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩)) : R))
  unfold markedTable
  rw [h]
  by_cases ha : SubdividedAccepted p a
  · have hlocal : ∀v : SubdividedVertex p.r p.t p.digits,
        subdividedTable p v (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩))=true := ha
    rw [ite_eq_left ha,ite_eq_left hlocal,←Nat.cast_sum,subdivided_operand p a ha]
  · have hlocal : ¬∀v : SubdividedVertex p.r p.t p.digits,
        subdividedTable p v (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩))=true := ha
    rw [ite_eq_right ha,ite_eq_right hlocal]

/-- The exact finite local contraction is the first moment of original
accepted assignments, via the actual equality-constraint bijection. -/
theorem accepted_contraction {R : Type*} [CommSemiring R] (p : Config)
    (b : R) (hb : b*b=0) :
    contraction p b=∑a : Accepted p,(1+b*(sourceOperand p a.val 0 : R)) := by
  unfold contraction
  calc
    _ = ∑a : Edge p.r p.t p.digits→Bool,if SubdividedAccepted p a then
        1+b*(sourceOperand p (fun signal => a (signal,false)) 0 : R) else 0 := by
      exact Finset.sum_congr rfl (fun a _ => assignment_product p b hb a)
    _ = ∑a : {a : Edge p.r p.t p.digits→Bool // SubdividedAccepted p a},
        (1+b*(sourceOperand p (fun signal => a.val (signal,false)) 0 : R)) := accepted_sum _ _
    _ = ∑a : Accepted p,(1+b*(sourceOperand p a.val 0 : R)) := by
      exact ((sharedEquiv p).sum_comp (fun a : Accepted p => 1+b*(sourceOperand p a.val 0 : R)))

/-- The explicit public graph-to-factor bijection preserves the actual first
operand. This strengthens its earlier unweighted cardinality theorem. -/
theorem first_factor (N : ℕ) (hN : 0<N) (a : Accepted (publicConfig N hN)) :
    (publicAcceptedFactorEquiv N hN a).val.1.val=sourceOperand (publicConfig N hN) a.val 0 := by
  change SemiprimeBooleanNetwork.operand (extractedInput (publicConfig N hN) a.val 0)=_
  exact extractedInput_operand _ a.val a.property 0

/-- Exact ordinary first-factor sum, including both orientations when distinct. -/
def factorSum (N : ℕ) : ℕ := ∑f : OrdinaryFactors N,f.val.1.val

/-- FULL public local weighted graph contraction equals the count plus the
marker times the sum of genuine ordinary first factors. All model uniqueness,
coverage, inactive digits and equality constraints are discharged internally. -/
theorem public_contraction {R : Type*} [CommSemiring R] (N : ℕ) (hN : 0<N)
    (b : R) (hb : b*b=0) :
    contraction (publicConfig N hN) b=
      (Fintype.card (OrdinaryFactors N) : R)+b*(factorSum N : R) := by
  rw [accepted_contraction _ b hb]
  calc
    _ = ∑a : Accepted (publicConfig N hN),(1+b*((publicAcceptedFactorEquiv N hN a).val.1.val : R)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [first_factor N hN a]
    _ = ∑f : OrdinaryFactors N,(1+b*(f.val.1.val : R)) :=
      (publicAcceptedFactorEquiv N hN).sum_comp (fun f : OrdinaryFactors N => 1+b*(f.val.1.val : R))
    _ = _ := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Nat.cast_sum]
      simp only [factorSum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

/-- Specializing only the FINAL scalar modulus cancels all higher moments.
Intermediate larger-precision integer computations remain unchanged. -/
theorem public_square_modulus (N : ℕ) (hN : 0<N) (B : ℕ) :
    contraction (publicConfig N hN) (B : ZMod (B^2))=
      ((Fintype.card (OrdinaryFactors N)+B*factorSum N : ℕ) : ZMod (B^2)) := by
  rw [public_contraction N hN _ (base_square_zero B)]
  push_cast
  rfl

end RiemannGaussian.SemiprimeD1PackedMomentOriginal
