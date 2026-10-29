/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroGraphExtension
import RiemannGaussian.SemiprimeMacroParameters

/-!
# Actual public macro graph counts ordinary integer factor pairs

All schedule, target reconstruction and active source width obligations are
discharged from the public integer. No factor-coverage or graph-correctness
premise is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace RiemannGaussian.SemiprimePublicFactorCount
open scoped BigOperators
open SemiprimeMacroFermatNetwork SemiprimeBooleanNetwork SemiprimeMacroBitNetwork
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroGraphExtension
open SemiprimeMacroParameters
attribute [local instance] Classical.propDecidable

/-- Literal compiler numerical configuration for the public positive integer. -/
def publicConfig (N : ℕ) (hN : 0<N) : Config where
  depth := macroDepth (bitLength N)
  r := firstAxis (bitLength N)
  t := secondAxis (bitLength N)
  digits := digitCount (bitLength N)
  bits := radixBits (bitLength N)
  shape := (axes_product _).trans (transform_eq_macroLength (bitLength_pos hN))
  quarter := (axes_product _).trans (transform_eq_four_radixBits (bitLength_pos hN))
  bits_pos := radixBits_pos (bitLength_pos hN)
  digits_pos := (digitCount_bounds (bitLength_pos hN)).1
  digits_le := (digitCount_bounds (bitLength_pos hN)).2
  width i := activeDigitBits (bitLength N) i.val
  width_le i := (activeDigitBits_bounds (bitLength_pos hN) i.isLt).2
  target := targetDigit (bitLength N) N
  target_lt i hi := Nat.mod_lt _ (by positivity)
  normalizer := Classical.choose (length_normalizer_exists (macroDepth (bitLength N)))
  normalizer_spec := Classical.choose_spec (length_normalizer_exists (macroDepth (bitLength N)))

/-- The public target words reconstruct exactly the supplied integer. -/
theorem public_target_value (N : ℕ) (hN : 0<N) : targetValue (publicConfig N hN)=N := by
  change (∑ i∈Finset.range (firstAxis (bitLength N)*secondAxis (bitLength N)),
    targetDigit (bitLength N) N i*(2^radixBits (bitLength N))^i)=N
  rw [axes_product]
  exact public_targetDigit_sum_transform hN

/-- Encode the actual radix digits of an ordinary candidate integer. -/
def publicInput (N : ℕ) (hN : 0<N) (x : ℕ) :
    Fin (publicConfig N hN).digits→BitVec (publicConfig N hN).bits :=
  fun i => encode (radixBits (bitLength N)) (targetDigit (bitLength N) x i.val)

/-- Candidate digit encoding is exact, with no unknown root/field operation. -/
theorem publicInput_value (N : ℕ) (hN : 0<N) (x : ℕ) (i : Fin (publicConfig N hN).digits) :
    decode (publicInput N hN x i)=targetDigit (bitLength N) x i.val :=
  decode_encode (Nat.mod_lt _ (by positivity))

/-- Every ordinary candidate at most N obeys the literal active top-bit limits. -/
theorem publicInput_width (N : ℕ) (hN : 0<N) (x : ℕ) (hx : x≤N)
    (i : Fin (publicConfig N hN).digits) :
    decode (publicInput N hN x i)<2^((publicConfig N hN).width i) := by
  rw [publicInput_value]
  exact public_factor_digit_bound hN hx i.isLt

/-- Actual source digits reconstruct every candidate at most N exactly. -/
theorem publicInput_operand (N : ℕ) (hN : 0<N) (x : ℕ) (hx : x≤N) :
    operand (publicInput N hN x)=x := by
  unfold operand
  calc
    _ = ∑ i∈Finset.range (digitCount (bitLength N)),targetDigit (bitLength N) x i*
        (2^radixBits (bitLength N))^i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hd := Finset.mem_range.mp hi
      have he : values (publicInput N hN x) i=targetDigit (bitLength N) x i :=
        (values_at (publicInput N hN x) ⟨i,hd⟩).trans (publicInput_value N hN x ⟨i,hd⟩)
      rw [he]
      rfl
    _ = x := targetDigit_sum (bitLength_pos hN) (hx.trans_lt (input_lt_bitLength_power N))

/-- Ordinary ordered nontrivial integer factor pairs; the finite bound N is
automatic for such factors and does not discard an orientation or a square. -/
abbrev OrdinaryFactors (N : ℕ) :=
  {pair : Fin (N+1)×Fin (N+1) // 2≤pair.1.val ∧ 2≤pair.2.val ∧ pair.1.val*pair.2.val=N}

/-- Project actual admissible source data onto their true ordinary factors. -/
def ordinaryProjection (N : ℕ) (hN : 0<N) (input : AdmissibleInputs (publicConfig N hN)) : OrdinaryFactors N := by
  have hprod : operand (input.val 0)*operand (input.val 1)=N :=
    input.property.2.2.trans (public_target_value N hN)
  have hleft : operand (input.val 0)≤N := by
    have hq := input.property.2.1 1
    have hm := Nat.mul_le_mul_left (operand (input.val 0)) (show 1≤operand (input.val 1) by omega)
    simpa only [Nat.mul_one,hprod] using hm
  have hright : operand (input.val 1)≤N := by
    have hp := input.property.2.1 0
    have hm := Nat.mul_le_mul_right (operand (input.val 1)) (show 1≤operand (input.val 0) by omega)
    simpa only [Nat.one_mul,hprod] using hm
  exact ⟨(⟨operand (input.val 0),by omega⟩,⟨operand (input.val 1),by omega⟩),
    input.property.2.1 0,input.property.2.1 1,hprod⟩

/-- No two source digit arrays represent the same ordinary factor pair. -/
theorem ordinaryProjection_injective (N : ℕ) (hN : 0<N) :
    Function.Injective (ordinaryProjection N hN) := by
  intro a b h
  apply Subtype.ext
  funext side
  fin_cases side
  · apply operand_injective
    exact congrArg (fun pair : Fin (N+1)×Fin (N+1) => pair.1.val) (congrArg Subtype.val h)
  · apply operand_injective
    exact congrArg (fun pair : Fin (N+1)×Fin (N+1) => pair.2.val) (congrArg Subtype.val h)

/-- Every ordinary nontrivial factor pair is covered by the actual public
source widths, with no width-coverage promise. -/
theorem ordinaryProjection_surjective (N : ℕ) (hN : 0<N) :
    Function.Surjective (ordinaryProjection N hN) := by
  intro pair
  let input : Inputs (publicConfig N hN) :=
    fun side => if side.val=0 then publicInput N hN pair.val.1.val else publicInput N hN pair.val.2.val
  have hp : pair.val.1.val≤N := by have := pair.val.1.isLt;omega
  have hq : pair.val.2.val≤N := by have := pair.val.2.isLt;omega
  have hzero : operand (input 0)=pair.val.1.val := publicInput_operand N hN _ hp
  have hone : operand (input 1)=pair.val.2.val := publicInput_operand N hN _ hq
  have hvalid : InputValid (publicConfig N hN) input := by
    refine ⟨?_,?_,?_⟩
    · intro side i
      fin_cases side
      · exact publicInput_width N hN _ hp i
      · exact publicInput_width N hN _ hq i
    · intro side
      fin_cases side
      · change 2≤operand (input (0 : Fin 2))
        rw [hzero];exact pair.property.1
      · change 2≤operand (input (1 : Fin 2))
        rw [hone];exact pair.property.2.1
    · rw [hzero,hone,public_target_value]
      exact pair.property.2.2
  refine ⟨⟨input,hvalid⟩,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact hzero
  · apply Fin.ext
    exact hone

/-- Concrete public source factor inputs are in bijection with ordinary factors. -/
def ordinaryFactorEquiv (N : ℕ) (hN : 0<N) :
    AdmissibleInputs (publicConfig N hN) ≃ OrdinaryFactors N :=
  Equiv.ofBijective (ordinaryProjection N hN)
    ⟨ordinaryProjection_injective N hN,ordinaryProjection_surjective N hN⟩

/-- Actual accepted original public graph assignments count ordinary factors. -/
def publicAcceptedFactorEquiv (N : ℕ) (hN : 0<N) :
    Accepted (publicConfig N hN) ≃ OrdinaryFactors N :=
  (acceptedInputEquiv (publicConfig N hN)).trans (ordinaryFactorEquiv N hN)

/-- The whole literal public ordered tensor graph counts ordinary nontrivial
integer factor pairs of N, with no global correctness/count/coverage premise. -/
theorem public_tensor_factor_count (N : ℕ) (hN : 0<N) :
    (∑ assignment : Edge (publicConfig N hN).r (publicConfig N hN).t (publicConfig N hN).digits→Bool,
      ∏ v : SubdividedVertex (publicConfig N hN).r (publicConfig N hN).t (publicConfig N hN).digits,
        if subdividedTable (publicConfig N hN) v (fun slot => assignment
          (orderedEdgeAt (publicConfig N hN).digits_pos (publicConfig N hN).cap ⟨v,slot⟩)) then (1 : ℕ) else 0)=
      Fintype.card (OrdinaryFactors N) := by
  rw [actual_tensor_contraction,indicator_card (InputValid (publicConfig N hN))]
  exact Fintype.card_congr (ordinaryFactorEquiv N hN)

end RiemannGaussian.SemiprimePublicFactorCount
