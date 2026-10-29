/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapePublicSearch
import RiemannGaussian.SemiprimeD1BinaryFactorExecution
import RiemannGaussian.SemiprimeD1PublicOperandBits
import RiemannGaussian.SemiprimeD1FactorValidationBits

/-! # Closed binary-output semiprime factor execution
All count queries acquire their own original root and execute the physical
recursive counter. Operand construction uses original selected-label scans and
Boolean radix assembly; proper-divisor validation and cofactor recovery use
Boolean comparison and restoring division. The result contains literal factor
bytes. Query, physical arithmetic and native metadata reports remain distinct;
no complete primitive-machine runtime is asserted by this module.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordTapeBinaryFactorExecution
open SemiprimePublicAcquiredExecution SemiprimeBitArithmetic SemiprimeBitDivision
open SemiprimePublicAcquiredExecution SemiprimeBitPrimeScan
attribute [local irreducible] SemiprimeD1WordTapePublicSearch.search
  SemiprimeD1PhysicalPublicCounter.search SemiprimeD1PublicCounter.search
  SemiprimeD1PublicOperandBits.run SemiprimeD1FactorValidationBits.run
  SemiprimePublicAcquiredExecution.decodeOperand

/-- Literal factor bytes and every retained contribution of this executed path. -/
structure Run where
  /-- Successful ordinary factor pair in little-endian binary words. -/
  factors : Option (List Bool × List Bool)
  /-- Actual original-prefix count queries executed by the search. -/
  queries : ℕ
  /-- All actual original root acquisition and physical recursive reports. -/
  queryWork : ℕ
  /-- Actual input zero test, radix shift/add and final validation/division. -/
  arithmeticClock : ℕ
  /-- Typed constructor/index/label/control reports, requiring host lowering. -/
  metadataWork : ℕ

/-- Original binary input is the only input. No acquired count, table, mode,
coefficient, word getter, decoder result or factor answer is supplied. -/
def run (input : List Bool) : Run :=
  let initial := nonzeroBits input
  if hz : initial.nonzero=true then
    let N := bitValue input
    let hN : 0 < N := (nonzeroBits_correct input).mp hz
    let queried := SemiprimeD1WordTapePublicSearch.search N hN
    match queried.result.values with
    | none => ⟨none,queried.result.queries,queried.queryWork,initial.clock+3,
      queried.metadataWork+10*(wireCount N+input.length+1)⟩
    | some values =>
      let operand := SemiprimeD1PublicOperandBits.run N values 0
      let checked := SemiprimeD1FactorValidationBits.run input operand.bits
      let answer := if checked.valid then some (operand.bits,checked.cofactor) else none
      ⟨answer,queried.result.queries,queried.queryWork,
        initial.clock+operand.arithmeticClock+checked.clock+7,
        queried.metadataWork+operand.metadataWork+10*(wireCount N+input.length+values.length+1)⟩
  else ⟨none,0,0,initial.clock+3,10*(input.length+1)⟩

/-- Every successful byte result is a true ordinary factor pair on every input. -/
theorem run_sound (input left right : List Bool) (h : (run input).factors=some (left,right)) :
    bitValue left*bitValue right=bitValue input ∧ 2 ≤ bitValue left ∧ 2 ≤ bitValue right := by
  dsimp only [run] at h
  split at h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
        exact SemiprimeD1FactorValidationBits.run_factor_pair _ _ (by assumption)
      · cases h
  · cases h

/-- Closed search completeness and ordinary decoded factors, derived from the
exact actual original-prefix counter without any count supplier at execution. -/
theorem selected_complete (N p q : ℕ) (hN : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N=p*q) :
    ∃ values,(SemiprimeD1WordTapePublicSearch.search N hN).result.values=some values ∧
      2 ≤ decodeOperand N values 0 ∧ 2 ≤ decodeOperand N values 1 ∧
        decodeOperand N values 0*decodeOperand N values 1=N := by
  have hc := SemiprimeD1PublicCorrectness.prefixCount_exact N p q hN hp hq hsem
  obtain ⟨values,hvalues⟩ := SemiprimeD1PublicCountConsequences.search_exists N p q hN hp hq hsem hc
  have he : (SemiprimeD1WordTapePublicSearch.search N hN).result.values=
      (SemiprimeD1PublicCounter.search N hN).values :=
    congrArg SemiprimeCountRecovery.SearchResult.values
      ((SemiprimeD1WordTapePublicSearch.search_spec N hN).trans
        ((SemiprimeD1WordTapePublicCounter.search_eq_physical N hN).trans
          (SemiprimeD1PhysicalPublicCounter.search_eq_original N hN)))
  exact ⟨values,he.trans hvalues,
    SemiprimeD1PublicCountConsequences.selected_factor_pair N hN hc values hvalues⟩

/-- Every semiprime, including a repeated prime, produces an entire actual
binary factor pair. All word/count/search/carry/cofactor semantics are closed. -/
theorem run_complete (input : List Bool) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hsem : bitValue input=p*q) :
    ∃ left right,(run input).factors=some (left,right) ∧
      bitValue left*bitValue right=bitValue input ∧
      2 ≤ bitValue left ∧ 2 ≤ bitValue right ∧ (bitValue left=p ∨ bitValue left=q) := by
  have hN : 0 < bitValue input := by rw [hsem];exact Nat.mul_pos hp.pos hq.pos
  have hz := (nonzeroBits_correct input).mpr hN
  obtain ⟨values,hvalues,hl,hr,hprod⟩ := selected_complete (bitValue input) p q hN hp hq hsem
  let operand := SemiprimeD1PublicOperandBits.run (bitValue input) values 0
  have hd : bitValue operand.bits=decodeOperand (bitValue input) values 0 :=
    SemiprimeD1PublicOperandBits.run_value _ _ _
  have hlt : bitValue operand.bits < bitValue input := by rw [hd];nlinarith
  have hdvd : bitValue operand.bits ∣ bitValue input := by
    rw [hd]
    exact ⟨decodeOperand (bitValue input) values 1,hprod.symm⟩
  have hflag : (SemiprimeD1FactorValidationBits.run input operand.bits).valid=true :=
    (SemiprimeD1FactorValidationBits.run_valid input operand.bits).mpr
      ⟨hd.symm ▸ hl,hlt,Nat.mod_eq_zero_of_dvd hdvd⟩
  have hout : (run input).factors=some
      (operand.bits,(SemiprimeD1FactorValidationBits.run input operand.bits).cofactor) := by
    dsimp only [run]
    rw [dite_eq_left hz,hvalues]
    exact ite_eq_left hflag
  have hpair := SemiprimeD1FactorValidationBits.run_factor_pair input operand.bits hflag
  refine ⟨operand.bits,(SemiprimeD1FactorValidationBits.run input operand.bits).cofactor,
    hout,hpair.1,hpair.2.1,hpair.2.2,?_⟩
  exact SemiprimeD1SemiprimePrefix.left_factor_eq p q _ _ hp hq hpair.2.1 hpair.2.2
    (hpair.1.trans hsem)

/-- The byte-producing execution makes only the same original linear number
of count queries; validation and cofactor production add none. -/
theorem run_queries (input : List Bool) : (run input).queries ≤ wireCount (bitValue input)+1 := by
  dsimp only [run]
  split
  · have hs := SemiprimeD1WordTapePublicSearch.search_queries (bitValue input)
      ((nonzeroBits_correct input).mp (by assumption))
    split <;> exact hs
  · dsimp only
    omega

end RiemannGaussian.SemiprimeD1WordTapeBinaryFactorExecution
