/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramBlocks
import RiemannGaussian.SemiprimeSourceCodeArrayHeight

/-! # Generated cached coefficient-array programs for original finite source syntax
Literal constants are extracted from the original expression itself. Recursive
children are compiled once; stable register IDs preserve both cached arrays.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeSourceArrayProgramCompiler
open scoped BigOperators
open Polynomial
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation
open SemiprimeSourceArrayProgramIR SemiprimeSourceArrayProgramBlocks

/-- Exactly the original literal leaves, in syntax traversal order. -/
def constants : PolynomialCode ℚ → List ℚ
  | .constant c => [c]
  | .indeterminate => []
  | .add p q => constants p++constants q
  | .mul p q => constants p++constants q

/-- Cached generated code and its stable output IDs, not computed coefficient answers. -/
structure Block where
  /-- Generated scalar instructions. -/
  code : List Instruction
  /-- One stable register per requested coefficient. -/
  output : ℕ → ℕ

/-- Cache both recursively generated child arrays, then execute a single array operation. -/
def compile (J zeroId oneId next : ℕ) (literal : ℚ → ℕ) : PolynomialCode ℚ → Block
  | .constant c => ⟨[],fun k => if k=0 then literal c else zeroId⟩
  | .indeterminate => ⟨[],fun k => if k=1 then oneId else zeroId⟩
  | .add p q =>
      let left := compile J zeroId oneId next literal p
      let right := compile J zeroId oneId (next+left.code.length) literal q
      let combined := left.code++right.code
      let start := next+combined.length
      ⟨combined++addCode J left.output right.output,fun k => start+k⟩
  | .mul p q =>
      let left := compile J zeroId oneId next literal p
      let right := compile J zeroId oneId (next+left.code.length) literal q
      let combined := left.code++right.code
      let start := next+combined.length
      ⟨combined++mulCode zeroId start left.output right.output J,fun k => mulResult start k⟩

/-- All initial literal IDs are original leaf values and predate fresh output registers. -/
def LiteralInputs (p : PolynomialCode ℚ) (literal : ℚ → ℕ) (next : ℕ) (env : ℕ → ℚ) : Prop :=
  ∀ c∈constants p,literal c < next ∧ env (literal c)=c

/-- Complete generated-array correctness and initialized-register invariant. -/
theorem compile_spec (J zeroId oneId next : ℕ) (literal : ℚ → ℕ) (p : PolynomialCode ℚ)
    (env : ℕ → ℚ) (hz : zeroId < next) (ho : oneId < next)
    (hez : env zeroId=0) (heo : env oneId=1) (hl : LiteralInputs p literal next env) :
    let out := compile J zeroId oneId next literal p
    WellFormed next out.code ∧ (∀ k < J,out.output k < next+out.code.length) ∧
      ∀ k < J,evaluate out.code next env (out.output k)=p.denote.coeff k := by
  induction p generalizing next env with
  | constant c =>
    have hc := hl c (by simp [constants])
    refine ⟨trivial,?_,?_⟩
    · intro k _; dsimp only [compile]; split_ifs  <;> simp only [List.length_nil,Nat.add_zero]  <;> omega
    · intro k _
      simp only [compile,evaluate,PolynomialCode.denote,coeff_C]
      split_ifs
      · exact hc.2
      · exact hez
  | indeterminate =>
    refine ⟨trivial,?_,?_⟩
    · intro k _; dsimp only [compile]; split_ifs  <;> simp only [List.length_nil,Nat.add_zero]  <;> omega
    · intro k _
      simp only [compile,evaluate,PolynomialCode.denote,coeff_X]
      by_cases hk : k=1
      · simp only [hk,ite_true];exact heo
      · have hk' : (1:ℕ)≠k := Ne.symm hk
        simp only [hk,hk',ite_false];exact hez
  | add p q ihp ihq =>
    let left := compile J zeroId oneId next literal p
    let middle := next+left.code.length
    let e := evaluate left.code next env
    have hp := ihp next env hz ho hez heo (fun c hc => hl c (List.mem_append_left _ hc))
    change WellFormed next left.code ∧ (∀ k < J,left.output k < next+left.code.length) ∧
      (∀ k < J,evaluate left.code next env (left.output k)=p.denote.coeff k) at hp
    have hqInputs : LiteralInputs q literal middle e := by
      intro c hc
      have hh := hl c (List.mem_append_right _ hc)
      exact ⟨lt_of_lt_of_le hh.1 (by dsimp [middle];omega),
        (evaluate_old left.code next _ env hh.1).trans hh.2⟩
    have hq := ihq middle e (by dsimp [middle];omega) (by dsimp [middle];omega)
      ((evaluate_old left.code next zeroId env hz).trans hez)
      ((evaluate_old left.code next oneId env ho).trans heo) hqInputs
    let right := compile J zeroId oneId middle literal q
    change WellFormed middle right.code ∧ (∀ k < J,right.output k < middle+right.code.length) ∧
      (∀ k < J,evaluate right.code middle e (right.output k)=q.denote.coeff k) at hq
    let combined := left.code++right.code
    let start := next+combined.length
    let e' := evaluate combined next env
    have hleft (k : ℕ) (hk : k < J) : left.output k < start :=
      (hp.2.1 k hk).trans_le (by dsimp [start,combined,middle];simp only [List.length_append];omega)
    have hright (k : ℕ) (hk : k < J) : right.output k < start := by
      have h := hq.2.1 k hk
      dsimp only [start,combined]
      simp only [List.length_append]
      exact lt_of_lt_of_eq h (by dsimp [middle];omega)
    have hpv (k : ℕ) (hk : k < J) : e' (left.output k)=p.denote.coeff k := by
      rw [show e'=evaluate right.code middle e by dsimp [e',combined];rw [evaluate_append]]
      exact (evaluate_old right.code middle _ e (hp.2.1 k hk)).trans (hp.2.2 k hk)
    have hqv (k : ℕ) (hk : k < J) : e' (right.output k)=q.denote.coeff k := by
      rw [show e'=evaluate right.code middle e by dsimp [e',combined];rw [evaluate_append]]
      exact hq.2.2 k hk
    change WellFormed next (combined++addCode J left.output right.output) ∧
      (∀ k < J,start+k < next+(combined++addCode J left.output right.output).length) ∧
      (∀ k < J,evaluate (combined++addCode J left.output right.output) next env (start+k)=(PolynomialCode.add p q).denote.coeff k)
    refine ⟨?_,?_,?_⟩
    · rw [wellFormed_append,wellFormed_append]
      exact ⟨⟨hp.1,hq.1⟩,addCode_wellFormed J start left.output right.output hleft hright⟩
    · intro k hk; simp only [List.length_append,addCode_length];dsimp [start];omega
    · intro k hk
      rw [evaluate_append]
      change evaluate (addCode J left.output right.output) start e' (start+k)=_
      rw [addCode_correct J start k left.output right.output e' hleft hright hk,hpv k hk,hqv k hk]
      simp only [PolynomialCode.denote,coeff_add]
  | mul p q ihp ihq =>
    let left := compile J zeroId oneId next literal p
    let middle := next+left.code.length
    let e := evaluate left.code next env
    have hp := ihp next env hz ho hez heo (fun c hc => hl c (List.mem_append_left _ hc))
    change WellFormed next left.code ∧ (∀ k < J,left.output k < next+left.code.length) ∧
      (∀ k < J,evaluate left.code next env (left.output k)=p.denote.coeff k) at hp
    have hqInputs : LiteralInputs q literal middle e := by
      intro c hc
      have hh := hl c (List.mem_append_right _ hc)
      exact ⟨lt_of_lt_of_le hh.1 (by dsimp [middle];omega),
        (evaluate_old left.code next _ env hh.1).trans hh.2⟩
    have hq := ihq middle e (by dsimp [middle];omega) (by dsimp [middle];omega)
      ((evaluate_old left.code next zeroId env hz).trans hez)
      ((evaluate_old left.code next oneId env ho).trans heo) hqInputs
    let right := compile J zeroId oneId middle literal q
    change WellFormed middle right.code ∧ (∀ k < J,right.output k < middle+right.code.length) ∧
      (∀ k < J,evaluate right.code middle e (right.output k)=q.denote.coeff k) at hq
    let combined := left.code++right.code
    let start := next+combined.length
    let e' := evaluate combined next env
    have hleft (k : ℕ) (hk : k < J) : left.output k < start :=
      (hp.2.1 k hk).trans_le (by dsimp [start,combined,middle];simp only [List.length_append];omega)
    have hright (k : ℕ) (hk : k < J) : right.output k < start := by
      have h := hq.2.1 k hk
      dsimp only [start,combined]
      simp only [List.length_append]
      exact lt_of_lt_of_eq h (by dsimp [middle];omega)
    have hpv (k : ℕ) (hk : k < J) : e' (left.output k)=p.denote.coeff k := by
      rw [show e'=evaluate right.code middle e by dsimp [e',combined];rw [evaluate_append]]
      exact (evaluate_old right.code middle _ e (hp.2.1 k hk)).trans (hp.2.2 k hk)
    have hqv (k : ℕ) (hk : k < J) : e' (right.output k)=q.denote.coeff k := by
      rw [show e'=evaluate right.code middle e by dsimp [e',combined];rw [evaluate_append]]
      exact hq.2.2 k hk
    have hzero : e' zeroId=0 := (evaluate_old combined next zeroId env hz).trans hez
    have hzs : zeroId < start := by dsimp [start];omega
    change WellFormed next (combined++mulCode zeroId start left.output right.output J) ∧
      (∀ k < J,mulResult start k < next+(combined++mulCode zeroId start left.output right.output J).length) ∧
      (∀ k < J,evaluate (combined++mulCode zeroId start left.output right.output J) next env (mulResult start k)=(PolynomialCode.mul p q).denote.coeff k)
    refine ⟨?_,?_,?_⟩
    · rw [wellFormed_append,wellFormed_append]
      exact ⟨⟨hp.1,hq.1⟩,mulCode_wellFormed zeroId start J left.output right.output hzs hleft hright⟩
    · intro k hk
      have h := mulResult_lt start J k hk
      simpa only [List.length_append,mulCode_length,start,Nat.add_assoc] using h
    · intro k hk
      rw [evaluate_append]
      change evaluate (mulCode zeroId start left.output right.output J) start e' (mulResult start k)=_
      rw [mulCode_correct zeroId start J k left.output right.output e' hzs hzero hleft hright hk]
      simp only [PolynomialCode.denote,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro i hi
      have hii := Finset.mem_range.mp hi
      rw [hpv i (by omega),hqv (k-i) (by omega)]

/-- Initial constants are literally extracted from the ORIGINAL syntax, including zero and one. -/
def bank (p : PolynomialCode ℚ) : List ℚ := 0::1::constants p

/-- Literal lookup is computed on that finite original syntax bank. -/
def literalId (p : PolynomialCode ℚ) (c : ℚ) : ℕ := 2+(constants p).idxOf c

/-- Mathematical interpretation of the actual original bank; not called by code generation. -/
def initialEnv (p : PolynomialCode ℚ) (i : ℕ) : ℚ := ((bank p)[i]?).getD 0

/-- Complete generated program; no compiled code or coefficient bank is a runtime input. -/
def program (J : ℕ) (p : PolynomialCode ℚ) : Block :=
  compile J 0 1 (bank p).length (literalId p) p

/-- Exact original literal-bank length. -/
theorem bank_length (p : PolynomialCode ℚ) : (bank p).length=2+(constants p).length := by
  simp only [bank,List.length_cons]
  omega

/-- Every actual literal lookup returns its original constant and a valid initial ID. -/
theorem bank_literals (p : PolynomialCode ℚ) : LiteralInputs p (literalId p) (bank p).length (initialEnv p) := by
  intro c hc
  have hi := List.idxOf_lt_length_of_mem hc
  refine ⟨?_,?_⟩
  · rw [bank_length]
    unfold literalId
    omega
  · unfold initialEnv literalId
    rw [show 2+(constants p).idxOf c=(constants p).idxOf c+2 by omega]
    change ((constants p)[(constants p).idxOf c]?).getD 0=c
    rw [List.getElem?_idxOf hc,Option.getD_some]

/-- Full initialized compiler theorem for the actual ORIGINAL-derived bank. -/
theorem program_spec (J : ℕ) (p : PolynomialCode ℚ) :
    WellFormed (bank p).length (program J p).code ∧
      (∀ k < J,(program J p).output k < (bank p).length+(program J p).code.length) ∧
      ∀ k < J,evaluate (program J p).code (bank p).length (initialEnv p)
        ((program J p).output k)=p.denote.coeff k := by
  apply compile_spec
  · rw [bank_length];omega
  · rw [bank_length];omega
  · simp [initialEnv,bank]
  · simp [initialEnv,bank]
  · exact bank_literals p

/-- The generated program refines the ACTUAL cached source coefficient interpreter. -/
theorem program_original_coefficient (J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) (hk : k < J) :
    evaluate (program J p).code (bank p).length (initialEnv p) ((program J p).output k)=
      SemiprimeJetArray.coefficient (SemiprimeSourceCodeArrays.compile J p).coefficients k :=
  ((program_spec J p).2.2 k hk).trans (SemiprimeSourceCodeArrays.compile_coefficient J p k hk).symm

/-- Literal banks contain no expansion beyond original syntax leaves. -/
theorem constants_length_le (p : PolynomialCode ℚ) : (constants p).length ≤ SemiprimeSourceCodeArrays.nodes p := by
  induction p with
  | constant c => simp [constants,SemiprimeSourceCodeArrays.nodes]
  | indeterminate => simp [constants,SemiprimeSourceCodeArrays.nodes]
  | add p q hp hq => simp only [constants,List.length_append,SemiprimeSourceCodeArrays.nodes];omega
  | mul p q hp hq => simp only [constants,List.length_append,SemiprimeSourceCodeArrays.nodes];omega

/-- Actual generated scalar code has fixed polynomial size in syntax and array width. -/
theorem compile_code_length (J zeroId oneId next : ℕ) (literal : ℚ → ℕ) (p : PolynomialCode ℚ) :
    (compile J zeroId oneId next literal p).code.length ≤
      SemiprimeSourceCodeArrays.nodes p*(J*(J+1)+J) := by
  induction p generalizing next with
  | constant c => simp [compile,SemiprimeSourceCodeArrays.nodes]
  | indeterminate => simp [compile,SemiprimeSourceCodeArrays.nodes]
  | add p q hp hq =>
    have hl := hp next
    have hr := hq (next+(compile J zeroId oneId next literal p).code.length)
    simp only [compile,List.length_append,addCode_length,SemiprimeSourceCodeArrays.nodes]
    nlinarith
  | mul p q hp hq =>
    have hl := hp next
    have hr := hq (next+(compile J zeroId oneId next literal p).code.length)
    simp only [compile,List.length_append,mulCode_length,SemiprimeSourceCodeArrays.nodes]
    nlinarith

/-- The actual original-bank program has the same polynomial length bound. -/
theorem program_code_length (J : ℕ) (p : PolynomialCode ℚ) :
    (program J p).code.length ≤ SemiprimeSourceCodeArrays.nodes p*(J*(J+1)+J) :=
  compile_code_length J 0 1 (bank p).length (literalId p) p

/-- Actual literal values inherit the ORIGINAL leaf representations. -/
theorem constants_representation (d B : ℕ) (p : PolynomialCode ℚ)
    (hp : SemiprimeSourceCodeArrayHeight.Leaves d B p) :
    ∀ c∈constants p,SemiprimeJetArrayHeight.Representation c d B := by
  induction p with
  | constant c =>
    intro z hz
    simp only [constants,List.mem_singleton] at hz
    subst z
    exact hp
  | indeterminate => intro z hz;simp [constants] at hz
  | add p q ihp ihq =>
    intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact ihp hp.1 c hc
    · exact ihq hp.2 c hc
  | mul p q ihp ihq =>
    intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact ihp hp.1 c hc
    · exact ihq hp.2 c hc

/-- Every ORIGINAL-derived input word is bounded without a constant-table oracle. -/
theorem bank_representation (d B : ℕ) (p : PolynomialCode ℚ) (hd : 0 < d) (hdB : d ≤ B)
    (hp : SemiprimeSourceCodeArrayHeight.Leaves d B p) :
    ∀ c∈bank p,SemiprimeJetArrayHeight.Representation c d B := by
  intro c hc
  simp only [bank,List.mem_cons] at hc
  rcases hc with rfl|rfl|hc
  · exact SemiprimeJetArrayHeight.representation_mono (SemiprimeHermiteArrayHeight.representation_zero d) (Nat.zero_le _)
  · exact SemiprimeJetArrayHeight.representation_mono (SemiprimeHermiteArrayHeight.representation_one d hd) hdB
  · exact constants_representation d B p hp c hc

end RiemannGaussian.SemiprimeSourceArrayProgramCompiler
