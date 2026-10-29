/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramSafe
import RiemannGaussian.SemiprimeSourceArrayProgramCompiler
import RiemannGaussian.SemiprimeSourceInterpolationBits

/-! # Whole generated source-array safety from original leaves
This instantiates actual emitted scalar operations at their actual environments.
The only numeric caps concern original leaf dimensions and the syntax-node cap.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace RiemannGaussian.SemiprimeSourceArrayCompilerSafe
open scoped BigOperators
open Polynomial
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation
open SemiprimeRationalBits SemiprimeJetArrayHeight
open SemiprimeSourceArrayProgramIR SemiprimeSourceArrayProgramBlocks
open SemiprimeSourceArrayProgramLowering SemiprimeSourceArrayProgramSafe
open SemiprimeSourceArrayProgramCompiler SemiprimeSourceCodeArrayHeight
open SemiprimeSourceCodeArrays (nodes)

/-- Every actual original subtree coefficient fits the shared original node cap. -/
theorem coefficient_fits (J d B N W : ℕ) (p : PolynomialCode ℚ) (hd : 0 < d)
    (hp : Leaves d B p) (hN : nodes p ≤ N) (hden : d^N<2^W)
    (hnum : base J d B^N<2^W) (k : ℕ) (hk : k < J) : Fits (p.denote.coeff k) W := by
  have hr := subtree_representation J d B N hd p p hp hN (.refl p) k hk
  rw [SemiprimeSourceCodeArrays.compile_coefficient J p k hk] at hr
  exact fits_representation (pow_pos hd _) hr hden hnum

/-- Every emitted original convolution prefix fits the SAME full-tree cap. -/
theorem prefix_fits (J d B N W : ℕ) (p q : PolynomialCode ℚ) (hd : 0 < d)
    (hp : Leaves d B (.mul p q)) (hN : nodes (.mul p q) ≤ N)
    (hden : d^N<2^W) (hnum : base J d B^N<2^W)
    (k len : ℕ) (hk : k < J) (hlen : len ≤ k+1) :
    Fits (∑ i∈Finset.range len,p.denote.coeff i*q.denote.coeff (k-i)) W := by
  have hr := subtree_convolution_slice J d B N hd (.mul p q) p q hp hN
    (.refl _) k 0 len hk (by omega)
  simp only [Nat.zero_add] at hr
  have heq : (∑ i∈Finset.range len,
      SemiprimeJetArray.coefficient (SemiprimeSourceCodeArrays.compile J p).coefficients i*
      SemiprimeJetArray.coefficient (SemiprimeSourceCodeArrays.compile J q).coefficients (k-i)) =
      ∑ i∈Finset.range len,p.denote.coeff i*q.denote.coeff (k-i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [SemiprimeSourceCodeArrays.compile_coefficient J p i (by omega),
      SemiprimeSourceCodeArrays.compile_coefficient J q (k-i) (by omega)]
  rw [heq] at hr
  exact fits_representation (pow_pos hd _) hr hden hnum

/-- Each separately cached scalar product also fits; it is a length-one slice,
so safety does not rely on cancellation in a final convolution coefficient. -/
theorem product_fits (J d B N W : ℕ) (p q : PolynomialCode ℚ) (hd : 0 < d)
    (hp : Leaves d B (.mul p q)) (hN : nodes (.mul p q) ≤ N)
    (hden : d^N<2^W) (hnum : base J d B^N<2^W)
    (k i : ℕ) (hk : k < J) (hi : i ≤ k) :
    Fits (p.denote.coeff i*q.denote.coeff (k-i)) W := by
  have hr := subtree_convolution_slice J d B N hd (.mul p q) p q hp hN
    (.refl _) k i 1 hk (by omega)
  simp only [Finset.sum_range_one,Nat.add_zero] at hr
  rw [SemiprimeSourceCodeArrays.compile_coefficient J p i (by omega),
    SemiprimeSourceCodeArrays.compile_coefficient J q (k-i) (by omega)] at hr
  exact fits_representation (pow_pos hd _) hr hden hnum

/-- ALL emitted instructions are safe from original leaf and node bounds.
There is no advised intermediate Fits or final coefficient value premise. -/
theorem compile_safe (J zeroId oneId next d B N W : ℕ) (literal : ℚ → ℕ)
    (p : PolynomialCode ℚ) (env : ℕ → ℚ) (hd : 0 < d)
    (hLeaves : Leaves d B p) (hN : nodes p ≤ N)
    (hden : d^N<2^W) (hnum : base J d B^N<2^W)
    (hz : zeroId < next) (ho : oneId < next) (hez : env zeroId=0) (heo : env oneId=1)
    (hl : LiteralInputs p literal next env) :
    Safe W (compile J zeroId oneId next literal p).code next env := by
  induction p generalizing next env with
  | constant c => trivial
  | indeterminate => trivial
  | add p q ihp ihq =>
    let left := compile J zeroId oneId next literal p
    let middle := next+left.code.length
    let e := evaluate left.code next env
    have hNp : nodes p ≤ N := by change nodes p+nodes q+1 ≤ N at hN;omega
    have hNq : nodes q ≤ N := by change nodes p+nodes q+1 ≤ N at hN;omega
    have lp : LiteralInputs p literal next env := fun c hc => hl c (List.mem_append_left _ hc)
    have hp := compile_spec J zeroId oneId next literal p env hz ho hez heo lp
    change WellFormed next left.code ∧ (∀ k < J,left.output k < next+left.code.length) ∧
      (∀ k < J,evaluate left.code next env (left.output k)=p.denote.coeff k) at hp
    have rq : LiteralInputs q literal middle e := by
      intro c hc
      have h := hl c (List.mem_append_right _ hc)
      exact ⟨lt_of_lt_of_le h.1 (by dsimp [middle];omega),(evaluate_old left.code next _ env h.1).trans h.2⟩
    have hzq : zeroId < middle := by dsimp [middle];omega
    have hoq : oneId < middle := by dsimp [middle];omega
    have hezq : e zeroId=0 := (evaluate_old left.code next zeroId env hz).trans hez
    have heoq : e oneId=1 := (evaluate_old left.code next oneId env ho).trans heo
    have hq := compile_spec J zeroId oneId middle literal q e hzq hoq hezq heoq rq
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
    change Safe W (combined++addCode J left.output right.output) next env
    rw [safe_append,safe_append]
    refine ⟨⟨ihp next env hLeaves.1 hNp hz ho hez heo lp,
      ihq middle e hLeaves.2 hNq hzq hoq hezq heoq rq⟩,?_⟩
    change Safe W (addCode J left.output right.output) start e'
    apply independent_safe
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
      exact ⟨hleft k (List.mem_range.mp hk),hright k (List.mem_range.mp hk)⟩
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
      have hk' := List.mem_range.mp hk
      change Fits (e' (left.output k)+e' (right.output k)) W
      rw [hpv k hk',hqv k hk']
      simpa only [PolynomialCode.denote,coeff_add] using
        coefficient_fits J d B N W (.add p q) hd hLeaves hN hden hnum k hk'
  | mul p q ihp ihq =>
    let left := compile J zeroId oneId next literal p
    let middle := next+left.code.length
    let e := evaluate left.code next env
    have hNp : nodes p ≤ N := by change nodes p+nodes q+1 ≤ N at hN;omega
    have hNq : nodes q ≤ N := by change nodes p+nodes q+1 ≤ N at hN;omega
    have lp : LiteralInputs p literal next env := fun c hc => hl c (List.mem_append_left _ hc)
    have hp := compile_spec J zeroId oneId next literal p env hz ho hez heo lp
    change WellFormed next left.code ∧ (∀ k < J,left.output k < next+left.code.length) ∧
      (∀ k < J,evaluate left.code next env (left.output k)=p.denote.coeff k) at hp
    have rq : LiteralInputs q literal middle e := by
      intro c hc
      have h := hl c (List.mem_append_right _ hc)
      exact ⟨lt_of_lt_of_le h.1 (by dsimp [middle];omega),(evaluate_old left.code next _ env h.1).trans h.2⟩
    have hzq : zeroId < middle := by dsimp [middle];omega
    have hoq : oneId < middle := by dsimp [middle];omega
    have hezq : e zeroId=0 := (evaluate_old left.code next zeroId env hz).trans hez
    have heoq : e oneId=1 := (evaluate_old left.code next oneId env ho).trans heo
    have hq := compile_spec J zeroId oneId middle literal q e hzq hoq hezq heoq rq
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
    change Safe W (combined++mulCode zeroId start left.output right.output J) next env
    rw [safe_append,safe_append]
    refine ⟨⟨ihp next env hLeaves.1 hNp hz ho hez heo lp,
      ihq middle e hLeaves.2 hNq hzq hoq hezq heoq rq⟩,?_⟩
    change Safe W (mulCode zeroId start left.output right.output J) start e'
    apply mulCode_safe_known zeroId start J W left.output right.output e'
    · dsimp [start];omega
    · exact (evaluate_old combined next zeroId env hz).trans hez
    · exact hleft
    · exact hright
    · intro k hk i hi
      rw [hpv i (by omega),hqv (k-i) (by omega)]
      exact product_fits J d B N W p q hd hLeaves hN hden hnum k i hk hi
    · intro k hk m hm
      have heq : (∑ i∈Finset.range m,e' (left.output i)*e' (right.output (k-i)))=
          ∑ i∈Finset.range m,p.denote.coeff i*q.denote.coeff (k-i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have him := Finset.mem_range.mp hi
        rw [hpv i (by omega),hqv (k-i) (by omega)]
      rw [heq]
      exact prefix_fits J d B N W p q hd hLeaves hN hden hnum k m hk hm

/-- Actual ORIGINAL interpolation code is safe at stateBits+1, including
all scalar products and accumulator states. Only original literal-bank values
and initialized IDs are required; no encoded-bank or intermediate-fit oracle. -/
theorem source_safe {r Q : ℕ} (A R zeroId oneId next : ℕ) (literal : ℚ → ℕ)
    (a y : OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType r Q 1)
    (env : ℕ → ℚ) (hz : zeroId < next) (ho : oneId < next)
    (hez : env zeroId=0) (heo : env oneId=1)
    (hl : LiteralInputs
      (SemiprimeSourceInterpolationExecution.code (SemiprimeBinomialExecution.parity A R) a 0 y)
      literal next env) :
    Safe (SemiprimeSourceInterpolationBits.stateBits A Q R+1)
      (compile (R+1) zeroId oneId next literal
        (SemiprimeSourceInterpolationExecution.code (SemiprimeBinomialExecution.parity A R) a 0 y)).code next env := by
  have hc := SemiprimeSourceInterpolationBits.common_caps_dyadic A Q R
  have hpow : 2^SemiprimeSourceInterpolationBits.stateBits A Q R <
      2^(SemiprimeSourceInterpolationBits.stateBits A Q R+1) := by
    rw [pow_succ]
    have hp := Nat.two_pow_pos (SemiprimeSourceInterpolationBits.stateBits A Q R)
    omega
  exact compile_safe (R+1) zeroId oneId next
    (SemiprimeSourceInterpolationHeight.leafDenominator Q R)
    (SemiprimeSourceInterpolationHeight.leafNumerator A Q R)
    (SemiprimeSourceInterpolationHeight.nodeCap Q)
    (SemiprimeSourceInterpolationBits.stateBits A Q R+1) literal _ env
    (SemiprimeSourceInterpolationHeight.leafDenominator_positive Q R)
    (SemiprimeSourceInterpolationHeight.code_leaves A R a y)
    (SemiprimeSourceInterpolationHeight.code_nodes A R a y)
    (hc.1.trans_lt hpow) (hc.2.trans_lt hpow) hz ho hez heo hl

/-- Literal enumeration traverses exactly the original bounded constant leaves. -/
theorem literal_representation (d B : ℕ) (p : PolynomialCode ℚ)
    (hp : Leaves d B p) (c : ℚ) (hc : c∈constants p) : Representation c d B := by
  induction p with
  | constant a =>
    simp only [constants,List.mem_singleton] at hc
    subst c
    exact hp
  | indeterminate => simp only [constants,List.not_mem_nil] at hc
  | add p q ihp ihq =>
    rcases List.mem_append.mp hc with h|h
    · exact ihp hp.1 h
    · exact ihq hp.2 h
  | mul p q ihp ihq =>
    rcases List.mem_append.mp hc with h|h
    · exact ihp hp.1 h
    · exact ihq hp.2 h

/-- Every actually acquired ORIGINAL literal fits the same physical bank width;
this supplies the encoder bound, not a pre-encoded bank oracle. -/
theorem source_literal_bounds {r Q : ℕ} (A R : ℕ)
    (a y : OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType r Q 1)
    (c : ℚ) (hc : c∈constants
      (SemiprimeSourceInterpolationExecution.code (SemiprimeBinomialExecution.parity A R) a 0 y)) :
    c.den ≤ 2^SemiprimeSourceInterpolationBits.stateBits A Q R ∧
      c.num.natAbs ≤ 2^SemiprimeSourceInterpolationBits.stateBits A Q R := by
  have hr := literal_representation _ _ _
    (SemiprimeSourceInterpolationHeight.code_leaves A R a y) c hc
  have hb := representation_reduced_bound
    (SemiprimeSourceInterpolationHeight.leafDenominator_positive Q R) hr
  have hbits : SemiprimeSourceInterpolationBits.leafBits A Q R ≤
      SemiprimeSourceInterpolationBits.stateBits A Q R := by
    unfold SemiprimeSourceInterpolationBits.stateBits SemiprimeSourceInterpolationHeight.nodeCap
    nlinarith
  have hd := (SemiprimeSourceInterpolationBits.leaf_denominator_dyadic Q R).trans
    (Nat.pow_le_pow_right (by decide) (show SemiprimeSourceInterpolationBits.leafDenominatorBits Q R ≤
      SemiprimeSourceInterpolationBits.stateBits A Q R by
      unfold SemiprimeSourceInterpolationBits.leafBits at hbits;omega))
  have hn := (SemiprimeSourceInterpolationBits.leaf_numerator_dyadic A Q R).trans
    (Nat.pow_le_pow_right (by decide) hbits)
  exact ⟨hb.1.trans hd,hb.2.trans hn⟩

end RiemannGaussian.SemiprimeSourceArrayCompilerSafe
