/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitGeometricMarks

/-!
# Original geometric evaluations by exact convolution

Triangular powers reduce original polynomial evaluations at a geometric
progression to middle coefficients of one convolution. The base ratio is
a unit; neither target differences nor target collision factors are
inverted. The algebra holds over composite rings and at zero evaluations.
The actual Boolean preparation is separate from the fast convolution bit
engine and from the varying-seed detector batch.
-/

namespace RiemannGaussian.SemiprimeBitGeometricEvaluation

open scoped BigOperators DualNumber
open Polynomial TrivSqZeroExt
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitInverse
open SemiprimeBitIndexTraversal SemiprimeBitGeometricCoefficients
open SemiprimeBitGeometricMarks

/-- Proof-side exponent of the quadratic convolution phase. -/
noncomputable def triangular : ℕ→ℕ
  | 0 => 0
  | n+1 => triangular n+n

/-- The cross term is the geometric evaluation exponent; no division
by two or inverse of two is needed in the coefficient ring. -/
theorem triangular_add (i j : ℕ) :
    triangular (i+j)=triangular i+triangular j+i*j := by
  induction j with
  | zero => simp only [Nat.add_zero,triangular,Nat.mul_zero]
  | succ j ih =>
    rw [Nat.add_succ,triangular,ih,triangular]
    ring

/-- Exact cancellation of the two triangular weights retains the
original bilinear exponent over every coefficient ring. -/
theorem triangular_chirp {R : Type*} [CommRing R] (q : Rˣ) (i j : ℕ) :
    (((q^triangular i)⁻¹ : Rˣ) : R)*(q : R)^triangular (i+j)*
      (((q^triangular j)⁻¹ : Rˣ) : R)=(q : R)^(i*j) := by
  have hu : (q^triangular i)⁻¹*q^triangular (i+j)*(q^triangular j)⁻¹=q^(i*j) := by
    rw [triangular_add,pow_add,pow_add]
    group
  simpa only [Units.val_mul,Units.val_pow_eq_pow_val] using
    congrArg (fun u : Rˣ => (u : R)) hu

/-- A weighted convolution summand is exactly its original polynomial
summand, including zero and nonunit coefficient or starting target. -/
theorem chirp_term {R : Type*} [CommRing R] (q : Rˣ) (x a : R) (i j : ℕ) :
    (a*x^i*(((q^triangular i)⁻¹ : Rˣ) : R))*(q : R)^triangular (i+j)*
      (((q^triangular j)⁻¹ : Rˣ) : R)=a*(x*(q : R)^j)^i := by
  calc
    _ = a*x^i*((((q^triangular i)⁻¹ : Rˣ) : R)*(q : R)^triangular (i+j)*
        (((q^triangular j)⁻¹ : Rˣ) : R)) := by ring
    _ = a*x^i*(q : R)^(i*j) := by rw [triangular_chirp]
    _ = _ := by simp only [mul_pow,←pow_mul]; rw [Nat.mul_comm j i]; ring

/-- Proof-side polynomial of reversed, weighted original coefficients. -/
noncomputable def reversedChirpPolynomial {R : Type*} [CommRing R]
    (q : Rˣ) (x : R) (c : ℕ→R) (d : ℕ) : R[X] :=
  ∑ i∈Finset.range (d+1), monomial (d-i) (c i*x^i*(((q^triangular i)⁻¹ : Rˣ) : R))

/-- Proof-side polynomial of the shared positive triangular kernel. -/
noncomputable def chirpKernelPolynomial {R : Type*} [CommRing R] (q : Rˣ) (n : ℕ) : R[X] :=
  ∑ k∈Finset.range n, monomial k ((q : R)^triangular k)

/-- Every supplied kernel slot retains its literal triangular phase. -/
theorem chirpKernelPolynomial_coeff {R : Type*} [CommRing R] (q : Rˣ)
    {n k : ℕ} (hk : k<n) :
    (chirpKernelPolynomial q n).coeff k=(q : R)^triangular k := by
  simp [chirpKernelPolynomial,coeff_monomial,hk]

/-- A single convolution contains every original geometric evaluation
in its middle coefficient range. This identity assumes no separation or
unit condition on the evaluation points. -/
theorem geometric_convolution_sum {R : Type*} [CommRing R]
    (q : Rˣ) (x : R) (c : ℕ→R) (d J : ℕ) {j : ℕ} (hj : j<J) :
    (reversedChirpPolynomial q x c d*chirpKernelPolynomial q (d+J)).coeff (d+j)*
      (((q^triangular j)⁻¹ : Rˣ) : R)=
      ∑ i∈Finset.range (d+1), c i*(x*(q : R)^j)^i := by
  rw [reversedChirpPolynomial,Finset.sum_mul,finsetSum_coeff,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hid : i≤d := by have hh := Finset.mem_range.mp hi; omega
  have hindex : d+j=(i+j)+(d-i) := by omega
  rw [hindex,coeff_monomial_mul,chirpKernelPolynomial_coeff q (by omega : i+j<d+J)]
  exact chirp_term q x (c i) i j

/-- The middle coefficient is the exact original polynomial value,
with all coefficients through the chosen degree bound retained. -/
theorem geometric_convolution_eval {R : Type*} [CommRing R]
    (q : Rˣ) (x : R) (P : R[X]) (d J : ℕ) (hd : P.natDegree≤d)
    {j : ℕ} (hj : j<J) :
    (reversedChirpPolynomial q x P.coeff d*chirpKernelPolynomial q (d+J)).coeff (d+j)*
      (((q^triangular j)⁻¹ : Rˣ) : R)=P.eval (x*(q : R)^j) := by
  rw [geometric_convolution_sum q x P.coeff d J hj]
  exact (eval_eq_sum_range' (by omega : P.natDegree<d+1) _).symm

/-- Original short products retain the chosen degree bound even over
the composite coefficient ring. -/
theorem original_row_degree_le {R : Type*} [CommRing R] (alpha : R) (s : ℕ) :
    (SemiprimeGeometricRows.rowPolynomial alpha s).natDegree≤s := by
  unfold SemiprimeGeometricRows.rowPolynomial SemiprimeCartesianCompletion.rootPolynomial
  calc
    _ ≤ ∑ i∈Finset.range s, (X-C (alpha^i) : R[X]).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _i∈Finset.range s, 1 := Finset.sum_le_sum fun i _ => natDegree_X_sub_C_le _
    _ = s := by simp

/-- The original base polynomial has the same short degree bound;
its coefficients come from the original first-order polynomial. -/
theorem original_base_degree_le {R : Type*} [CommRing R] (alpha : R) (s : ℕ) :
    (SemiprimeSharedIntervalJet.babyBasePolynomial alpha s).natDegree≤s := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [←marked_coeff_base]
  have hz := natDegree_le_iff_coeff_eq_zero.mp (original_row_degree_le (markedBase alpha) s) k hk
  rw [hz,snd_zero]

/-- The SAME kernel evaluates all three ORIGINAL block polynomials,
with the base derivative taken at fixed target throughout. -/
theorem original_three_channel_convolution {R : Type*} [CommRing R]
    (alpha : R) (q : Rˣ) (x : R) (s J : ℕ) {j : ℕ} (hj : j<J) :
    let P := SemiprimeGeometricRows.rowPolynomial alpha s
    let H := SemiprimeSharedIntervalJet.babyBasePolynomial alpha s
    let K := chirpKernelPolynomial q (s+J)
    let phase := (((q^triangular j)⁻¹ : Rˣ) : R)
    ((reversedChirpPolynomial q x P.coeff s*K).coeff (s+j)*phase,
      (reversedChirpPolynomial q x P.derivative.coeff s*K).coeff (s+j)*phase,
      (reversedChirpPolynomial q x H.coeff s*K).coeff (s+j)*phase)=
      (P.eval (x*(q : R)^j),P.derivative.eval (x*(q : R)^j),H.eval (x*(q : R)^j)) := by
  dsimp only
  have hp := original_row_degree_le alpha s
  have hd := (natDegree_derivative_le (SemiprimeGeometricRows.rowPolynomial alpha s)).trans
    ((Nat.sub_le _ _).trans hp)
  rw [geometric_convolution_eval q x _ s J hp hj,
    geometric_convolution_eval q x _ s J hd hj,
    geometric_convolution_eval q x _ s J (original_base_degree_le alpha s) hj]

/-- Actual work of one triangular-phase update and count decrement. -/
structure GeometricKernelFrame where
  /-- Full Boolean remaining-count scan. -/
  scan : NonzeroReport
  /-- Actual count decrement passed to the child. -/
  decrement : SubReport
  /-- Current phase times current geometric step. -/
  power : ModularProduct
  /-- Current step times the supplied ratio word. -/
  step : ModularProduct

/-- Computed kernel words, final states, visits and primitive clock. -/
structure GeometricKernelReport where
  /-- Ordered literal triangular-phase words. -/
  words : List (List Bool)
  /-- Actual final triangular phase. -/
  power : List Bool
  /-- Actual final geometric step. -/
  step : List Bool
  /-- Every visited Boolean count update. -/
  frames : List GeometricKernelFrame
  /-- Full terminal count scan. -/
  finalScan : NonzeroReport
  /-- Complete modular products, scans, decrements and source references. -/
  clock : ℕ

/-- Generate triangular phases by TWO modular products per actual
Boolean count visit. No exponent value or quadratic-power oracle is used. -/
def geometricKernelLoopBits (modulus ratio power step remaining : List Bool) : GeometricKernelReport :=
  let scan := nonzeroBits remaining
  if hs : scan.nonzero=true then
    let decrement := subBits remaining [true] false
    let nextPower := modMulBits power step modulus
    let nextStep := modMulBits step ratio modulus
    let child := geometricKernelLoopBits modulus ratio nextPower.division.remainder
      nextStep.division.remainder decrement.result.bits
    ⟨power::child.words,child.power,child.step,⟨scan,decrement,nextPower,nextStep⟩::child.frames,
      child.finalScan,scan.clock+bitCost decrement.result+nextPower.clock+nextStep.clock+child.clock+12⟩
  else ⟨[],power,step,[],scan,scan.clock+5⟩
termination_by bitValue remaining
decreasing_by
  have hp := (nonzeroBits_correct remaining).mp hs
  rw [(decrementBits_value hp).2]
  omega

/-- Every emitted phase and both final states are their literal
triangular/geometric powers; padding and zero count are retained. -/
theorem geometricKernelLoopBits_exact (modulus ratio power step remaining : List Bool) (i : ℕ)
    (hp : (bitValue power : ZMod (bitValue modulus))=
      (bitValue ratio : ZMod (bitValue modulus))^triangular i)
    (hs : (bitValue step : ZMod (bitValue modulus))=(bitValue ratio : ZMod (bitValue modulus))^i) :
    (bitValue (geometricKernelLoopBits modulus ratio power step remaining).power : ZMod (bitValue modulus))=
      (bitValue ratio : ZMod (bitValue modulus))^triangular (i+bitValue remaining) ∧
    (bitValue (geometricKernelLoopBits modulus ratio power step remaining).step : ZMod (bitValue modulus))=
      (bitValue ratio : ZMod (bitValue modulus))^(i+bitValue remaining) ∧
    (geometricKernelLoopBits modulus ratio power step remaining).words.map
      (fun word => (bitValue word : ZMod (bitValue modulus)))=
      (List.range (bitValue remaining)).map
        (fun k => (bitValue ratio : ZMod (bitValue modulus))^triangular (i+k)) := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power step remaining i with
  | h n ih =>
    by_cases hscan : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hscan
      let decrement := subBits remaining [true] false
      let nextPower := modMulBits power step modulus
      let nextStep := modMulBits step ratio modulus
      have hdec : bitValue decrement.result.bits=n-1 := by
        exact (decrementBits_value hn).2.trans (by rw [he])
      have hnp : (bitValue nextPower.division.remainder : ZMod (bitValue modulus))=
          (bitValue ratio : ZMod (bitValue modulus))^triangular (i+1) := by
        rw [modular_product_value,hp,hs,triangular,pow_add]
      have hns : (bitValue nextStep.division.remainder : ZMod (bitValue modulus))=
          (bitValue ratio : ZMod (bitValue modulus))^(i+1) := by
        rw [modular_product_value,hs,pow_succ]
      have ht := ih _ (by omega : bitValue decrement.result.bits<n)
        nextPower.division.remainder nextStep.division.remainder decrement.result.bits (i+1) hnp hns rfl
      have hi : i+1+bitValue decrement.result.bits=i+n := by omega
      rw [hi] at ht
      rw [geometricKernelLoopBits]
      dsimp only
      simp only [dif_pos hscan]
      refine ⟨ht.1,ht.2.1,?_⟩
      change (bitValue power : ZMod (bitValue modulus))::
        (geometricKernelLoopBits modulus ratio nextPower.division.remainder nextStep.division.remainder
          decrement.result.bits).words.map _=_
      rw [hp,ht.2.2,hdec]
      have hlen : n=(n-1)+1 := by omega
      conv_rhs => rw [hlen,List.range_succ_eq_map,List.map_cons,List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro k _
      congr 2
      omega
    · have hn : n=0 := by have hz := counter_zero_of_clear hscan; omega
      rw [geometricKernelLoopBits]
      dsimp only
      simp only [dif_neg hscan,hn,List.range_zero,List.map_nil,Nat.add_zero]
      exact ⟨hp,hs,trivial⟩

/-- Every actual kernel visit is paid, output counts are exact, and
normalized phases retain the modulus's physical width. -/
theorem geometricKernelLoopBits_cost_width {W : ℕ} {modulus : List Bool}
    (hN : 0<bitValue modulus) (hW : 1≤W) (ratio power step remaining : List Bool)
    (hm : modulus.length≤W) (hratio : ratio.length≤W) (hp : power.length=modulus.length)
    (hs : step.length≤W) (hr : remaining.length≤W) :
    (geometricKernelLoopBits modulus ratio power step remaining).clock≤
      (bitValue remaining+1)*(400*(W+1)^2) ∧
    (geometricKernelLoopBits modulus ratio power step remaining).power.length=modulus.length ∧
    (geometricKernelLoopBits modulus ratio power step remaining).step.length≤W ∧
    (geometricKernelLoopBits modulus ratio power step remaining).words.length=bitValue remaining ∧
    (geometricKernelLoopBits modulus ratio power step remaining).frames.length=bitValue remaining ∧
    ∀ word∈(geometricKernelLoopBits modulus ratio power step remaining).words, word.length=modulus.length := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power step remaining with
  | h n ih =>
    have hscanCost := nonzeroBits_cost remaining
    by_cases hscan : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hscan
      let decrement := subBits remaining [true] false
      let nextPower := modMulBits power step modulus
      let nextStep := modMulBits step ratio modulus
      have hd : bitValue decrement.result.bits=n-1 := by
        exact (decrementBits_value hn).2.trans (by rw [he])
      have hdec : decrement.result.bits.length≤W := by
        rw [(subBits_counts remaining [true] false).2.2.2.2]
        exact max_le hr (by simpa only [List.length_cons,List.length_nil] using hW)
      have hnp := bounded_modMulBits (hp.le.trans hm) hs hm
      have hns := bounded_modMulBits hs hratio hm
      have hpw : nextPower.division.remainder.length=modulus.length := modMulBits_width hN
      have hsw : nextStep.division.remainder.length≤W := (modMulBits_width hN).le.trans hm
      have ht := ih _ (by omega : bitValue decrement.result.bits<n)
        nextPower.division.remainder nextStep.division.remainder decrement.result.bits hpw hsw hdec rfl
      have hsub := subBits_cost remaining [true] false
      have hmax : max remaining.length ([true] : List Bool).length≤W :=
        max_le hr (by simpa only [List.length_cons,List.length_nil] using hW)
      have hframe : (nonzeroBits remaining).clock+bitCost decrement.result+
          nextPower.clock+nextStep.clock+12≤400*(W+1)^2 := by
        dsimp only [decrement,nextPower,nextStep] at *
        nlinarith only [hscanCost,hr,hsub,hmax,hnp,hns,hW]
      rw [geometricKernelLoopBits]
      dsimp only
      simp only [dif_pos hscan,List.length_cons]
      refine ⟨?_,ht.2.1,ht.2.2.1,?_,?_,?_⟩
      · change (nonzeroBits remaining).clock+bitCost decrement.result+nextPower.clock+nextStep.clock+
          (geometricKernelLoopBits modulus ratio nextPower.division.remainder nextStep.division.remainder
            decrement.result.bits).clock+12≤_
        have hclock := ht.1
        have hcount : bitValue decrement.result.bits+1=n := by omega
        rw [hcount] at hclock
        calc
          _ ≤ 400*(W+1)^2+n*(400*(W+1)^2) := by omega
          _ = (n+1)*(400*(W+1)^2) := by ring
      · rw [ht.2.2.2.1]; omega
      · rw [ht.2.2.2.2.1]; omega
      · intro word hw
        rcases List.mem_cons.mp hw with hsame|htail
        · subst word
          exact hp
        · exact ht.2.2.2.2.2 word htail
    · have hn : n=0 := by have hz := counter_zero_of_clear hscan; omega
      rw [geometricKernelLoopBits]
      dsimp only
      simp only [dif_neg hscan,hn,List.length_nil]
      refine ⟨?_,hp,hs,trivial,trivial,?_⟩
      · simp only [Nat.zero_add,Nat.one_mul]
        nlinarith only [hscanCost,hr,hW]
      · intro word hw
        cases hw

/-- Proof-side scalar phase holds the marked channel fixed at zero. -/
noncomputable def scalarPhase {R : Type*} [Zero R] (a : R) : R[ε] := ⟨a,0⟩

/-- Freeze one actual scalar residue as a two-channel word; the empty
marked word is a literal zero, not derivative or inverse advice. -/
def scalarWord (word : List Bool) : MarkedWord := ⟨word,[]⟩

/-- The frozen scalar word has exactly zero first-order variation. -/
theorem scalarWord_value (modulus word : List Bool) :
    (scalarWord word).interpret modulus=scalarPhase (bitValue word : ZMod (bitValue modulus)) := by
  simp only [scalarWord,MarkedWord.interpret,scalarPhase,bitValue,Nat.cast_zero]
  rfl

/-- One actual original coefficient pair and every phase update. -/
structure GeometricWeightFrame where
  /-- Computed start-power times inverse triangular phase. -/
  factor : ModularProduct
  /-- Original value/base pair weighted by a frozen scalar phase. -/
  coefficient : MarkedProductReport
  /-- Actual next starting-target power. -/
  power : ModularProduct
  /-- Actual next inverse triangular phase. -/
  chirp : ModularProduct
  /-- Actual next inverse geometric step. -/
  step : ModularProduct

/-- Weighted actual coefficients and their complete primitive work. -/
structure GeometricWeightReport where
  /-- Original weighted value/base pairs in ascending coefficient order. -/
  words : List MarkedWord
  /-- Every coefficient visit and its actually computed phases. -/
  frames : List GeometricWeightFrame
  /-- All modular products, phase updates and source decisions. -/
  clock : ℕ

/-- Weight original physical coefficients by computed phase words.
All phase updates, including unused final states, are paid. -/
def geometricWeightRunBits (modulus start ratio power chirp step : List Bool) :
    List MarkedWord→GeometricWeightReport
  | [] => ⟨[],[],3⟩
  | coefficient::coefficients =>
    let factor := modMulBits power chirp modulus
    let weighted := markedMulBits modulus coefficient (scalarWord factor.division.remainder)
    let nextPower := modMulBits power start modulus
    let nextChirp := modMulBits chirp step modulus
    let nextStep := modMulBits step ratio modulus
    let child := geometricWeightRunBits modulus start ratio nextPower.division.remainder
      nextChirp.division.remainder nextStep.division.remainder coefficients
    ⟨weighted.word::child.words,⟨factor,weighted,nextPower,nextChirp,nextStep⟩::child.frames,
      factor.clock+weighted.clock+nextPower.clock+nextChirp.clock+nextStep.clock+child.clock+14⟩

/-- Actual coefficient weighting preserves the ORIGINAL marked
coefficient channel: neither starting target nor geometric ratio is
differentiated. Their phases are frozen scalar multipliers. -/
theorem geometricWeightRunBits_exact (modulus start ratio power chirp step : List Bool)
    (coefficients : List MarkedWord) (i : ℕ) (c : ℕ→(ZMod (bitValue modulus))[ε])
    (hp : (bitValue power : ZMod (bitValue modulus))=(bitValue start : ZMod (bitValue modulus))^i)
    (hc : (bitValue chirp : ZMod (bitValue modulus))=(bitValue ratio : ZMod (bitValue modulus))^triangular i)
    (hs : (bitValue step : ZMod (bitValue modulus))=(bitValue ratio : ZMod (bitValue modulus))^i)
    (hcoeff : coefficients.map (fun word => word.interpret modulus)=
      (List.range coefficients.length).map (fun k => c (i+k))) :
    (geometricWeightRunBits modulus start ratio power chirp step coefficients).words.map
      (fun word => word.interpret modulus)=
      (List.range coefficients.length).map
        (fun k => c (i+k)*scalarPhase ((bitValue start : ZMod (bitValue modulus))^(i+k)*
          (bitValue ratio : ZMod (bitValue modulus))^triangular (i+k))) := by
  induction coefficients generalizing power chirp step i with
  | nil => rfl
  | cons coefficient coefficients ih =>
    have hv := hcoeff
    rw [List.map_cons,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map] at hv
    have hhead : coefficient.interpret modulus=c i := by
      simpa only [Nat.add_zero] using (List.cons.inj hv).1
    have htail : coefficients.map (fun word => word.interpret modulus)=
        (List.range coefficients.length).map (fun k => c (i+1+k)) := by
      simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using (List.cons.inj hv).2
    let factor := modMulBits power chirp modulus
    let weighted := markedMulBits modulus coefficient (scalarWord factor.division.remainder)
    let nextPower := modMulBits power start modulus
    let nextChirp := modMulBits chirp step modulus
    let nextStep := modMulBits step ratio modulus
    have hnp : (bitValue nextPower.division.remainder : ZMod (bitValue modulus))=
        (bitValue start : ZMod (bitValue modulus))^(i+1) := by
      rw [modular_product_value,hp,pow_succ]
    have hnc : (bitValue nextChirp.division.remainder : ZMod (bitValue modulus))=
        (bitValue ratio : ZMod (bitValue modulus))^triangular (i+1) := by
      rw [modular_product_value,hc,hs,triangular,pow_add]
    have hns : (bitValue nextStep.division.remainder : ZMod (bitValue modulus))=
        (bitValue ratio : ZMod (bitValue modulus))^(i+1) := by
      rw [modular_product_value,hs,pow_succ]
    have hw : weighted.word.interpret modulus=c i*scalarPhase
        ((bitValue start : ZMod (bitValue modulus))^i*
          (bitValue ratio : ZMod (bitValue modulus))^triangular i) := by
      change (markedMulBits modulus coefficient (scalarWord factor.division.remainder)).word.interpret modulus=_
      rw [markedMulBits_value,hhead,scalarWord_value,modular_product_value,hp,hc]
    have ht := ih nextPower.division.remainder nextChirp.division.remainder nextStep.division.remainder
      (i+1) hnp hnc hns htail
    rw [geometricWeightRunBits]
    dsimp only
    change weighted.word.interpret modulus::
      (geometricWeightRunBits modulus start ratio nextPower.division.remainder
        nextChirp.division.remainder nextStep.division.remainder coefficients).words.map _=_
    rw [hw,ht,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro k _
    have hi : i+1+k=i+(k+1) := by omega
    simp only [Function.comp_def,Nat.succ_eq_add_one,hi]

/-- The complete actual original weighting walk has a linear-in-count
quadratic primitive bit clock and exact modulus-width output pairs. -/
theorem geometricWeightRunBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (start ratio power chirp step : List Bool) (coefficients : List MarkedWord) (W : ℕ)
    (hm : modulus.length≤W) (hstart : start.length≤W) (hratio : ratio.length≤W)
    (hp : power.length≤W) (hc : chirp.length≤W) (hs : step.length≤W)
    (hcoeff : ∀ word∈coefficients, word.Bounded W) :
    (geometricWeightRunBits modulus start ratio power chirp step coefficients).clock≤
      (coefficients.length+1)*(2000*(W+1)^2) ∧
    (geometricWeightRunBits modulus start ratio power chirp step coefficients).words.length=coefficients.length ∧
    (geometricWeightRunBits modulus start ratio power chirp step coefficients).frames.length=coefficients.length ∧
    ∀ word∈(geometricWeightRunBits modulus start ratio power chirp step coefficients).words,
      word.scalar.length=modulus.length ∧ word.marked.length=modulus.length := by
  induction coefficients generalizing power chirp step with
  | nil =>
    refine ⟨?_,rfl,rfl,?_⟩
    · simp only [geometricWeightRunBits,List.length_nil,Nat.zero_add,Nat.one_mul]
      nlinarith only [Nat.zero_le W]
    · intro word hw
      cases hw
  | cons coefficient coefficients ih =>
    let factor := modMulBits power chirp modulus
    let weighted := markedMulBits modulus coefficient (scalarWord factor.division.remainder)
    let nextPower := modMulBits power start modulus
    let nextChirp := modMulBits chirp step modulus
    let nextStep := modMulBits step ratio modulus
    have hf := bounded_modMulBits hp hc hm
    have hfw : (scalarWord factor.division.remainder).Bounded W :=
      ⟨(modMulBits_width hN).le.trans hm,Nat.zero_le _⟩
    have hw := markedMulBits_cost_width hN coefficient (scalarWord factor.division.remainder) W hm
      (hcoeff coefficient List.mem_cons_self) hfw
    have hnp := bounded_modMulBits hp hstart hm
    have hnc := bounded_modMulBits hc hs hm
    have hns := bounded_modMulBits hs hratio hm
    have hpw : nextPower.division.remainder.length≤W := (modMulBits_width hN).le.trans hm
    have hcw : nextChirp.division.remainder.length≤W := (modMulBits_width hN).le.trans hm
    have hsw : nextStep.division.remainder.length≤W := (modMulBits_width hN).le.trans hm
    have ht := ih nextPower.division.remainder nextChirp.division.remainder nextStep.division.remainder
      hpw hcw hsw (fun word hw => hcoeff word (List.mem_cons_of_mem coefficient hw))
    have hframe : factor.clock+weighted.clock+nextPower.clock+nextChirp.clock+nextStep.clock+14≤
        2000*(W+1)^2 := by
      dsimp only [factor,weighted,nextPower,nextChirp,nextStep]
      nlinarith only [hf,hw.1,hnp,hnc,hns,Nat.zero_le W]
    rw [geometricWeightRunBits]
    dsimp only
    refine ⟨?_,?_,?_,?_⟩
    · change factor.clock+weighted.clock+nextPower.clock+nextChirp.clock+nextStep.clock+
        (geometricWeightRunBits modulus start ratio nextPower.division.remainder nextChirp.division.remainder
          nextStep.division.remainder coefficients).clock+14≤_
      have hclock := ht.1
      simp only [List.length_cons]
      calc
        _ ≤ 2000*(W+1)^2+(coefficients.length+1)*(2000*(W+1)^2) := by omega
        _ = (coefficients.length+1+1)*(2000*(W+1)^2) := by ring
    · change (geometricWeightRunBits modulus start ratio nextPower.division.remainder nextChirp.division.remainder
        nextStep.division.remainder coefficients).words.length+1=coefficients.length+1
      rw [ht.2.1]
    · change (geometricWeightRunBits modulus start ratio nextPower.division.remainder nextChirp.division.remainder
        nextStep.division.remainder coefficients).frames.length+1=coefficients.length+1
      rw [ht.2.2.1]
    · intro word hword
      rcases List.mem_cons.mp hword with hsame|htail
      · subst word
        exact ⟨hw.2.1,hw.2.2.1⟩
      · exact ht.2.2.2 word htail

/-- Actual scalar coefficient freezing and a paid final zero slot. -/
structure FrozenTargetReport where
  /-- Each scalar coefficient with zero mark, then the zero top coefficient. -/
  words : List MarkedWord
  /-- Every source cell and pair/list construction, including the final slot. -/
  clock : ℕ

/-- Pad the derivative to the SAME degree bound as the value polynomial,
using the source's already normalized zero word. -/
def freezeTargetBits (zero : List Bool) : List (List Bool)→FrozenTargetReport
  | [] => ⟨[scalarWord zero],4⟩
  | word::words =>
    let child := freezeTargetBits zero words
    ⟨scalarWord word::child.words,child.clock+4⟩

/-- Exact scalar-freezing count and clock without any width premise. -/
theorem freezeTargetBits_counts (zero : List Bool) (words : List (List Bool)) :
    (freezeTargetBits zero words).clock=4*(words.length+1) ∧
    (freezeTargetBits zero words).words.length=words.length+1 := by
  induction words with
  | nil => exact ⟨rfl,rfl⟩
  | cons word words ih =>
    rw [freezeTargetBits]
    dsimp only
    exact ⟨by rw [ih.1,List.length_cons]; ring,by rw [List.length_cons,ih.2,List.length_cons]⟩

/-- Freezing retains every supplied scalar and adds only the literal
computed zero top slot. -/
theorem freezeTargetBits_values (modulus zero : List Bool) (words : List (List Bool)) :
    (freezeTargetBits zero words).words.map (fun word => word.interpret modulus)=
      words.map (fun word => scalarPhase (bitValue word : ZMod (bitValue modulus)))++
        [scalarPhase (bitValue zero : ZMod (bitValue modulus))] := by
  induction words with
  | nil => simp only [freezeTargetBits,List.map_cons,List.map_nil,scalarWord_value,List.nil_append]
  | cons word words ih =>
    simp only [freezeTargetBits,List.map_cons,scalarWord_value,ih,List.cons_append]

/-- Scalar freezing has exact counts, bounded words and linear work. -/
theorem freezeTargetBits_cost_width (zero : List Bool) (words : List (List Bool)) (W : ℕ)
    (hz : zero.length≤W) (hw : ∀ word∈words, word.length≤W) :
    (freezeTargetBits zero words).clock=4*(words.length+1) ∧
    (freezeTargetBits zero words).words.length=words.length+1 ∧
    ∀ word∈(freezeTargetBits zero words).words, word.Bounded W := by
  induction words with
  | nil =>
    refine ⟨rfl,rfl,?_⟩
    intro word hword
    rcases List.mem_singleton.mp hword with rfl
    exact ⟨hz,Nat.zero_le _⟩
  | cons word words ih =>
    have ht := ih (fun word hw' => hw word (List.mem_cons_of_mem _ hw'))
    rw [freezeTargetBits]
    dsimp only
    refine ⟨by rw [ht.1,List.length_cons]; ring,by rw [List.length_cons,ht.2.1,List.length_cons],?_⟩
    intro value hvalue
    rcases List.mem_cons.mp hvalue with hsame|htail
    · subst value
      exact ⟨hw word List.mem_cons_self,Nat.zero_le _⟩
    · exact ht.2.2 value htail

/-- Actual coefficient-list reversal and its reference/cell clock. -/
structure ReversedCoefficientReport where
  /-- Actual reversed list; residue bit words are retained by reference. -/
  words : List MarkedWord
  /-- Every list read, pair reference and new list cell. -/
  clock : ℕ

/-- Reverse computed coefficients structurally, without a native index. -/
def reverseCoefficientLoopBits : List MarkedWord→List MarkedWord→ReversedCoefficientReport
  | [],acc => ⟨acc,2⟩
  | word::words,acc =>
    let child := reverseCoefficientLoopBits words (word::acc)
    ⟨child.words,child.clock+5⟩

/-- Actual reversal preserves every word and has a linear complete
reference/cell clock, including its terminal decision. -/
theorem reverseCoefficientLoopBits_exact (words acc : List MarkedWord) :
    (reverseCoefficientLoopBits words acc).words=words.reverse++acc ∧
    (reverseCoefficientLoopBits words acc).clock=5*words.length+2 := by
  induction words generalizing acc with
  | nil => simp only [reverseCoefficientLoopBits,List.reverse_nil,List.nil_append,List.length_nil,
      Nat.mul_zero,Nat.zero_add,and_self]
  | cons word words ih =>
    have ht := ih (word::acc)
    rw [reverseCoefficientLoopBits]
    dsimp only
    refine ⟨?_,?_⟩
    · rw [ht.1,List.reverse_cons,List.append_assoc,List.singleton_append]
    · rw [ht.2,List.length_cons]; ring

/-- The original source report is retained on both constructor branches. -/
theorem threeChannelCoefficientBits_source (modulus alpha degree : List Bool) :
    (threeChannelCoefficientBits modulus alpha degree).source=markedGeometricCoefficientBits modulus alpha degree := by
  rw [threeChannelCoefficientBits]
  split <;> rfl

/-- The actual source constructs the original short block's scalar
base power; it is never supplied as a separate parameter. -/
theorem constructed_step_word_value {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha degree : List Bool) :
    (bitValue (threeChannelCoefficientBits modulus alpha degree).source.initialization.power.scalar :
      ZMod (bitValue modulus))=(bitValue alpha : ZMod (bitValue modulus))^bitValue degree := by
  rw [threeChannelCoefficientBits_source]
  let one := divideBits [true] modulus
  let zero := divideBits [] modulus
  let initial : MarkedWord := ⟨one.remainder,zero.remainder⟩
  let base : MarkedWord := ⟨alpha,alpha⟩
  have hone : initial.interpret modulus=1 := initialMarkedWord_value modulus
  have hp : initial.interpret modulus=base.interpret modulus^0 := by rw [hone,pow_zero]
  have hc : initial.interpret modulus=(SemiprimeGeometricRows.rowPolynomial (base.interpret modulus) 0).coeff 0 := by
    simpa only [SemiprimeGeometricRows.rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,
      Finset.range_zero,Finset.prod_empty,coeff_one_zero] using hone
  have hi := markedInitLoop_exact hN base initial initial degree 0 (initialMarkedWord_canonical hN) hp hc
  have hh := congrArg (fun z : (ZMod (bitValue modulus))[ε] => fst z) hi.1
  change (bitValue (markedGeometricCoefficientBits modulus alpha degree).initialization.power.scalar :
    ZMod (bitValue modulus))=fst (base.interpret modulus^(0+bitValue degree)) at hh
  have hb : base.interpret modulus=markedBase (bitValue alpha : ZMod (bitValue modulus)) := rfl
  simpa only [hb,Nat.zero_add,(markedBase_power _ _).1] using hh

/-- A supplied MATHEMATICAL unit identifies the computed scalar
inverse and gate. It is absent from executable arguments. -/
theorem scalar_inverse_word_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (word : List Bool) (u : (ZMod (bitValue modulus))ˣ)
    (hu : (bitValue word : ZMod (bitValue modulus))=(u : ZMod (bitValue modulus))) :
    (isOneBits (inverseBits modulus word).gcd).value=true ∧
    (bitValue (inverseBits modulus word).coefficient : ZMod (bitValue modulus))=
      ((u⁻¹ : (ZMod (bitValue modulus))ˣ) : ZMod (bitValue modulus)) := by
  have hunit : IsUnit (bitValue word : ZMod (bitValue modulus)) := by rw [hu]; exact u.isUnit
  have hg : (bitValue modulus).gcd (bitValue word)=1 :=
    ((ZMod.isUnit_iff_coprime _ _).mp hunit).symm
  have hinverse := inverseBits_correct hN word
  rw [hg,Nat.cast_one,hu] at hinverse
  refine ⟨(isOneBits_correct _).mpr (by rw [inverseBits_gcd hN,hg]),?_⟩
  calc
    _ = (bitValue (inverseBits modulus word).coefficient : ZMod (bitValue modulus))*
        ((u : ZMod (bitValue modulus))*((u⁻¹ : (ZMod (bitValue modulus))ˣ) : ZMod (bitValue modulus))) := by
      rw [u.mul_inv,mul_one]
    _ = _ := by rw [←mul_assoc,hinverse,one_mul]

/-- Every actual input needed by the three shared convolutions. -/
structure GeometricEvaluationInputs where
  /-- Paid original value/base coefficient weighting. -/
  valueBase : GeometricWeightReport
  /-- Paid scalar derivative freezing and degree padding. -/
  frozenTarget : FrozenTargetReport
  /-- Paid target-derivative coefficient weighting. -/
  target : GeometricWeightReport
  /-- Actual positive triangular kernel shared by all three channels. -/
  kernel : GeometricKernelReport
  /-- Actual inverse triangular phases for the returned evaluation slots. -/
  phase : GeometricKernelReport
  /-- Actual reversed original value/base weighted coefficients. -/
  reversedValueBase : ReversedCoefficientReport
  /-- Actual reversed weighted derivative coefficients. -/
  reversedTarget : ReversedCoefficientReport

/-- Source, actual scalar inverse/gate, count construction and inputs. -/
structure GeometricEvaluationPreparationReport where
  /-- Complete original three-channel coefficient source. -/
  source : ThreeChannelCoefficientReport
  /-- Computed scalar inverse if the coefficient source accepts. -/
  inverse : Option InverseBitsReport
  /-- Actual scalar GCD-one check if the source accepts. -/
  gate : Option OneBitsReport
  /-- Actual degree plus evaluation-count Boolean sum. -/
  kernelCount : Option BitReport
  /-- All actual convolution inputs when both source and ratio gate accept. -/
  inputs : Option GeometricEvaluationInputs
  /-- Entire source, normalization, inverse, phase and weighting work. -/
  clock : ℕ

/-- Construct every original convolution input from Boolean words.
The ratio is the checked inverse of the source's COMPUTED alpha^degree.
No scalar power, triangular kernel, inverse or marked input is advice. -/
def geometricEvaluationPreparationBits (modulus alpha degree start evaluations : List Bool) :
    GeometricEvaluationPreparationReport :=
  let source := threeChannelCoefficientBits modulus alpha degree
  match source.coefficients with
  | none => ⟨source,none,none,none,none,source.clock+4⟩
  | some (coefficients,targetCoefficients) =>
    let step := source.source.initialization.power.scalar
    let inverse := inverseBits modulus step
    let gate := isOneBits inverse.gcd
    if gate.value=true then
      let count := addBits degree evaluations false
      let one := source.source.one.remainder
      let zero := source.source.zero.remainder
      let valueBase := geometricWeightRunBits modulus start step one one one coefficients
      let frozenTarget := freezeTargetBits zero targetCoefficients
      let target := geometricWeightRunBits modulus start step one one one frozenTarget.words
      let kernel := geometricKernelLoopBits modulus inverse.coefficient one one count.bits
      let phase := geometricKernelLoopBits modulus step one one evaluations
      let reversedValueBase := reverseCoefficientLoopBits valueBase.words []
      let reversedTarget := reverseCoefficientLoopBits target.words []
      let inputs : GeometricEvaluationInputs :=
        ⟨valueBase,frozenTarget,target,kernel,phase,reversedValueBase,reversedTarget⟩
      ⟨source,some inverse,some gate,some count,some inputs,
        source.clock+inverse.clock+gate.clock+bitCost count+valueBase.clock+frozenTarget.clock+
          target.clock+kernel.clock+phase.clock+reversedValueBase.clock+reversedTarget.clock+26⟩
    else ⟨source,some inverse,some gate,none,none,source.clock+inverse.clock+gate.clock+9⟩

/-- The constructed short-block step has the modulus's exact width,
on accepted and rejected sources alike. -/
theorem constructed_step_word_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha degree : List Bool) :
    (threeChannelCoefficientBits modulus alpha degree).source.initialization.power.scalar.length=modulus.length := by
  rw [threeChannelCoefficientBits_source]
  let initial : MarkedWord :=
    ⟨(divideBits [true] modulus).remainder,(divideBits [] modulus).remainder⟩
  have hw : initial.scalar.length=modulus.length ∧ initial.marked.length=modulus.length :=
    ⟨(divideBits_widths (xs:=[true]) hN).1,(divideBits_widths (xs:=[]) hN).1⟩
  exact (markedInitLoop_width_exact hN ⟨alpha,alpha⟩ initial initial degree hw hw).1.1

/-- All ACTUAL original coefficient weights, the shared positive
kernel and returned-slot inverse phases are correct. Only mathematical
proof arguments mention a unit, polynomial, index or exponent. -/
theorem geometricEvaluationPreparationBits_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha degree start evaluations : List Bool) (a : (ZMod (bitValue modulus))ˣ)
    (ha : (bitValue alpha : ZMod (bitValue modulus))=(a : ZMod (bitValue modulus)))
    (hgaps : ∀ j, 0<j→j≤bitValue degree→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1)) :
    ∃ inputs, (geometricEvaluationPreparationBits modulus alpha degree start evaluations).inputs=some inputs ∧
      inputs.valueBase.words.map (fun word => word.interpret modulus)=
        (List.range (bitValue degree+1)).map (fun i =>
          (SemiprimeGeometricRows.rowPolynomial (markedBase (bitValue alpha : ZMod (bitValue modulus)))
            (bitValue degree)).coeff i*
          scalarPhase ((bitValue start : ZMod (bitValue modulus))^i*
            ((bitValue alpha : ZMod (bitValue modulus))^bitValue degree)^triangular i)) ∧
      inputs.target.words.map (fun word => word.interpret modulus)=
        (List.range (bitValue degree+1)).map (fun i =>
          scalarPhase ((SemiprimeGeometricRows.rowPolynomial (bitValue alpha : ZMod (bitValue modulus))
            (bitValue degree)).derivative.coeff i)*
          scalarPhase ((bitValue start : ZMod (bitValue modulus))^i*
            ((bitValue alpha : ZMod (bitValue modulus))^bitValue degree)^triangular i)) ∧
      inputs.kernel.words.map (fun word => (bitValue word : ZMod (bitValue modulus)))=
        (List.range (bitValue degree+bitValue evaluations)).map (fun i =>
          (((a^bitValue degree)⁻¹ : (ZMod (bitValue modulus))ˣ) : ZMod (bitValue modulus))^triangular i) ∧
      inputs.phase.words.map (fun word => (bitValue word : ZMod (bitValue modulus)))=
        (List.range (bitValue evaluations)).map (fun i =>
          ((bitValue alpha : ZMod (bitValue modulus))^bitValue degree)^triangular i) ∧
      inputs.reversedValueBase.words=inputs.valueBase.words.reverse ∧
      inputs.reversedTarget.words=inputs.target.words.reverse := by
  let source := threeChannelCoefficientBits modulus alpha degree
  have hunit : IsUnit (bitValue alpha : ZMod (bitValue modulus)) := by rw [ha]; exact a.isUnit
  obtain ⟨coefficients,targetCoefficients,hout,he,hd⟩ :=
    threeChannelCoefficientBits_exact hN alpha degree hunit hgaps
  have hlen : coefficients.length=bitValue degree+1 := by
    have hh := congrArg List.length he
    simpa only [List.length_map,List.length_range] using hh
  have htargetLength : targetCoefficients.length=bitValue degree := by
    have hh := congrArg List.length hd
    simpa only [List.length_map,List.length_range] using hh
  have hdual : coefficients.map (fun word => word.interpret modulus)=
      (List.range coefficients.length).map (fun i =>
        (SemiprimeGeometricRows.rowPolynomial (markedBase (bitValue alpha : ZMod (bitValue modulus)))
          (bitValue degree)).coeff i) := by
    have hh := congrArg (List.map (fun pair : ZMod (bitValue modulus)×ZMod (bitValue modulus) =>
      (⟨pair.1,pair.2⟩ : (ZMod (bitValue modulus))[ε]))) he
    rw [List.map_map,List.map_map] at hh
    change coefficients.map (fun word => word.interpret modulus)=
      (List.range (bitValue degree+1)).map (fun i =>
        (⟨(SemiprimeGeometricRows.rowPolynomial (bitValue alpha : ZMod (bitValue modulus))
          (bitValue degree)).coeff i,
          (SemiprimeSharedIntervalJet.babyBasePolynomial (bitValue alpha : ZMod (bitValue modulus))
            (bitValue degree)).coeff i⟩ : (ZMod (bitValue modulus))[ε])) at hh
    rw [hlen]
    apply hh.trans
    apply List.map_congr_left
    intro i _
    apply TrivSqZeroExt.ext
    · simp only [fst_mk,marked_coeff_value]
    · simp only [snd_mk,marked_coeff_base]
  let one := source.source.one.remainder
  let zero := source.source.zero.remainder
  let step := source.source.initialization.power.scalar
  have hone : (bitValue one : ZMod (bitValue modulus))=1 := by
    change (bitValue source.source.one.remainder : ZMod (bitValue modulus))=1
    rw [threeChannelCoefficientBits_source]
    exact reduced_one_value modulus
  have hzero : (bitValue zero : ZMod (bitValue modulus))=0 := by
    change (bitValue source.source.zero.remainder : ZMod (bitValue modulus))=0
    rw [threeChannelCoefficientBits_source]
    change (bitValue (divideBits [] modulus).remainder : ZMod (bitValue modulus))=0
    rw [(divideBits_correct [] modulus).2]
    simp only [bitValue,Nat.zero_mod,Nat.cast_zero]
  have hstep : (bitValue step : ZMod (bitValue modulus))=
      (bitValue alpha : ZMod (bitValue modulus))^bitValue degree := constructed_step_word_value hN alpha degree
  have hstepUnit : (bitValue step : ZMod (bitValue modulus))=
      ((a^bitValue degree : (ZMod (bitValue modulus))ˣ) : ZMod (bitValue modulus)) := by
    rw [hstep,ha,Units.val_pow_eq_pow_val]
  have hinverse := scalar_inverse_word_exact hN step (a^bitValue degree) hstepUnit
  let inverse := inverseBits modulus step
  let gate := isOneBits inverse.gcd
  let count := addBits degree evaluations false
  have hq : (bitValue inverse.coefficient : ZMod (bitValue modulus))=
      (((a^bitValue degree)⁻¹ : (ZMod (bitValue modulus))ˣ) : ZMod (bitValue modulus)) := hinverse.2
  have hcount : bitValue count.bits=bitValue degree+bitValue evaluations := by
    have hh := addBits_correct degree evaluations false
    simpa only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] using hh
  have hstartPower : (bitValue one : ZMod (bitValue modulus))=(bitValue start : ZMod (bitValue modulus))^0 := by
    rw [hone,pow_zero]
  have hstartChirp : (bitValue one : ZMod (bitValue modulus))=
      (bitValue step : ZMod (bitValue modulus))^triangular 0 := by rw [hone,triangular,pow_zero]
  have hstartStep : (bitValue one : ZMod (bitValue modulus))=(bitValue step : ZMod (bitValue modulus))^0 := by
    rw [hone,pow_zero]
  have hv := geometricWeightRunBits_exact modulus start step one one one coefficients 0
    (fun i => (SemiprimeGeometricRows.rowPolynomial (markedBase (bitValue alpha : ZMod (bitValue modulus)))
      (bitValue degree)).coeff i) hstartPower hstartChirp hstartStep
    (by simpa only [Nat.zero_add] using hdual)
  let frozenTarget := freezeTargetBits zero targetCoefficients
  have hDzero : (SemiprimeGeometricRows.rowPolynomial (bitValue alpha : ZMod (bitValue modulus))
      (bitValue degree)).derivative.coeff (bitValue degree)=0 := by
    rw [coeff_derivative,natDegree_le_iff_coeff_eq_zero.mp
      (original_row_degree_le (bitValue alpha : ZMod (bitValue modulus)) (bitValue degree))
      (bitValue degree+1) (by omega),zero_mul]
  have hf : frozenTarget.words.map (fun word => word.interpret modulus)=
      (List.range frozenTarget.words.length).map (fun i =>
        scalarPhase ((SemiprimeGeometricRows.rowPolynomial (bitValue alpha : ZMod (bitValue modulus))
          (bitValue degree)).derivative.coeff i)) := by
    have hh := freezeTargetBits_values modulus zero targetCoefficients
    have hfl : frozenTarget.words.length=bitValue degree+1 := by
      exact (freezeTargetBits_counts zero targetCoefficients).2.trans (by rw [htargetLength])
    rw [hfl,List.range_succ,List.map_append,List.map_cons,List.map_nil,hDzero]
    have hmap : targetCoefficients.map (fun word => scalarPhase (bitValue word : ZMod (bitValue modulus)))=
        (List.range (bitValue degree)).map (fun i => scalarPhase
          ((SemiprimeGeometricRows.rowPolynomial (bitValue alpha : ZMod (bitValue modulus))
            (bitValue degree)).derivative.coeff i)) := by
      have hh' := congrArg (List.map (fun x : ZMod (bitValue modulus) => scalarPhase x)) hd
      simpa only [List.map_map,Function.comp_def] using hh'
    exact hh.trans (by rw [hmap,hzero])
  have ht := geometricWeightRunBits_exact modulus start step one one one frozenTarget.words 0
    (fun i => scalarPhase ((SemiprimeGeometricRows.rowPolynomial (bitValue alpha : ZMod (bitValue modulus))
      (bitValue degree)).derivative.coeff i)) hstartPower hstartChirp hstartStep
    (by simpa only [Nat.zero_add] using hf)
  have hfLength : frozenTarget.words.length=bitValue degree+1 := by
    exact (freezeTargetBits_counts zero targetCoefficients).2.trans (by rw [htargetLength])
  have hk := geometricKernelLoopBits_exact modulus inverse.coefficient one one count.bits 0
    (by rw [hone,triangular,pow_zero]) (by rw [hone,pow_zero])
  have hs := geometricKernelLoopBits_exact modulus step one one evaluations 0 hstartChirp hstartStep
  let valueBase := geometricWeightRunBits modulus start step one one one coefficients
  let target := geometricWeightRunBits modulus start step one one one frozenTarget.words
  let kernel := geometricKernelLoopBits modulus inverse.coefficient one one count.bits
  let phase := geometricKernelLoopBits modulus step one one evaluations
  let reversedValueBase := reverseCoefficientLoopBits valueBase.words []
  let reversedTarget := reverseCoefficientLoopBits target.words []
  let inputs : GeometricEvaluationInputs :=
    ⟨valueBase,frozenTarget,target,kernel,phase,reversedValueBase,reversedTarget⟩
  refine ⟨inputs,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [geometricEvaluationPreparationBits]
    dsimp only
    rw [hout]
    dsimp only
    have hgate : (isOneBits (inverseBits modulus
      (threeChannelCoefficientBits modulus alpha degree).source.initialization.power.scalar).gcd).value=true := hinverse.1
    rw [if_pos hgate]
  · simpa only [Nat.zero_add,hlen,hstep] using hv
  · simpa only [Nat.zero_add,hfLength,hstep] using ht
  · simpa only [Nat.zero_add,hcount,hq] using hk.2.2
  · simpa only [Nat.zero_add,hstep] using hs.2.2
  · simpa only [List.append_nil] using (reverseCoefficientLoopBits_exact valueBase.words []).1
  · simpa only [List.append_nil] using (reverseCoefficientLoopBits_exact target.words []).1

/-- Entire ACTUAL convolution preparation has a linear-in-source
primitive bit clock, including all rejected gates. Every accepted word
has the fixed modulus width and every original slot count is exact. -/
theorem geometricEvaluationPreparationBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha degree start evaluations : List Bool) (W : ℕ) (hW : 1≤W)
    (hm : modulus.length≤W) (ha : alpha.length≤W) (hd : degree.length≤W)
    (hx : start.length≤W) (hJ : evaluations.length≤W) :
    (geometricEvaluationPreparationBits modulus alpha degree start evaluations).clock≤
      (bitValue degree+bitValue evaluations+1)*(40000*(W+2)^3) ∧
    ∀ inputs, (geometricEvaluationPreparationBits modulus alpha degree start evaluations).inputs=some inputs→
      inputs.valueBase.words.length=bitValue degree+1 ∧
      inputs.target.words.length=bitValue degree+1 ∧
      inputs.kernel.words.length=bitValue degree+bitValue evaluations ∧
      inputs.phase.words.length=bitValue evaluations ∧
      (∀ word∈inputs.valueBase.words, word.scalar.length=modulus.length ∧ word.marked.length=modulus.length) ∧
      (∀ word∈inputs.target.words, word.scalar.length=modulus.length ∧ word.marked.length=modulus.length) ∧
      (∀ word∈inputs.kernel.words, word.length=modulus.length) ∧
      (∀ word∈inputs.phase.words, word.length=modulus.length) := by
  let source := threeChannelCoefficientBits modulus alpha degree
  let B := bitValue degree+bitValue evaluations+1
  let Q := (W+2)^3
  have hB : 1≤B := by dsimp only [B]; omega
  have hQ : 1≤Q := by
    have hh : 0<Q := by dsimp only [Q]; positivity
    omega
  have hBQ : 1≤B*Q := by simpa only [Nat.one_mul] using Nat.mul_le_mul hB hQ
  have hcube : (W+1)^3≤Q := by dsimp only [Q]; gcongr; omega
  have hsquare : (W+1)^2≤Q := by
    have hh : (W+1)^2≤(W+1)^3 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
    exact hh.trans hcube
  have hsquare' : (W+2)^2≤Q := by
    dsimp only [Q]
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hlinear : W+1≤Q := by
    dsimp only [Q]
    nlinarith only [Nat.zero_le W,Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have hdegree : bitValue degree+1≤B := by dsimp only [B]; omega
  have hevaluations : bitValue evaluations+1≤B := by dsimp only [B]; omega
  have hsource := threeChannelCoefficientBits_cost_width hN alpha degree W hW hm ha hd
  have hsourceClock : source.clock≤B*(22000*Q) := hsource.1.trans
    (Nat.mul_le_mul hdegree (Nat.mul_le_mul_left 22000 hcube))
  have hone : source.source.one.remainder.length=modulus.length := by
    rw [threeChannelCoefficientBits_source]
    exact (divideBits_widths (xs:=[true]) hN).1
  have hzero : source.source.zero.remainder.length=modulus.length := by
    rw [threeChannelCoefficientBits_source]
    exact (divideBits_widths (xs:=[]) hN).1
  have hstep : source.source.initialization.power.scalar.length=modulus.length :=
    constructed_step_word_width hN alpha degree
  cases hout : source.coefficients with
  | none =>
    have hout' : (threeChannelCoefficientBits modulus alpha degree).coefficients=none := hout
    have hclock : (geometricEvaluationPreparationBits modulus alpha degree start evaluations).clock=source.clock+4 := by
      rw [geometricEvaluationPreparationBits]
      dsimp only
      rw [hout']
    refine ⟨?_,?_⟩
    · rw [hclock]
      change source.clock+4≤B*(40000*Q)
      nlinarith only [hsourceClock,hBQ]
    · intro inputs hi
      rw [geometricEvaluationPreparationBits] at hi
      dsimp only at hi
      rw [hout'] at hi
      cases hi
  | some pair =>
    rcases pair with ⟨coefficients,targetCoefficients⟩
    have hout' : (threeChannelCoefficientBits modulus alpha degree).coefficients=some (coefficients,targetCoefficients) := hout
    have hwSource := hsource.2 coefficients targetCoefficients hout
    let one := source.source.one.remainder
    let zero := source.source.zero.remainder
    let step := source.source.initialization.power.scalar
    let inverse := inverseBits modulus step
    let gate := isOneBits inverse.gcd
    have hinverseWidth := inverseBits_width hN step
    have hinverse := inverseBits_cost hN hm (hstep.le.trans hm)
    have hgate := isOneBits_cost (hinverseWidth.1.trans hm)
    have hiClock : inverse.clock≤B*(4000*Q) := by
      have hh : (inverseBits modulus step).clock≤4000*Q := hinverse.trans (Nat.mul_le_mul_left 4000 hcube)
      exact hh.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (4000*Q) hB)
    have hgClock : gate.clock≤B*(50*Q) := by
      have hh : (isOneBits (inverseBits modulus step).gcd).clock≤50*Q := by
        nlinarith only [hgate,hlinear,hQ]
      exact hh.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (50*Q) hB)
    by_cases hpass : gate.value=true
    · let count := addBits degree evaluations false
      let valueBase := geometricWeightRunBits modulus start step one one one coefficients
      let frozenTarget := freezeTargetBits zero targetCoefficients
      let target := geometricWeightRunBits modulus start step one one one frozenTarget.words
      let kernel := geometricKernelLoopBits modulus inverse.coefficient one one count.bits
      let phase := geometricKernelLoopBits modulus step one one evaluations
      let reversedValueBase := reverseCoefficientLoopBits valueBase.words []
      let reversedTarget := reverseCoefficientLoopBits target.words []
      have hcount : bitValue count.bits=bitValue degree+bitValue evaluations := by
        have hh := addBits_correct degree evaluations false
        simpa only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] using hh
      have hcountWidth : count.bits.length≤W+1 := (bounded_addBits hd hJ false).2
      have hcountCost := (bounded_addBits hd hJ false).1
      have hcc : ∀ word∈coefficients, word.Bounded W := by
        intro word hw
        exact ⟨(hwSource.2.2.1 word hw).1.le.trans hm,(hwSource.2.2.1 word hw).2.le.trans hm⟩
      have hv := geometricWeightRunBits_cost_width hN start step one one one coefficients W
        hm hx (hstep.le.trans hm) (hone.le.trans hm) (hone.le.trans hm) (hone.le.trans hm) hcc
      have hf := freezeTargetBits_cost_width zero targetCoefficients W (hzero.le.trans hm)
        (fun word hw => (hwSource.2.2.2 word hw).le.trans hm)
      have ht := geometricWeightRunBits_cost_width hN start step one one one frozenTarget.words W
        hm hx (hstep.le.trans hm) (hone.le.trans hm) (hone.le.trans hm) (hone.le.trans hm) hf.2.2
      have hk := geometricKernelLoopBits_cost_width hN (by omega : 1≤W+1)
        inverse.coefficient one one count.bits (hm.trans (by omega))
        ((hinverseWidth.2.trans hm).trans (by omega)) hone ((hone.le.trans hm).trans (by omega)) hcountWidth
      have hp := geometricKernelLoopBits_cost_width hN hW step one one evaluations hm
        (hstep.le.trans hm) hone (hone.le.trans hm) hJ
      have hrevv := reverseCoefficientLoopBits_exact valueBase.words []
      have hrevt := reverseCoefficientLoopBits_exact target.words []
      have hvl : valueBase.words.length=bitValue degree+1 := hv.2.1.trans hwSource.1
      have htl : target.words.length=bitValue degree+1 := ht.2.1.trans (hf.2.1.trans
        (by rw [hwSource.2.1]))
      have hvClock : valueBase.clock≤B*(4000*Q) := by
        apply hv.1.trans
        calc
          _ ≤ (2*B)*(2000*Q) := Nat.mul_le_mul
            (by rw [hwSource.1]; dsimp only [B]; omega) (Nat.mul_le_mul_left 2000 hsquare)
          _ = _ := by ring
      have htClock : target.clock≤B*(4000*Q) := by
        apply ht.1.trans
        calc
          _ ≤ (2*B)*(2000*Q) := Nat.mul_le_mul
            (by rw [hf.2.1,hwSource.2.1]; dsimp only [B]; omega) (Nat.mul_le_mul_left 2000 hsquare)
          _ = _ := by ring
      have hkClock : kernel.clock≤B*(400*Q) := by
        have hh := hk.1
        rw [hcount] at hh
        exact hh.trans (Nat.mul_le_mul_left B (Nat.mul_le_mul_left 400 hsquare'))
      have hpClock : phase.clock≤B*(400*Q) := hp.1.trans
        (Nat.mul_le_mul hevaluations (Nat.mul_le_mul_left 400 hsquare))
      have hfClock : frozenTarget.clock≤B*(4*Q) := by
        have hh : frozenTarget.clock=4*(bitValue degree+1) := by rw [hf.1,hwSource.2.1]
        rw [hh]
        have hprod := Nat.mul_le_mul hdegree hQ
        nlinarith only [hprod]
      have hrvClock : reversedValueBase.clock≤B*(7*Q) := by
        have hh : reversedValueBase.clock=5*(bitValue degree+1)+2 := by rw [hrevv.2,hvl]
        rw [hh]
        have hprod := Nat.mul_le_mul hdegree hQ
        nlinarith only [hprod,hBQ]
      have hrtClock : reversedTarget.clock≤B*(7*Q) := by
        have hh : reversedTarget.clock=5*(bitValue degree+1)+2 := by rw [hrevt.2,htl]
        rw [hh]
        have hprod := Nat.mul_le_mul hdegree hQ
        nlinarith only [hprod,hBQ]
      have hcClock : bitCost count≤B*(20*Q) := by
        have hh : bitCost count≤20*Q := by nlinarith only [hcountCost,hlinear,hQ]
        exact hh.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (20*Q) hB)
      have hpass' : (isOneBits (inverseBits modulus
          (threeChannelCoefficientBits modulus alpha degree).source.initialization.power.scalar).gcd).value=true := hpass
      have hclock : (geometricEvaluationPreparationBits modulus alpha degree start evaluations).clock=
          source.clock+inverse.clock+gate.clock+bitCost count+valueBase.clock+frozenTarget.clock+target.clock+
            kernel.clock+phase.clock+reversedValueBase.clock+reversedTarget.clock+26 := by
        rw [geometricEvaluationPreparationBits]
        dsimp only
        rw [hout']
        dsimp only
        rw [if_pos hpass']
      refine ⟨?_,?_⟩
      · rw [hclock]
        change _≤B*(40000*Q)
        nlinarith only [hsourceClock,hiClock,hgClock,hcClock,hvClock,hfClock,htClock,hkClock,hpClock,
          hrvClock,hrtClock,hBQ]
      · intro inputs hi
        rw [geometricEvaluationPreparationBits] at hi
        dsimp only at hi
        rw [hout'] at hi
        dsimp only at hi
        rw [if_pos hpass'] at hi
        cases hi
        exact ⟨hvl,htl,hk.2.2.2.1.trans hcount,hp.2.2.2.1,hv.2.2.2,ht.2.2.2,hk.2.2.2.2.2,hp.2.2.2.2.2⟩
    · have hpass' : ¬(isOneBits (inverseBits modulus
          (threeChannelCoefficientBits modulus alpha degree).source.initialization.power.scalar).gcd).value=true := hpass
      have hclock : (geometricEvaluationPreparationBits modulus alpha degree start evaluations).clock=
          source.clock+inverse.clock+gate.clock+9 := by
        rw [geometricEvaluationPreparationBits]
        dsimp only
        rw [hout']
        dsimp only
        rw [if_neg hpass']
      refine ⟨?_,?_⟩
      · rw [hclock]
        change _≤B*(40000*Q)
        nlinarith only [hsourceClock,hiClock,hgClock,hBQ]
      · intro inputs hi
        rw [geometricEvaluationPreparationBits] at hi
        dsimp only at hi
        rw [hout'] at hi
        dsimp only at hi
        rw [if_neg hpass'] at hi
        cases hi

/-- Proof-side restoration of the three convolution outputs to the
original absolute-index block jet. No detector factor is divided away. -/
noncomputable def blockConvolutionJet {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) (s J j : ℕ) : R×R×R :=
  let q := (alpha^s)⁻¹
  let P := SemiprimeGeometricRows.rowPolynomial (alpha : R) s
  let H := SemiprimeSharedIntervalJet.babyBasePolynomial (alpha : R) s
  let K := chirpKernelPolynomial q (s+J)
  let phase := (((q^triangular j)⁻¹ : Rˣ) : R)
  let v := (reversedChirpPolynomial q x P.coeff s*K).coeff (s+j)*phase
  let d := (reversedChirpPolynomial q x P.derivative.coeff s*K).coeff (s+j)*phase
  let b := (reversedChirpPolynomial q x H.coeff s*K).coeff (s+j)*phase
  let z := x*(q : R)^j
  let c := (alpha : R)^(j*s)
  let h := c^s
  (h*v,h*(q : R)^j*d,h*((j*s : ℕ)*(s : R)*v+b-((j*s : ℕ) : R)*z*d))

/-- Three shared-kernel convolutions and literal phase restoration
retain EXACTLY the original block product, target derivative and
absolute-index base derivative, including every zero block. -/
theorem blockConvolutionJet_exact {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) {s : ℕ} (hs : 0<s) (J : ℕ) {j : ℕ} (hj : j<J) :
    blockConvolutionJet alpha x s J j=SemiprimeSharedIntervalJet.blockJet (alpha : R) x (j*s) s := by
  have hu : ((alpha^s)⁻¹)^j=(alpha^(j*s))⁻¹ := by
    rw [inv_pow,←pow_mul,Nat.mul_comm s j]
  have hq : (((alpha^s)⁻¹ : Rˣ) : R)^j=(((alpha^(j*s))⁻¹ : Rˣ) : R) := by
    rw [←Units.val_pow_eq_pow_val,hu]
  have hz : SemiprimeSharedIntervalJet.normalizedPoint alpha x s j=
      x*((((alpha^s)⁻¹ : Rˣ) : R)^j) := by
    unfold SemiprimeSharedIntervalJet.normalizedPoint
    rw [←hq]
    ring
  have hvalues := original_three_channel_convolution (alpha : R) (alpha^s)⁻¹ x s J hj
  have hp := congrArg (fun v : R×R×R => v.1) hvalues
  have hd := congrArg (fun v : R×R×R => v.2.1) hvalues
  have hb := congrArg (fun v : R×R×R => v.2.2) hvalues
  dsimp only at hp hd hb
  rw [blockConvolutionJet]
  rw [hp,hd,hb]
  have hh := SemiprimeSharedIntervalJet.normalizedBlockJet_eq alpha x hs j
  unfold SemiprimeSharedIntervalJet.normalizedBlockJet at hh
  dsimp only at hh
  rw [hz,←hq] at hh
  exact hh

/-- The original interval has at most two-modulus many complete
two-modulus blocks. The final short tail stays a separate source. -/
theorem original_complete_block_count_le {m : ℕ} (hm : 4≤m) :
    SemiprimeSeedSumAcquisition.seedLength m/(2*m)≤2*m := by
  have hl := (SemiprimeSeedSumAcquisition.seedLength_bounds hm).2
  have hd := Nat.div_mul_le_self (SemiprimeSeedSumAcquisition.seedLength m) (2*m)
  nlinarith only [hl,hd,hm]

/-- At the ACTUAL public row modulus, all original convolution inputs
for one seed's complete blocks are constructed with a near-linear
primitive clock. Fast convolution, the final tail, public word production
and the varying-seed detector remain separate obligations. -/
theorem public_original_geometric_preparation {p q W : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q)) (g : (ZMod (p*q))ˣ)
    (hlong : SemiprimeLocalOrderRouting.LongData g (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (modulus alpha degree start evaluations : List Bool) (hmod : bitValue modulus=p*q)
    (halpha : (bitValue alpha : ZMod (p*q))=
      ((SemiprimeSeedSumAcquisition.seedBase
        (SemiprimeCentreFreeCover.projectedUnit g (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
        (SemiprimeEuclidRowBudget.publicRowModulus (p*q)) : (ZMod (p*q))ˣ) : ZMod (p*q)))
    (hdegree : bitValue degree=2*SemiprimeEuclidRowBudget.publicRowModulus (p*q))
    (hevaluations : bitValue evaluations=
      SemiprimeSeedSumAcquisition.seedLength (SemiprimeEuclidRowBudget.publicRowModulus (p*q))/
        (2*SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hW : 1≤W) (hm : modulus.length≤W) (ha : alpha.length≤W) (hd : degree.length≤W)
    (hx : start.length≤W) (hJ : evaluations.length≤W) :
    ∃ inputs, (geometricEvaluationPreparationBits modulus alpha degree start evaluations).inputs=some inputs ∧
      inputs.valueBase.words.length=2*SemiprimeEuclidRowBudget.publicRowModulus (p*q)+1 ∧
      inputs.target.words.length=2*SemiprimeEuclidRowBudget.publicRowModulus (p*q)+1 ∧
      inputs.kernel.words.length=2*SemiprimeEuclidRowBudget.publicRowModulus (p*q)+bitValue evaluations ∧
      inputs.phase.words.length=bitValue evaluations ∧
      (geometricEvaluationPreparationBits modulus alpha degree start evaluations).clock≤
        (8*SemiprimeLehmanCoverage.sixthWidth (p*q)+1)*(40000*(W+2)^3) := by
  have hN : 0<bitValue modulus := by rw [hmod]; exact Nat.mul_pos hp.pos hq.pos
  have hbounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds (Nat.mul_pos hp.pos hq.pos)
  have hm₄ : 4≤SemiprimeEuclidRowBudget.publicRowModulus (p*q) := hB.trans hbounds.1
  have hunit : IsUnit (bitValue alpha : ZMod (bitValue modulus)) := by
    rw [hmod,halpha]
    exact (SemiprimeSeedSumAcquisition.seedBase
      (SemiprimeCentreFreeCover.projectedUnit g (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))).isUnit
  have hgaps : ∀ j, 0<j→j≤bitValue degree→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1) := by
    intro j hj hjmax
    rw [hmod,halpha]
    apply SemiprimeSeedGeometricRecurrence.long_seedHalf_power_gaps_unit hp hq hm₄ g hlong j hj
    apply hjmax.trans
    rw [hdegree]
    exact two_modulus_block_le_half hm₄
  obtain ⟨a,haUnit⟩ := hunit
  obtain ⟨inputs,hout,_⟩ := geometricEvaluationPreparationBits_exact hN alpha degree start evaluations a haUnit.symm hgaps
  have hc := geometricEvaluationPreparationBits_cost_width hN alpha degree start evaluations W hW hm ha hd hx hJ
  have hw := hc.2 inputs hout
  refine ⟨inputs,hout,by rw [hdegree] at hw; exact hw.1,
    by rw [hdegree] at hw; exact hw.2.1,by rw [hdegree] at hw; exact hw.2.2.1,hw.2.2.2.1,?_⟩
  apply hc.1.trans
  apply Nat.mul_le_mul_right
  have hcount := original_complete_block_count_le hm₄
  rw [←hevaluations] at hcount
  rw [hdegree]
  omega

end RiemannGaussian.SemiprimeBitGeometricEvaluation
