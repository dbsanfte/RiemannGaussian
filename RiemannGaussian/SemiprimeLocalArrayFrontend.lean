/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeArrayOps
import RiemannGaussian.SemiprimeLocalPrefixHeight

/-!
# Executed local Taylor and multilinear frontend

Horner composition uses cached jet operations rather than coefficient advice or
an uncharged binomial supplier. The local evaluator is a depth-first traversal
with an explicit paid integer table callback at each leaf.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeLocalArrayFrontend
open scoped BigOperators
open Polynomial
open SemiprimeJetArray SemiprimeJetRecurrence SemiprimeJetArrayHeight
open SemiprimeArrayOps SemiprimeStreamingTensor

/-- Actual integer-valued local predicate callback and its reported work. -/
structure EntryReport where
  /-- Native integer table value. -/
  value : ℤ
  /-- Charged scalar/backend operations in the callback. -/
  arithmetic : ℕ
  /-- Charged callback reads. -/
  reads : ℕ

/-- Actual depth-first local interpolation. No truth-table list is an input. -/
def localEvaluate (J : ℕ) : (w : ℕ) → ((Fin w → Bool) → EntryReport) →
    (Fin w → Array ℚ) → InverseReport
  | 0, T, _ =>
      let entry := T Fin.elim0
      let out := scaleJet (oneJet J).coefficients (entry.value : ℚ) J
      ⟨out.coefficients, entry.arithmetic + out.arithmetic, entry.reads + out.reads⟩
  | w + 1, T, inputs =>
      let lo := localEvaluate J w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)
      let hi := localEvaluate J w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)
      let neg := scaleJet (inputs 0) (-1) J
      let no := addJet (oneJet J).coefficients neg.coefficients J
      let left := multiply no.coefficients lo.coefficients J
      let right := multiply (inputs 0) hi.coefficients J
      let out := addJet left.coefficients right.coefficients J
      ⟨out.coefficients, lo.arithmetic + hi.arithmetic + neg.arithmetic + no.arithmetic +
        left.arithmetic + right.arithmetic + out.arithmetic,
        lo.reads + hi.reads + neg.reads + no.reads + left.reads + right.reads + out.reads⟩

theorem oneJet_spec (J i : ℕ) (hi : i < J) :
    coefficient (oneJet J).coefficients i = (1 : Polynomial ℚ).coeff i := by
  rw [oneJet_coefficient J i hi]
  simp only [coeff_one]

/-- Actual local array value equals native multilinear interpolation under any
low-coefficient port specifications. -/
theorem localEvaluate_correct (J w : ℕ) (T : (Fin w → Bool) → EntryReport)
    (inputs : Fin w → Array ℚ) (ports : Fin w → Polynomial ℚ)
    (hinputs : ∀ v i, i < J → coefficient (inputs v) i = (ports v).coeff i) :
    asPolynomial (localEvaluate J w T inputs).coefficients =
      evaluate w (fun eta => C ((T eta).value : ℚ)) ports %ₘ X ^ J := by
  induction w with
  | zero =>
    change asPolynomial (scaleJet (oneJet J).coefficients ((T Fin.elim0).value : ℚ) J).coefficients = _
    simpa only [evaluate, mul_one] using
      scaleJet_correct (oneJet J).coefficients ((T Fin.elim0).value : ℚ) J 1 (oneJet_spec J)
  | succ w ih =>
    let lo := localEvaluate J w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)
    let hi := localEvaluate J w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)
    let L := evaluate w (fun eta => C ((T (Fin.cons false eta)).value : ℚ)) (fun i => ports i.succ)
    let H := evaluate w (fun eta => C ((T (Fin.cons true eta)).value : ℚ)) (fun i => ports i.succ)
    have hlo : asPolynomial lo.coefficients = L %ₘ X ^ J :=
      ih _ _ _ (fun v i h => hinputs v.succ i h)
    have hhi : asPolynomial hi.coefficients = H %ₘ X ^ J :=
      ih _ _ _ (fun v i h => hinputs v.succ i h)
    let neg := scaleJet (inputs 0) (-1) J
    let no := addJet (oneJet J).coefficients neg.coefficients J
    have hneg : asPolynomial neg.coefficients = (C (-1) * ports 0) %ₘ X ^ J :=
      scaleJet_correct _ _ _ _ (hinputs 0)
    have hno : asPolynomial no.coefficients = (1 - ports 0) %ₘ X ^ J := by
      have h := addJet_correct (oneJet J).coefficients neg.coefficients J 1 (C (-1) * ports 0)
        (oneJet_spec J) (specification_of_asPolynomial _ _ _ hneg)
      convert h using 1
      congr 1
      simp only [C_neg, C_1, neg_mul]
      ring
    let left := multiply no.coefficients lo.coefficients J
    let right := multiply (inputs 0) hi.coefficients J
    have hleft : asPolynomial left.coefficients = ((1 - ports 0) * L) %ₘ X ^ J :=
      multiply_correct _ _ _ _ _ (specification_of_asPolynomial _ _ _ hno)
        (specification_of_asPolynomial _ _ _ hlo)
    have hright : asPolynomial right.coefficients = (ports 0 * H) %ₘ X ^ J :=
      multiply_correct _ _ _ _ _ (hinputs 0) (specification_of_asPolynomial _ _ _ hhi)
    change asPolynomial (addJet left.coefficients right.coefficients J).coefficients = _
    exact addJet_correct _ _ _ _ _ (specification_of_asPolynomial _ _ _ hleft)
      (specification_of_asPolynomial _ _ _ hright)

/-- Per-node rational arithmetic/read overhead, before callback work. -/
def localOverhead (J : ℕ) : ℕ := 2 * (J * (J + 1)) + 5 * J

/-- Callback work is charged at every actual leaf; no truth-table oracle cost is omitted. -/
theorem localEvaluate_work (J w A : ℕ) (T : (Fin w → Bool) → EntryReport)
    (inputs : Fin w → Array ℚ)
    (hT : ∀ eta, (T eta).arithmetic ≤ A ∧ (T eta).reads ≤ A) :
    (localEvaluate J w T inputs).arithmetic ≤ 2 ^ w * (A + (w + 1) * localOverhead J + J) ∧
      (localEvaluate J w T inputs).reads ≤ 2 ^ w * (A + (w + 1) * localOverhead J + J) := by
  induction w with
  | zero =>
    have h := hT Fin.elim0
    dsimp only [localEvaluate, scaleJet]
    simp only [pow_zero, one_mul, Nat.zero_add]
    constructor <;> omega
  | succ w ih =>
    have hl := ih (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)
      (fun eta => hT (Fin.cons false eta))
    have hh := ih (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)
      (fun eta => hT (Fin.cons true eta))
    dsimp only [localEvaluate]
    simp only [scaleJet, addJet, multiply_work]
    have hp : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by decide)
    have hs : localOverhead J ≤ 2 ^ w * 2 * localOverhead J := by
      have h := Nat.mul_le_mul_right (localOverhead J) (show 1 ≤ 2 ^ w * 2 by omega)
      simpa only [one_mul] using h
    unfold localOverhead at hl hh hs ⊢
    rw [pow_succ]
    constructor <;> nlinarith [hl.1, hl.2, hh.1, hh.2, hs]

/-- Source polynomial described by a finite coefficient-array tail. -/
noncomputable def sourceTail (a : Array ℚ) (start len : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range len, C (coefficient a (start + i)) * X ^ i

/-- Executed Horner shift by the integer/rational node, with cached multiplication. -/
def shiftFrom (a : Array ℚ) (t : ℚ) (J : ℕ) : ℕ → ℕ → InverseReport
  | _, 0 => zeroJet J
  | start, len + 1 =>
      let old := shiftFrom a t J (start + 1) len
      let product := multiply old.coefficients #[t, 1] J
      let constant := scaleJet (oneJet J).coefficients (coefficient a start) J
      let out := addJet constant.coefficients product.coefficients J
      ⟨out.coefficients, old.arithmetic + product.arithmetic + constant.arithmetic + out.arithmetic,
        old.reads + product.reads + constant.reads + out.reads + 1⟩

theorem sourceTail_succ (a : Array ℚ) (start len : ℕ) :
    sourceTail a start (len + 1) = C (coefficient a start) + X * sourceTail a (start + 1) len := by
  unfold sourceTail
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, pow_zero, mul_one, Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show start + (i + 1) = start + 1 + i by omega, pow_succ]
  ring

theorem shiftLinear_polynomial (t : ℚ) : asPolynomial #[t, 1] = C t + X := by
  simp [asPolynomial, jetPolynomial, coefficient, Finset.sum_range_succ]
  rw [← C_mul_X_eq_monomial, C_1, one_mul]

/-- Every actually computed Horner suffix is the finite shifted source tail. -/
theorem shiftFrom_correct (a : Array ℚ) (t : ℚ) (J start len : ℕ) :
    asPolynomial (shiftFrom a t J start len).coefficients = taylor t (sourceTail a start len) %ₘ X ^ J := by
  induction len generalizing start with
  | zero => simp [shiftFrom, sourceTail, zeroJet_correct]
  | succ len ih =>
    let old := shiftFrom a t J (start + 1) len
    let product := multiply old.coefficients #[t, 1] J
    let constant := scaleJet (oneJet J).coefficients (coefficient a start) J
    have ho : asPolynomial old.coefficients = taylor t (sourceTail a (start + 1) len) %ₘ X ^ J := ih _
    have hp : asPolynomial product.coefficients =
        (taylor t (sourceTail a (start + 1) len) * (C t + X)) %ₘ X ^ J := by
      apply multiply_correct
      · exact specification_of_asPolynomial _ _ _ ho
      · intro i _
        rw [← asPolynomial_coeff, shiftLinear_polynomial]
    have hc : asPolynomial constant.coefficients = C (coefficient a start) %ₘ X ^ J := by
      simpa only [mul_one] using scaleJet_correct (oneJet J).coefficients
        (coefficient a start) J 1 (oneJet_spec J)
    have he : taylor t (sourceTail a start (len + 1)) = C (coefficient a start) +
        taylor t (sourceTail a (start + 1) len) * (C t + X) := by
      rw [sourceTail_succ, map_add, taylor_C, taylor_mul, taylor_X]
      ring
    rw [he]
    change asPolynomial (addJet constant.coefficients product.coefficients J).coefficients = _
    exact addJet_correct _ _ _ _ _ (specification_of_asPolynomial _ _ _ hc)
      (specification_of_asPolynomial _ _ _ hp)

theorem shiftFrom_work (a : Array ℚ) (t : ℚ) (J start len : ℕ) :
    (shiftFrom a t J start len).arithmetic = len * (J * (J + 1) + 2 * J) ∧
      (shiftFrom a t J start len).reads = len * (J * (J + 1) + 3 * J + 1) := by
  induction len generalizing start with
  | zero => simp [shiftFrom, zeroJet]
  | succ len ih =>
    simp only [shiftFrom, scaleJet, addJet, multiply_work, ih]
    constructor <;> ring

/-- The complete supplied source row is shifted, with no requested Taylor value assumed. -/
theorem sourceTail_eq (a : Array ℚ) (P : Polynomial ℚ) (R : ℕ)
    (hP : P.natDegree ≤ R) (ha : ∀ i ≤ R, coefficient a i = P.coeff i) :
    sourceTail a 0 (R + 1) = P := by
  rw [sourceTail, P.as_sum_range' (R + 1) (by omega)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.zero_add, ha i (by have := Finset.mem_range.mp hi; omega), C_mul_X_pow_eq_monomial]

/-- Executable row Taylor supplier from concrete source coefficient arrays. -/
def shiftRow (a : Array ℚ) (t : ℚ) (R J : ℕ) : InverseReport := shiftFrom a t J 0 (R + 1)

theorem shiftRow_correct (a : Array ℚ) (t : ℚ) (R J : ℕ) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ R) (ha : ∀ i ≤ R, coefficient a i = P.coeff i) :
    asPolynomial (shiftRow a t R J).coefficients = taylor t P %ₘ X ^ J := by
  rw [shiftRow, shiftFrom_correct, sourceTail_eq a P R hP ha]

/-- Copy the degree-zero Boolean base and independent positive-degree correction. -/
def maskShift (a : Array ℚ) (base correction : Bool) (J : ℕ) : InverseReport :=
  ⟨Array.ofFn (fun k : Fin J => if k.val = 0 then
      if base then coefficient a 0 else 0 else if correction then coefficient a k.val else 0), 0, J⟩

theorem maskShift_coefficient (a : Array ℚ) (base correction : Bool) (J i : ℕ) (hi : i < J) :
    coefficient (maskShift a base correction J).coefficients i =
      if i = 0 then (if base then coefficient a 0 else 0) else
        (if correction then coefficient a i else 0) := ofFn_coefficient _ _ hi

/-- Streamed acquisition of a corrected input port, charging every row shift. -/
def acquireCorrected (source : ℕ → Array ℚ) (t : ℚ) (R J : ℕ)
    (base correction : ℕ → Bool) : ℕ → InverseReport
  | 0 => zeroJet J
  | n + 1 =>
      let old := acquireCorrected source t R J base correction n
      let row := shiftRow (source n) t R J
      let masked := maskShift row.coefficients (base n) (correction n) J
      let out := addJet old.coefficients masked.coefficients J
      ⟨out.coefficients, old.arithmetic + row.arithmetic + masked.arithmetic + out.arithmetic,
        old.reads + row.reads + masked.reads + out.reads⟩

/-- One row's independent Boolean base/correction contribution. -/
noncomputable def maskedPolynomial (P : Polynomial ℚ) (t : ℚ) (base correction : Bool) : Polynomial ℚ :=
  C (if base then P.eval t else 0) + if correction then taylor t P - C (P.eval t) else 0

theorem maskedPolynomial_coefficient (P : Polynomial ℚ) (t : ℚ) (base correction : Bool) (i : ℕ) :
    (maskedPolynomial P t base correction).coeff i =
      if i = 0 then (if base then (taylor t P).coeff 0 else 0) else
        (if correction then (taylor t P).coeff i else 0) := by
  cases i with
  | zero => cases base <;> cases correction <;> simp [maskedPolynomial, taylor_coeff_zero]
  | succ i => cases base <;> cases correction <;> simp [maskedPolynomial]

theorem acquireCorrected_coefficient (source : ℕ → Array ℚ) (P : ℕ → Polynomial ℚ)
    (t : ℚ) (R J n : ℕ) (base correction : ℕ → Bool)
    (hP : ∀ v < n, (P v).natDegree ≤ R)
    (hs : ∀ v < n, ∀ k ≤ R, coefficient (source v) k = (P v).coeff k)
    (i : ℕ) (hi : i < J) :
    coefficient (acquireCorrected source t R J base correction n).coefficients i =
      if i = 0 then ∑ v ∈ Finset.range n, if base v then (taylor t (P v)).coeff 0 else 0
      else ∑ v ∈ Finset.range n, if correction v then (taylor t (P v)).coeff i else 0 := by
  induction n with
  | zero => simp [acquireCorrected, zeroJet_coefficient]
  | succ n ih =>
    have hold := ih (fun v hv => hP v (by omega)) (fun v hv => hs v (by omega))
    have hrow := shiftRow_correct (source n) t R J (P n) (hP n (by omega)) (hs n (by omega))
    have hr (k : ℕ) (hk : k < J) := specification_of_asPolynomial _ _ _ hrow k hk
    change coefficient (addJet (acquireCorrected source t R J base correction n).coefficients
      (maskShift (shiftRow (source n) t R J).coefficients (base n) (correction n) J).coefficients J).coefficients i = _
    rw [addJet_coefficient _ _ J i hi, hold, maskShift_coefficient _ _ _ J i hi,
      hr i hi, hr 0 (by omega)]
    by_cases hz : i = 0 <;> simp [hz, Finset.sum_range_succ]

/-- Complete corrected-input acquisition from SOURCE coefficient arrays, not requested Taylor values. -/
theorem acquireCorrected_correct (source : ℕ → Array ℚ) (P : ℕ → Polynomial ℚ)
    (t : ℚ) (R J n : ℕ) (base correction : ℕ → Bool)
    (hP : ∀ v < n, (P v).natDegree ≤ R)
    (hs : ∀ v < n, ∀ k ≤ R, coefficient (source v) k = (P v).coeff k) :
    asPolynomial (acquireCorrected source t R J base correction n).coefficients =
      (∑ v ∈ Finset.range n, maskedPolynomial (P v) t (base v) (correction v)) %ₘ X ^ J := by
  have hsize : (acquireCorrected source t R J base correction n).coefficients.size = J := by
    cases n <;> simp [acquireCorrected, zeroJet_size, addJet_size]
  ext k
  rw [asPolynomial_coeff, coeff_mod_X_pow]
  by_cases hk : k < J
  · rw [ite_eq_left hk, acquireCorrected_coefficient source P t R J n base correction hP hs k hk,
      Polynomial.finsetSum_coeff]
    by_cases hz : k = 0 <;> simp only [maskedPolynomial_coefficient, hz, ite_true, ite_false]
  · rw [ite_eq_right hk, coefficient_zero (by omega)]

theorem acquireCorrected_work (source : ℕ → Array ℚ) (t : ℚ) (R J n : ℕ) (base correction : ℕ → Bool) :
    (acquireCorrected source t R J base correction n).arithmetic =
      n * ((R + 1) * (J * (J + 1) + 2 * J) + J) ∧
    (acquireCorrected source t R J base correction n).reads =
      n * ((R + 1) * (J * (J + 1) + 3 * J + 1) + 3 * J) := by
  induction n with
  | zero => simp [acquireCorrected, zeroJet]
  | succ n ih =>
    simp only [acquireCorrected, shiftRow, shiftFrom_work, maskShift, addJet, ih]
    constructor <;> ring

/-- The finite masked-row sum is the EXISTING native correctedPort. -/
theorem maskedSum_native {n : ℕ} (rows : Fin n → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (hrows : ∀ v, (rows v).natDegree ≤ R) (x U : Finset (Fin n)) :
    (∑ v : Fin n, maskedPolynomial (rows v) t (decide (v ∈ x)) (decide (v ∈ U))) =
      SemiprimeCounterPacketHeight.correctedPort rows t R x U := by
  classical
  ext k
  rw [Polynomial.finsetSum_coeff]
  simp only [SemiprimeCounterPacketHeight.correctedPort, SemiprimeCounterPacketHeight.packet_coeff]
  cases k with
  | zero =>
    simp [maskedPolynomial_coefficient, SemiprimeBooleanDiagonal.indicator, taylor_coeff_zero]
  | succ k =>
    by_cases hk : k < R
    · simp [maskedPolynomial_coefficient, hk, SemiprimeBooleanDiagonal.indicator]
    · have hz (v : Fin n) : (taylor t (rows v)).coeff (k + 1) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_taylor]
        exact lt_of_le_of_lt (hrows v) (by omega)
      simp [maskedPolynomial_coefficient, hk, hz]

/-- Concrete finite-index source family supplied by the layout constructor. -/
def acquireCorrectedFin {n : ℕ} (source : Fin n → Array ℚ) (t : ℚ) (R J : ℕ)
    (base correction : Fin n → Bool) : InverseReport :=
  acquireCorrected (fun v => if h : v < n then source ⟨v, h⟩ else #[]) t R J
    (fun v => if h : v < n then base ⟨v, h⟩ else false)
    (fun v => if h : v < n then correction ⟨v, h⟩ else false) n

/-- Actual acquired array is the native correctedPort used by the global counter. -/
theorem acquireCorrectedFin_native {n : ℕ} (source : Fin n → Array ℚ)
    (rows : Fin n → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (hrows : ∀ v, (rows v).natDegree ≤ R)
    (hsource : ∀ v k, k ≤ R → coefficient (source v) k = (rows v).coeff k)
    (x U : Finset (Fin n)) :
    asPolynomial (acquireCorrectedFin source t R J (fun v => decide (v ∈ x))
      (fun v => decide (v ∈ U))).coefficients =
      SemiprimeCounterPacketHeight.correctedPort rows t R x U %ₘ X ^ J := by
  let P : ℕ → Polynomial ℚ := fun v => if h : v < n then rows ⟨v, h⟩ else 0
  have hs := acquireCorrected_correct
    (fun v => if h : v < n then source ⟨v, h⟩ else #[]) P t R J n
    (fun v => if h : v < n then decide (⟨v, h⟩ ∈ x) else false)
    (fun v => if h : v < n then decide (⟨v, h⟩ ∈ U) else false)
    (by intro v hv; simpa only [P, dite_eq_left hv] using hrows ⟨v, hv⟩)
    (by intro v hv k hk; simpa only [P, dite_eq_left hv] using hsource ⟨v, hv⟩ k hk)
  change asPolynomial (acquireCorrected _ _ _ _ _ _ _).coefficients = _
  rw [hs]
  congr 1
  rw [← maskedSum_native rows t R hrows x U, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' := Finset.mem_range.mp hv
  simp only [P, dite_eq_left hv']

/-- Complete local native call: acquire each input port then evaluate its table. -/
def nativeLocal {n : ℕ} (w J R : ℕ) (t : ℚ)
    (source : Fin w → Fin n → Array ℚ) (base correction : Fin n → Bool)
    (T : (Fin w → Bool) → EntryReport) : InverseReport :=
  let inputs := Array.ofFn (fun v : Fin w => acquireCorrectedFin (source v) t R J base correction)
  let getInput := fun v : Fin w => inputs[v.val]'(by simp [inputs])
  let out := localEvaluate J w T (fun v => (getInput v).coefficients)
  ⟨out.coefficients, (∑ v, (getInput v).arithmetic) + out.arithmetic,
    (∑ v, (getInput v).reads) + out.reads⟩

/-- The actual full local frontend agrees with the EXISTING native polynomial evaluator. -/
theorem nativeLocal_correct {n : ℕ} (w J R : ℕ) (t : ℚ)
    (source : Fin w → Fin n → Array ℚ) (rows : Fin w → Fin n → Polynomial ℚ)
    (hrows : ∀ v i, (rows v i).natDegree ≤ R)
    (hsource : ∀ v i k, k ≤ R → coefficient (source v i) k = (rows v i).coeff k)
    (x U : Finset (Fin n)) (T : (Fin w → Bool) → EntryReport) :
    asPolynomial (nativeLocal w J R t source (fun v => decide (v ∈ x))
      (fun v => decide (v ∈ U)) T).coefficients =
      evaluate w (fun eta => C ((T eta).value : ℚ))
        (fun v => SemiprimeCounterPacketHeight.correctedPort (rows v) t R x U) %ₘ X ^ J := by
  apply localEvaluate_correct
  intro v i hi
  simpa only [Array.getElem_ofFn] using specification_of_asPolynomial _ _ _
    (acquireCorrectedFin_native (source v) (rows v) t R J (hrows v) (hsource v) x U) i hi

theorem acquireCorrectedFin_work {n : ℕ} (source : Fin n → Array ℚ) (t : ℚ) (R J : ℕ)
    (base correction : Fin n → Bool) :
    (acquireCorrectedFin source t R J base correction).arithmetic =
      n * ((R + 1) * (J * (J + 1) + 2 * J) + J) ∧
    (acquireCorrectedFin source t R J base correction).reads =
      n * ((R + 1) * (J * (J + 1) + 3 * J + 1) + 3 * J) :=
  acquireCorrected_work _ _ _ _ _ _ _

/-- Full local cost includes materialized corrected inputs and every table callback. -/
theorem nativeLocal_work {n : ℕ} (w J R A : ℕ) (t : ℚ)
    (source : Fin w → Fin n → Array ℚ) (base correction : Fin n → Bool)
    (T : (Fin w → Bool) → EntryReport)
    (hT : ∀ eta, (T eta).arithmetic ≤ A ∧ (T eta).reads ≤ A) :
    (nativeLocal w J R t source base correction T).arithmetic ≤
      w * (n * ((R + 1) * (J * (J + 1) + 2 * J) + J)) +
        2 ^ w * (A + (w + 1) * localOverhead J + J) ∧
    (nativeLocal w J R t source base correction T).reads ≤
      w * (n * ((R + 1) * (J * (J + 1) + 3 * J + 1) + 3 * J)) +
        2 ^ w * (A + (w + 1) * localOverhead J + J) := by
  let inputs := Array.ofFn (fun v : Fin w => acquireCorrectedFin (source v) t R J base correction)
  let getInput := fun v : Fin w => inputs[v.val]'(by simp [inputs])
  have hc (v : Fin w) : (getInput v).arithmetic = n * ((R + 1) * (J * (J + 1) + 2 * J) + J) ∧
      (getInput v).reads = n * ((R + 1) * (J * (J + 1) + 3 * J + 1) + 3 * J) := by
    simpa only [getInput, inputs, Array.getElem_ofFn] using
      acquireCorrectedFin_work (source v) t R J base correction
  have ha : (∑ v, (getInput v).arithmetic) = w * (n * ((R + 1) * (J * (J + 1) + 2 * J) + J)) := by
    simp only [(hc _).1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  have hr : (∑ v, (getInput v).reads) = w * (n * ((R + 1) * (J * (J + 1) + 3 * J + 1) + 3 * J)) := by
    simp only [(hc _).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  have he := localEvaluate_work J w A T (fun v => (getInput v).coefficients) hT
  change (∑ v, (getInput v).arithmetic) + _ ≤ _ ∧ (∑ v, (getInput v).reads) + _ ≤ _
  rw [ha, hr]
  exact ⟨Nat.add_le_add_left he.1 _, Nat.add_le_add_left he.2 _⟩

theorem representation_neg {q : ℚ} {d B : ℕ} (h : Representation q d B) :
    Representation (-q) d B := by
  obtain ⟨z, hz, hb⟩ := h
  exact ⟨-z, by simpa only [Int.cast_neg, neg_div] using congrArg Neg.neg hz,
    by simpa only [Int.natAbs_neg] using hb⟩

theorem oneJet_representation (J d : ℕ) (hd : 0 < d) (i : ℕ) (hi : i < J) :
    Representation (coefficient (oneJet J).coefficients i) d d := by
  rw [oneJet_coefficient J i hi]
  split_ifs
  · exact SemiprimeHermiteArrayHeight.representation_one d hd
  · exact representation_mono (SemiprimeHermiteArrayHeight.representation_zero d) (by omega)

/-- Uniform local tree height scale, based only on native input-port bounds. -/
def localBase (J d B : ℕ) : ℕ := 2 * J * (d + B)

/-- Every recursive local subtree has an explicit shared power denominator;
this applies before any sum cancellation and charges no hidden normalization. -/
theorem localEvaluate_representation (J w d B : ℕ) (hd : 0 < d)
    (T : (Fin w → Bool) → EntryReport) (inputs : Fin w → Array ℚ)
    (hT : ∀ eta, (T eta).value.natAbs ≤ 1)
    (hinputs : ∀ v i, i < J → Representation (coefficient (inputs v) i) d B)
    (i : ℕ) (hi : i < J) :
    Representation (coefficient (localEvaluate J w T inputs).coefficients i)
      (d ^ w) (localBase J d B ^ w) := by
  induction w generalizing i with
  | zero =>
    rw [pow_zero, pow_zero]
    change Representation (coefficient (scaleJet (oneJet J).coefficients ((T Fin.elim0).value : ℚ) J).coefficients i) 1 1
    rw [scaleJet_coefficient _ _ J i hi, oneJet_coefficient J i hi]
    split_ifs
    · rw [mul_one]
      exact representation_mono (SemiprimeHermiteArrayHeight.representation_integer _) (hT _)
    · rw [mul_zero]
      exact representation_mono (SemiprimeHermiteArrayHeight.representation_zero 1) (by decide)
  | succ w ih =>
    let lo := localEvaluate J w (fun eta => T (Fin.cons false eta)) (fun v => inputs v.succ)
    let hiTree := localEvaluate J w (fun eta => T (Fin.cons true eta)) (fun v => inputs v.succ)
    have hlo (k : ℕ) (hk : k < J) : Representation (coefficient lo.coefficients k) (d ^ w) (localBase J d B ^ w) :=
      ih _ _ (fun eta => hT (Fin.cons false eta)) (fun v => hinputs v.succ) k hk
    have hhi (k : ℕ) (hk : k < J) : Representation (coefficient hiTree.coefficients k) (d ^ w) (localBase J d B ^ w) :=
      ih _ _ (fun eta => hT (Fin.cons true eta)) (fun v => hinputs v.succ) k hk
    let neg := scaleJet (inputs 0) (-1) J
    let no := addJet (oneJet J).coefficients neg.coefficients J
    have hneg (k : ℕ) (hk : k < J) : Representation (coefficient neg.coefficients k) d B := by
      rw [scaleJet_coefficient _ _ J k hk, neg_one_mul]
      exact representation_neg (hinputs 0 k hk)
    have hno (k : ℕ) (hk : k < J) : Representation (coefficient no.coefficients k) d (d + B) :=
      addJet_representation _ _ J d d B (oneJet_representation J d hd) hneg k hk
    let left := multiply no.coefficients lo.coefficients J
    let right := multiply (inputs 0) hiTree.coefficients J
    have hl := multiply_representation no.coefficients lo.coefficients d (d ^ w) (d + B)
      (localBase J d B ^ w) J hno hlo i hi
    have hr := multiply_representation (inputs 0) hiTree.coefficients d (d ^ w) B
      (localBase J d B ^ w) J (hinputs 0) hhi i hi
    have hr' : Representation (coefficient right.coefficients i) (d * d ^ w)
        (J * (d + B) * localBase J d B ^ w) := representation_mono hr (by gcongr; omega)
    change Representation (coefficient (addJet left.coefficients right.coefficients J).coefficients i) _ _
    rw [addJet_coefficient _ _ J i hi]
    have hs := representation_add hl hr'
    convert hs using 1
    · rw [pow_succ']
    · rw [pow_succ]
      unfold localBase
      ring

end RiemannGaussian.SemiprimeLocalArrayFrontend
