/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorTotalTraceSourceAudit
import scripts.ArithmeticOperatorQDetValuationPhaseAudit
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Integral signed products: transport with the repeated depths paid

For exponents in {-1,0,1}, integrality forces the whole-product weighted
prime-depth packet to agree with its cumulative-row ledger at every prime
of total unreweighted depth at most one. The full discrepancy is at most
four times the repeated depth. An arbitrary bounded depth weight retains
the physical prime-power cutoff and phase. No depth is reset.

Only the finite estimate is asserted here. Complete-base mean and source
transport, and any new signed arithmetic estimate, remain separate gates.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.SignedDepthTransport

/-- Depths one through v, with the literal phase and any bounded cutoff. -/
def weightedDepth (f : ℕ → ℂ) (v : ℕ) : ℂ :=
  ∑ r ∈ Finset.range v, f (r+1)

/-- This weighted packet specializes to the existing full-depth phase. -/
theorem weightedDepth_phase (z : ℂ) (v : ℕ) :
    weightedDepth (fun r => z^r) v = QDetValuationPhase.depthPacket z v := rfl

/-- The difference uses the next v depths, never a phase reset. -/
theorem weightedDepth_add (f : ℕ → ℂ) (a v : ℕ) :
    weightedDepth f (a+v)-weightedDepth f a =
      ∑ r ∈ Finset.range v, f (a+r+1) := by
  simp only [weightedDepth, Finset.sum_range_add, add_sub_cancel_left]

/-- Every bounded-depth increment has norm at most its number of depths. -/
theorem norm_increment_le (f : ℕ → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) (a v : ℕ) :
    ‖weightedDepth f (a+v)-weightedDepth f a‖ ≤ v := by
  rw [weightedDepth_add]
  calc
    _ ≤ ∑ r ∈ Finset.range v, ‖f (a+r+1)‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range v, (1:ℝ) := Finset.sum_le_sum (fun r _ => hf _)
    _ = v := by simp

/-- The whole packet has the same elementary norm bound. -/
theorem norm_depth_le (f : ℕ → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) (v : ℕ) :
    ‖weightedDepth f v‖ ≤ v := by
  simpa [weightedDepth] using norm_increment_le f hf 0 v

/-- The only zero/single-depth packet is its literal first-depth coefficient. -/
theorem depth_le_one (f : ℕ → ℂ) (v : ℕ) (hv : v ≤ 1) :
    weightedDepth f v = (v:ℂ)*f 1 := by
  interval_cases v <;> simp [weightedDepth]

/-- An increment fitting in a single total depth has no shifted phase. -/
theorem increment_le_one (f : ℕ → ℂ) (a v : ℕ) (hv : a+v ≤ 1) :
    weightedDepth f (a+v)-weightedDepth f a = (v:ℂ)*f 1 := by
  rw [depth_le_one f (a+v) hv, depth_le_one f a (by omega)]
  push_cast
  ring

/-- Signed cumulative-row ledger: every row retains its preceding depth. -/
def rowLedger (s : Finset ℕ) (beta : ℕ → ℤ) (v offset : ℕ → ℕ)
    (f : ℕ → ℂ) : ℂ :=
  ∑ e ∈ s, (beta e:ℂ) *
    (weightedDepth f (offset e+v e)-weightedDepth f (offset e))

/-- Unit-bounded signed exponents retain the total unweighted depth budget. -/
theorem norm_rowLedger_le (s : Finset ℕ) (beta : ℕ → ℤ) (v offset : ℕ → ℕ)
    (f : ℕ → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1)
    (hb : ∀ e ∈ s, -1 ≤ beta e ∧ beta e ≤ 1) :
    ‖rowLedger s beta v offset f‖ ≤ (∑ e ∈ s, v e : ℕ) := by
  calc
    _ ≤ ∑ e ∈ s, ‖(beta e:ℂ) *
        (weightedDepth f (offset e+v e)-weightedDepth f (offset e))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ e ∈ s, (v e:ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      have hbe : ‖(beta e:ℂ)‖ ≤ 1 := by
        obtain ⟨hl, hu⟩ := hb e he
        interval_cases beta e <;> norm_num
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hbe (norm_nonneg _)).trans
        (by simpa using norm_increment_le f hf (offset e) (v e))
    _ = _ := by norm_cast

/-- The valuation of an integral signed product cannot exceed the original depth. -/
theorem signed_depth_le (s : Finset ℕ) (beta : ℕ → ℤ) (v : ℕ → ℕ) (w : ℕ)
    (hb : ∀ e ∈ s, beta e ≤ 1)
    (hw : (w:ℤ) = ∑ e ∈ s, beta e*(v e:ℤ)) : w ≤ ∑ e ∈ s, v e := by
  have h : (w:ℤ) ≤ ∑ e ∈ s, (v e:ℤ) := by
    rw [hw]
    apply Finset.sum_le_sum
    intro e he
    simpa using mul_le_mul_of_nonneg_right (hb e he) (Int.natCast_nonneg (v e))
  exact_mod_cast h

/-- At total depth at most one the signed row ledger is exactly the integer packet. -/
theorem single_depth_exact (s : Finset ℕ) (beta : ℕ → ℤ) (v offset : ℕ → ℕ)
    (f : ℕ → ℂ) (w : ℕ)
    (hb : ∀ e ∈ s, beta e ≤ 1)
    (hw : (w:ℤ) = ∑ e ∈ s, beta e*(v e:ℤ))
    (ho : ∀ e ∈ s, offset e+v e ≤ ∑ i ∈ s, v i)
    (hV : ∑ e ∈ s, v e ≤ 1) :
    weightedDepth f w = rowLedger s beta v offset f := by
  have hwl := signed_depth_le s beta v w hb hw
  rw [depth_le_one f w (by omega), rowLedger]
  calc
    (w:ℂ)*f 1 = (∑ e ∈ s, (beta e:ℂ)*(v e:ℂ))*f 1 := by
      congr 1
      exact_mod_cast hw
    _ = ∑ e ∈ s, (beta e:ℂ)*((v e:ℂ)*f 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [increment_le_one f (offset e) (v e) ((ho e he).trans hV)]

/-- The full signed depth error is confined to repeated prime-power depths. -/
theorem depth_transport (s : Finset ℕ) (beta : ℕ → ℤ) (v offset : ℕ → ℕ)
    (f : ℕ → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) (w : ℕ)
    (hb : ∀ e ∈ s, -1 ≤ beta e ∧ beta e ≤ 1)
    (hw : (w:ℤ) = ∑ e ∈ s, beta e*(v e:ℤ))
    (ho : ∀ e ∈ s, offset e+v e ≤ ∑ i ∈ s, v i) :
    ‖weightedDepth f w-rowLedger s beta v offset f‖ ≤
      4*((∑ e ∈ s, v e)-1:ℕ) := by
  by_cases hV : ∑ e ∈ s, v e ≤ 1
  · rw [single_depth_exact s beta v offset f w (fun e he => (hb e he).2) hw ho hV]
    simp
  · have htwo : 2 ≤ ∑ e ∈ s, v e := by omega
    have hwV := signed_depth_le s beta v w (fun e he => (hb e he).2) hw
    have hwVR : (w:ℝ) ≤ (∑ e ∈ s, v e:ℕ) := by exact_mod_cast hwV
    have hV2 : (2:ℝ) ≤ (∑ e ∈ s, v e:ℕ) := by exact_mod_cast htwo
    have hcast : (((∑ e ∈ s, v e)-1:ℕ):ℝ) = (∑ e ∈ s, v e:ℕ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ ∑ e ∈ s, v e), Nat.cast_one]
    calc
      _ ≤ ‖weightedDepth f w‖+‖rowLedger s beta v offset f‖ := norm_sub_le _ _
      _ ≤ (w:ℝ)+(∑ e ∈ s, v e:ℕ) :=
        add_le_add (norm_depth_le f hf w) (norm_rowLedger_le s beta v offset f hf hb)
      _ ≤ 4*((∑ e ∈ s, v e)-1:ℕ) := by rw [hcast]; linarith

/-- Cumulative depth of earlier actual cyclotomic factors. -/
def beforeDepth (b M q e : ℕ) : ℕ :=
  ∑ i ∈ (Finset.Icc 2 M).filter (fun i => i<e),
    padicValInt q (TotalTraceSource.value b i)

/-- The actual preceding-depth block lies inside the original total depth. -/
theorem beforeDepth_le (b M q e : ℕ) (he : e ∈ Finset.Icc 2 M) :
    beforeDepth b M q e + padicValInt q (TotalTraceSource.value b e) ≤
      ∑ i ∈ Finset.Icc 2 M, padicValInt q (TotalTraceSource.value b i) := by
  have hnot : e ∉ (Finset.Icc 2 M).filter (fun i => i<e) := by simp
  have hsub : insert e ((Finset.Icc 2 M).filter (fun i => i<e)) ⊆ Finset.Icc 2 M := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact he
    · exact (Finset.mem_filter.mp hi).1
  have h := Finset.sum_le_sum_of_subset hsub (f := fun i =>
    padicValInt q (TotalTraceSource.value b i))
  simpa [Finset.sum_insert hnot, beforeDepth, Nat.add_comm] using h

/-- Actual integral cyclotomic product, not a formal freely chosen valuation array. -/
theorem cyclotomic_depth_transport (b M q : ℕ) [Fact q.Prime] (hb : 2 ≤ b)
    (beta : ℕ → ℤ) (P : ℤ)
    (hP : TotalTraceSource.signedProduct b M beta = (P:ℚ))
    (hbeta : ∀ e ∈ Finset.Icc 2 M, -1 ≤ beta e ∧ beta e ≤ 1)
    (f : ℕ → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) :
    ‖weightedDepth f (padicValInt q P) -
      rowLedger (Finset.Icc 2 M) beta
        (fun e => padicValInt q (TotalTraceSource.value b e))
        (beforeDepth b M q) f‖ ≤
      4*((∑ e ∈ Finset.Icc 2 M, padicValInt q (TotalTraceSource.value b e))-1:ℕ) := by
  apply depth_transport _ _ _ _ f hf _ hbeta
  · have h := TotalTraceSource.signedProduct_valuation b M q hb beta
    simpa [hP, padicValRat.of_int] using h
  · exact fun e he => beforeDepth_le b M q e he


/-- The literal physical prime-power phase, retaining the physical cutoff. -/
def physicalWeight (q X : ℕ) (y : ℝ) (r : ℕ) : ℂ :=
  if q^r ≤ X then QDetValuationPhase.physicalPhase q y ^ r else 0

/-- Cutting off the literal prime-power phase never enlarges its unit modulus. -/
theorem physicalWeight_norm (q X : ℕ) (y : ℝ) (r : ℕ) :
    ‖physicalWeight q X y r‖ ≤ 1 := by
  have hp : ‖QDetValuationPhase.physicalPhase q y‖ = 1 := by
    rw [QDetValuationPhase.physicalPhase, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, Real.exp_zero]
  unfold physicalWeight
  split_ifs
  · rw [norm_pow, hp, one_pow]
  · simp

/-- Summing the exact signed errors costs only the original repeated depths.
No denominatorwise bound is imposed on the main row ledger itself. -/
theorem cyclotomic_packet_transport (b M X : ℕ) (hb : 2 ≤ b)
    (beta : ℕ → ℤ) (P : ℤ)
    (hP : TotalTraceSource.signedProduct b M beta = (P:ℚ))
    (hbeta : ∀ e ∈ Finset.Icc 2 M, -1 ≤ beta e ∧ beta e ≤ 1)
    (primes : Finset ℕ) (hprimes : ∀ q ∈ primes, q.Prime) (y : ℝ) :
    ‖∑ q ∈ primes, (Real.log q:ℂ) *
      (weightedDepth (physicalWeight q X y) (padicValInt q P) -
        rowLedger (Finset.Icc 2 M) beta
          (fun e => padicValInt q (TotalTraceSource.value b e))
          (beforeDepth b M q) (physicalWeight q X y))‖ ≤
      4*∑ q ∈ primes, Real.log q *
        (((∑ e ∈ Finset.Icc 2 M, padicValInt q (TotalTraceSource.value b e))-1:ℕ):ℝ) := by
  calc
    _ ≤ ∑ q ∈ primes, ‖(Real.log q:ℂ) *
      (weightedDepth (physicalWeight q X y) (padicValInt q P) -
        rowLedger (Finset.Icc 2 M) beta
          (fun e => padicValInt q (TotalTraceSource.value b e))
          (beforeDepth b M q) (physicalWeight q X y))‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ primes, Real.log q *
        (4*(((∑ e ∈ Finset.Icc 2 M, padicValInt q (TotalTraceSource.value b e))-1:ℕ):ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have : Fact q.Prime := ⟨hprimes q hq⟩
      have hlog : 0 ≤ Real.log q := Real.log_nonneg (by
        exact_mod_cast (hprimes q hq).one_lt.le)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
      apply mul_le_mul_of_nonneg_left _ hlog
      exact cyclotomic_depth_transport b M q hb beta P hP hbeta
        (physicalWeight q X y) (physicalWeight_norm q X y)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring

/-- Allowing exponent two already breaks the single-depth identity.
This is a scope counterexample, not a source estimate. -/
theorem exponent_two_obstruction :
    weightedDepth (fun r => (-1:ℂ)^r) 2 ≠
      (2:ℂ)*weightedDepth (fun r => (-1:ℂ)^r) 1 := by
  norm_num [weightedDepth, Finset.sum_range_succ]

end OpenAIReview.SignedDepthTransport

#lint+ in OpenAIReview.SignedDepthTransport

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty signed-depth transport audit."
  logInfo m!"Signed depth transport: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-signed-depth-transport-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-signed-depth-transport-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual integral unit-bounded signed cyclotomic products; full phase/cutoff depth transport bounded by repeated depths; asymptotic source and averaging separate"),
      ("namespaceLinters",toJson (15:Nat)),("onlyStandardAxioms",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr details)]).pretty
