/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteAbelVariation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import scripts.ArithmeticOperatorDigitalCarryAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Moving carry cutoff: the exact smooth-source response

The weights are the integrals of the power density on literal unit cells,
not a sampled surrogate. Any code with prefix discrepancy at most B has
normalized matched-power response at most 2B/X on every interval starting
at X. Thus the native moving dyadic upper-carry code deletes the diagnostic
zero power whenever its block length is o(X). No prime estimate or zeta
explicit formula is asserted. Macroscopic blocks instead restore an exact
uncoded weighted interval; arbitrary masks do not inherit the bound.
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section
open scoped BigOperators
open Filter MeasureTheory
namespace OpenAIReview.DigitalSource

/-- Exact unit-cell integral of the matched real power density. -/
def powerCell (beta : ℝ) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ((n : ℝ)+t)^(beta-1)

/-- Signed response with every cell kept at its actual position. -/
def response (beta : ℝ) (z : ℕ → ℂ) (lo count : ℕ) : ℂ :=
  ∑ k ∈ Finset.range count, (powerCell beta (lo+k) : ℂ)*z (lo+k)

/-- Local integrability uses positivity of the physical starting point. -/
theorem powerCell_integrable (beta : ℝ) {n : ℕ} (hn : 0<n) :
    IntervalIntegrable (fun t : ℝ => ((n : ℝ)+t)^(beta-1)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  intro t ht
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  exact ((continuous_const.add continuous_id).continuousAt.rpow_const
    (Or.inl (ne_of_gt (by linarith [ht.1] : (0 : ℝ)<n+t)))).continuousWithinAt

/-- These are positive real density cells. -/
theorem powerCell_nonneg (beta : ℝ) (n : ℕ) : 0≤powerCell beta n := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg n) ht.1) _

/-- On the source strip, complete cells decrease with their position. -/
theorem powerCell_antitone {beta : ℝ} (hb : beta≤1) {n m : ℕ}
    (hn : 0<n) (hnm : n≤m) : powerCell beta m≤powerCell beta n := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (powerCell_integrable beta (hn.trans_le hnm)) (powerCell_integrable beta hn)
  intro t ht
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hnmR : (n : ℝ)≤m := by exact_mod_cast hnm
  exact Real.rpow_le_rpow_of_nonpos (by linarith [ht.1]) (by linarith)
    (by linarith)

/-- The exact cell never exceeds its left endpoint density. -/
theorem powerCell_le {beta : ℝ} (hb : beta≤1) {n : ℕ} (hn : 0<n) :
    powerCell beta n≤(n : ℝ)^(beta-1) := by
  have hi : IntervalIntegrable (fun _ : ℝ => (n : ℝ)^(beta-1)) volume 0 1 :=
    intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ)≤1)
    (powerCell_integrable beta hn) hi (fun t ht =>
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by linarith [ht.1])
        (by linarith : beta-1≤0))
  simpa [powerCell] using h

/-- Translation shows this is the literal power integral, not quadrature. -/
theorem powerCell_eq_interval (beta : ℝ) (n : ℕ) :
    powerCell beta n=∫ t in (n : ℝ)..(n+1 : ℝ), t^(beta-1) := by
  simpa [powerCell] using
    (intervalIntegral.integral_comp_add_left (fun t : ℝ => t^(beta-1)) (n : ℝ)
      (a:=0) (b:=1))

/-- Exact Mellin mass on a literal unit cell. -/
theorem powerCell_eq {beta : ℝ} (hb : 0<beta) (n : ℕ) :
    powerCell beta n=(((n : ℝ)+1)^beta-(n : ℝ)^beta)/beta := by
  rw [powerCell_eq_interval,integral_rpow (Or.inl (by linarith : -1<beta-1))]
  congr 2 <;> congr 1 <;> ring

/-- The finite interval retains both global prefix boundaries. -/
theorem shifted_prefix (z : ℕ → ℂ) (lo count : ℕ) :
    ∑ k ∈ Finset.range count,z (lo+k)=
      (∑ k ∈ Finset.range (lo+count),z k)-(∑ k ∈ Finset.range lo,z k) := by
  rw [Finset.sum_range_add]
  simp

/-- Prefix cancellation is transported only after the signed cells join. -/
theorem response_bound {beta B : ℝ} (hb : beta≤1) (z : ℕ → ℂ)
    (hB : ∀ n, ‖∑ k ∈ Finset.range n,z k‖≤B)
    {lo : ℕ} (hlo : 0<lo) (count : ℕ) :
    ‖response beta z lo count‖≤2*B*(lo : ℝ)^(beta-1) := by
  have hB0 : 0≤B := by simpa using hB 0
  cases count with
  | zero => simp [response]; positivity
  | succ n =>
    have h := RiemannGaussian.FiniteAbelVariation.decreasing_bound
      (fun k => powerCell beta (lo+k)) (fun k => z (lo+k)) n
      (fun k _ => powerCell_nonneg beta (lo+k))
      (fun i _ j _ hij => powerCell_antitone hb (by omega) (by omega))
      (B:=2*B) (by
        intro k _
        rw [shifted_prefix]
        exact (norm_sub_le _ _).trans (by linarith [hB (lo+(k+1)),hB lo]))
    exact h.trans (by
      simpa only [Nat.add_zero] using
        mul_le_mul_of_nonneg_left (powerCell_le hb hlo) (by positivity : 0≤2*B))

/-- Summing the exact unit cells recovers the full interval Mellin mass. -/
theorem sum_powerCell {beta : ℝ} (hb : 0<beta) (lo count : ℕ) :
    (∑ k ∈ Finset.range count,powerCell beta (lo+k))=
      (((lo+count : ℕ) : ℝ)^beta-(lo : ℝ)^beta)/beta := by
  simp_rw [powerCell_eq hb]
  rw [← Finset.sum_div]
  have he := Finset.sum_range_sub (fun k => ((lo+k : ℕ) : ℝ)^beta) count
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero,add_assoc] using
    congrArg (fun v : ℝ => v/beta) he

/-- Source normalization removes the exponent: only relative prefix
size remains. This is uniform in the moving interval and cutoff. -/
theorem normalized_response_bound {beta B : ℝ} (hb : beta≤1) (z : ℕ → ℂ)
    (hB : ∀ n, ‖∑ k ∈ Finset.range n,z k‖≤B)
    {lo : ℕ} (hlo : 0<lo) (count : ℕ) :
    ‖(Real.rpow (lo : ℝ) (-beta) : ℂ)*response beta z lo count‖≤2*B/(lo : ℝ) := by
  have hloR : (0 : ℝ)<lo := by exact_mod_cast hlo
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Real.rpow_eq_pow,
    abs_of_nonneg (Real.rpow_nonneg hloR.le _)]
  calc
    _ ≤ (lo : ℝ)^(-beta)*(2*B*(lo : ℝ)^(beta-1)) :=
      mul_le_mul_of_nonneg_left (response_bound hb z hB hlo count)
        (Real.rpow_nonneg hloR.le _)
    _ = 2*B*((lo : ℝ)^(-beta)*(lo : ℝ)^(beta-1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hloR,show -beta+(beta-1)=(-1 : ℝ) by ring,
        Real.rpow_neg_one,div_eq_mul_inv]

/-- An exact complex embedding of the native Kummer code. -/
def carryCode (k n : ℕ) : ℂ := DigitalCarry.highCode k n

/-- All prefixes are controlled independently of the moving cutoff. -/
theorem carryCode_prefix (k n : ℕ) :
    ‖∑ j ∈ Finset.range n,carryCode k j‖≤(2^k : ℕ) := by
  have h := DigitalCarry.abs_sum_highCode_prefix_le k n
  have he : (∑ j ∈ Finset.range n,carryCode k j)=
      ((∑ j ∈ Finset.range n,DigitalCarry.highCode k j : ℤ) : ℂ) := by
    simp [carryCode]
  rw [he,Complex.norm_intCast]
  exact_mod_cast h

/-- The actual upper-carry packet has normalized smooth source at most
2H/X. Every original lower boundary and final partial block remains. -/
theorem carry_source_bound {beta : ℝ} (hb : beta≤1) (k : ℕ)
    {lo : ℕ} (hlo : 0<lo) (count : ℕ) :
    ‖(Real.rpow (lo : ℝ) (-beta) : ℂ)*response beta (carryCode k) lo count‖≤
      2*(2^k : ℕ)/(lo : ℝ) :=
  normalized_response_bound hb (carryCode k) (carryCode_prefix k) hlo count

/-- Changing digital thresholds do not rescue the linear matched power
when the original integer prefixes are submacroscopic. -/
theorem tendsto_carry_source {beta : ℝ} (hb : beta≤1)
    (k lo count : ℕ → ℕ) (hlo : ∀ j,0<lo j)
    (hr : Tendsto (fun j => (2^(k j) : ℕ)/(lo j : ℝ)) atTop (nhds 0)) :
    Tendsto (fun j => (Real.rpow (lo j : ℝ) (-beta) : ℂ)*
      response beta (carryCode (k j)) (lo j) (count j)) atTop (nhds 0) := by
  apply squeeze_zero_norm (a:=fun j => 2*((2^(k j) : ℕ)/(lo j : ℝ)))
  · intro j
    simpa only [mul_div_assoc] using carry_source_bound hb (k j) (hlo j) (count j)
  · simpa only [mul_zero] using tendsto_const_nhds.mul hr

/-- A nonzero normalized power response requires a macroscopic prefix
budget. It cannot be certified by ordinary cancellation alone. -/
theorem source_requires_prefix {beta B eta : ℝ} (hb : beta≤1) (z : ℕ → ℂ)
    (hB : ∀ n, ‖∑ k ∈ Finset.range n,z k‖≤B)
    {lo : ℕ} (hlo : 0<lo) (count : ℕ)
    (hs : eta≤‖(Real.rpow (lo : ℝ) (-beta) : ℂ)*response beta z lo count‖) :
    eta*(lo : ℝ)≤2*B := by
  have hloR : (0 : ℝ)<lo := by exact_mod_cast hlo
  exact (le_div_iff₀ hloR).mp (hs.trans (normalized_response_bound hb z hB hlo count))

/-- At a macroscopic native cutoff the next complete block is constant.
This is the exact scope boundary of the source-deletion theorem. -/
theorem carryCode_second_block (k n : ℕ) (hn : n<2^k) :
    carryCode k (2^k+n)= -1 := by
  have hp : 0<2^k := Nat.two_pow_pos k
  have hq : (2^k+n)/2^k=1 := by
    rw [Nat.add_comm,Nat.add_div_right _ hp,Nat.div_eq_of_lt hn]
  simp [carryCode,DigitalCarry.highCode,hq]

/-- Restoring a macroscopic source here restores the identical uncoded
prime interval. Arbitrary weights retain all prime powers and phases. -/
theorem macroscopic_packet (k : ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.range (2^k),carryCode k (2^k+n)*w (2^k+n))=
      -(∑ n ∈ Finset.range (2^k),w (2^k+n)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [carryCode_second_block k n (Finset.mem_range.mp hn)]
  ring

/-- The macroscopic code has a nonzero, unchanged smooth power response,
not merely a failure of the sublinear upper bound. -/
theorem macroscopic_source {beta : ℝ} (hb : 0<beta) (k : ℕ) :
    (Real.rpow (2^k : ℕ) (-beta) : ℂ)*
      response beta (carryCode k) (2^k) (2^k)=
      -((Real.rpow 2 beta-1)/beta : ℝ) := by
  have he : response beta (carryCode k) (2^k) (2^k)=
      -((∑ n ∈ Finset.range (2^k),powerCell beta (2^k+n) : ℝ) : ℂ) := by
    unfold response
    rw [Complex.ofReal_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [carryCode_second_block k n (Finset.mem_range.mp hn)]
    simp
  rw [he,sum_powerCell hb]
  have hH : (0 : ℝ)<(2^k : ℕ) := by exact_mod_cast Nat.two_pow_pos k
  have hr : Real.rpow ((2^k : ℕ) : ℝ) (-beta)*
      -((((2^k+2^k : ℕ) : ℝ)^beta-((2^k : ℕ) : ℝ)^beta)/beta)=
      -((Real.rpow 2 beta-1)/beta) := by
    rw [Real.rpow_eq_pow,Real.rpow_eq_pow,Nat.cast_add,
      show ((2^k : ℕ) : ℝ)+((2^k : ℕ) : ℝ)=2*((2^k : ℕ) : ℝ) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hH.le]
    have hi : ((2^k : ℕ) : ℝ)^(-beta)*((2^k : ℕ) : ℝ)^beta=1 := by
      rw [← Real.rpow_add hH,neg_add_cancel,Real.rpow_zero]
    calc
      _ = -((((2 : ℝ)^beta-1)*
          (((2^k : ℕ) : ℝ)^(-beta)*((2^k : ℕ) : ℝ)^beta))/beta) := by ring
      _ = _ := by rw [hi,mul_one]
  exact_mod_cast hr

/-- The surviving coarse power is strictly negative for every beta>0. -/
theorem macroscopic_source_re_neg {beta : ℝ} (hb : 0<beta) (k : ℕ) :
    ((Real.rpow (2^k : ℕ) (-beta) : ℂ)*
      response beta (carryCode k) (2^k) (2^k)).re<0 := by
  rw [macroscopic_source hb]
  simp only [Complex.neg_re,Complex.ofReal_re]
  have htwo : (1 : ℝ)<Real.rpow 2 beta := by
    rw [Real.rpow_eq_pow]
    exact Real.one_lt_rpow (by norm_num) hb
  exact neg_neg_of_pos (div_pos (sub_pos.mpr htwo) hb)

/-- Density subtraction has the same exact collapse; the unestimated
arithmetic error is retained, not silently paid as a pole. -/
theorem macroscopic_centering (k : ℕ) (w : ℕ → ℂ) (density : ℂ) :
    (∑ n ∈ Finset.range (2^k),carryCode k (2^k+n)*w (2^k+n))+density=
      -((∑ n ∈ Finset.range (2^k),w (2^k+n))-density) := by
  rw [macroscopic_packet]
  ring

/-- Exact cancellation of the matching height in the diagnostic power
mode. This does not assert an explicit formula for a nonlinear code. -/
theorem matched_power_phase (beta y m : ℝ) (x : ℝ) :
    Complex.exp (-(Complex.I*y)*(Real.log x : ℂ))*
      (-m*Complex.exp (((beta : ℂ)+Complex.I*y-1)*(Real.log x : ℂ)))=
    -m*Complex.exp (((beta : ℂ)-1)*(Real.log x : ℂ)) := by
  calc
    _ = -m*(Complex.exp (-(Complex.I*y)*(Real.log x : ℂ))*
        Complex.exp (((beta : ℂ)+Complex.I*y-1)*(Real.log x : ℂ))) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

/-- The matched exponential is exactly the real power density used in
the cell response; no phase was estimated by absolute values. -/
theorem matched_power_density (beta y m : ℝ) {x : ℝ} (hx : 0<x) :
    Complex.exp (-(Complex.I*y)*(Real.log x : ℂ))*
      (-m*Complex.exp (((beta : ℂ)+Complex.I*y-1)*(Real.log x : ℂ)))=
    -m*(Real.rpow x (beta-1) : ℂ) := by
  rw [matched_power_phase,Real.rpow_eq_pow,Real.rpow_def_of_pos hx,Complex.ofReal_exp]
  congr 2
  push_cast
  ring

/-- Native signs remain exactly involutive after embedding. -/
theorem carryCode_sq (k n : ℕ) : carryCode k n ^ 2=1 := by
  simp only [carryCode,DigitalCarry.highCode,DigitalCarry.epsilon,Int.cast_pow,
    Int.cast_neg,Int.cast_one]
  rw [← pow_mul,Nat.mul_comm _ 2,pow_mul]
  norm_num

/-- A bounded selector can restore the original uncoded channel. Thus
none of the prefix theorems licenses arbitrary correlated masks. -/
theorem selected_mask_ledger (k : ℕ) (I : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ I,((1+carryCode k n)/2)*carryCode k n*w n)=
      ((∑ n ∈ I,carryCode k n*w n)+(∑ n ∈ I,w n))/2 := by
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = (carryCode k n*w n+carryCode k n^2*w n)/2 := by ring
    _ = _ := by rw [carryCode_sq]; ring

end OpenAIReview.DigitalSource

#lint+ in OpenAIReview.DigitalSource

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty moving-source audit."
  logInfo m!"Moving-source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-digital-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-digital-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "exact smooth power response of moving Kummer code; no prime estimate or nonlinear source bridge"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
