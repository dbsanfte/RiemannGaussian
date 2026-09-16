/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFullCycleSupply
import RiemannGaussian.ZetaRieszCycleIteration

/-!
# A proved arithmetic budget for the whole original carrier

Exact target profiles, original complex directions and separately retained
capacities give proved arithmetic cycle budgets. All failed tests and
remaining original terms stay accounted for. Sufficient aggregate saving
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszArithmeticCycles
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTransportPhase ZetaRieszConditionedEnergy
open ZetaRieszTargetProfile
open ZetaRieszRetainedFraction
open ZetaRieszCycleCapacity
open ZetaRieszFullCycleSupply

/-- The two partner labels determine their actual gcd and prime
quotients. The central original label is left unrestricted. -/
def partnerArithmeticTest (e : ℕ × ℕ × ℕ) : Prop :=
  let g := Nat.gcd e.2.1 e.2.2
  (e.2.1 / g).Prime ∧ (e.2.2 / g).Prime ∧
    ¬ (e.2.1 / g) ∣ g ∧ ¬ (e.2.2 / g) ∣ g ∧
    Squarefree g ∧ g ≠ 1

/-- Every actual original triple receives a fully specified arithmetic
saving budget. It retains the exact midpoint target profile, the complete
polynomial directions and the separate remaining capacities. Failed
arithmetic or orientation tests receive zero saving, not a deleted term. -/
def arithmeticCycleBudget (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (processed : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) : ℝ :=
  let f := bandWeight L P N t
  let g := Nat.gcd e.2.1 e.2.2
  let q := e.2.1 / g
  let r := e.2.2 / g
  let x := (Real.log q + Real.log r) / 2
  if partnerArithmeticTest e ∧ ZetaRieszCycleCore.positiveCycle (f e.1) (f e.2.1) (f e.2.2) then
    rayCapacity (ZetaRieszMassTransport.ray (f e.1)) (ZetaRieszMassTransport.ray (f e.2.1))
      (ZetaRieszMassTransport.ray (f e.2.2))
      (retainedFraction f processed e.1 * ‖f e.1‖)
      (retainedFraction f processed e.2.1 *
        (‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t e.2.1‖ *
          max 0 (|targetProfile L g x| - cofactorTargetError x q g)))
      (retainedFraction f processed e.2.2 *
        (‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t e.2.2‖ *
          max 0 (|targetProfile L g x| - cofactorTargetError x r g))) *
      (ZetaRieszCycleCore.area (ZetaRieszMassTransport.ray (f e.2.1)) (ZetaRieszMassTransport.ray (f e.2.2)) +
       ZetaRieszCycleCore.area (ZetaRieszMassTransport.ray (f e.2.2)) (ZetaRieszMassTransport.ray (f e.1)) +
       ZetaRieszCycleCore.area (ZetaRieszMassTransport.ray (f e.1)) (ZetaRieszMassTransport.ray (f e.2.1)))
  else 0

/-- The guard makes every arithmetic budget nonnegative, including
all ineligible triples and exhausted previous capacities. -/
theorem arithmeticCycleBudget_nonneg (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (processed : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) :
    0 ≤ arithmeticCycleBudget L P N t processed e := by
  unfold arithmeticCycleBudget
  dsimp only
  split_ifs with he
  · have hc := positiveCycle_ray he.2
    apply mul_nonneg
    · apply rayCapacity_nonneg hc
      · exact mul_nonneg (retainedFraction_bounds _ _ _).1 (norm_nonneg _)
      · exact mul_nonneg (retainedFraction_bounds _ _ _).1
          (mul_nonneg (norm_nonneg _) (le_max_left _ _))
      · exact mul_nonneg (retainedFraction_bounds _ _ _).1
          (mul_nonneg (norm_nonneg _) (le_max_left _ _))
    · exact add_nonneg (add_nonneg hc.1.le hc.2.1.le) hc.2.2.le
  · exact le_rfl

/-- The complete arithmetic budget is proved from the original finite
data, with no residual capacity or cancellation premise. -/
theorem arithmeticCycleBudget_le_saving (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (processed : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) :
    arithmeticCycleBudget L P N t processed e ≤
      ZetaRieszCycleCore.cycleSaving
        (ZetaRieszCycleIteration.cycleResidual (bandWeight L P N t) processed e.1)
        (ZetaRieszCycleIteration.cycleResidual (bandWeight L P N t) processed e.2.1)
        (ZetaRieszCycleIteration.cycleResidual (bandWeight L P N t) processed e.2.2) := by
  unfold arithmeticCycleBudget
  dsimp only
  split_ifs with he
  · obtain ⟨hq, hr, hqg, hrg, hg, hg1⟩ := he.1
    have hqeq : (e.2.1 / Nat.gcd e.2.1 e.2.2) * Nat.gcd e.2.1 e.2.2 = e.2.1 :=
      Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    have hreq : (e.2.2 / Nat.gcd e.2.1 e.2.2) * Nat.gcd e.2.1 e.2.2 = e.2.2 :=
      Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hc : ZetaRieszCycleCore.positiveCycle (bandWeight L P N t e.1)
        (bandWeight L P N t ((e.2.1 / Nat.gcd e.2.1 e.2.2) * Nat.gcd e.2.1 e.2.2))
        (bandWeight L P N t ((e.2.2 / Nat.gcd e.2.1 e.2.2) * Nat.gcd e.2.1 e.2.2)) := by
      simpa only [hqeq, hreq] using he.2
    have hb := full_cycle_after_previous_ge_cofactor_target L
      ((Real.log (e.2.1 / Nat.gcd e.2.1 e.2.2 : ℕ) + Real.log (e.2.2 / Nat.gcd e.2.1 e.2.2 : ℕ)) / 2)
      P N t processed e.1 hq hr hqg hrg hg hg1 hc
    simpa only [hqeq, hreq] using hb
  · exact ZetaRieszCycleCore.cycleSaving_nonneg _ _ _

/-- Accumulate the proved arithmetic budgets with the actual processed of
every step. A later term receives only its truly remaining capacity. -/
def arithmeticSavings (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (processed : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) → ℝ
  | [] => 0
  | e :: es => arithmeticCycleBudget L P N t processed e +
      arithmeticSavings L P N t (processed ++ [e]) es

/-- The entire explicitly defined arithmetic budget is nonnegative. -/
theorem arithmeticSavings_nonneg (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (processed es : List (ℕ × ℕ × ℕ)) : 0 ≤ arithmeticSavings L P N t processed es := by
  induction es generalizing processed with
  | nil => exact le_rfl
  | cons e es ih => exact add_nonneg (arithmeticCycleBudget_nonneg _ _ _ _ _ _) (ih _)

/-- All local arithmetic budgets add to a certified lower bound for
the exact saving of the actual successive cycles. -/
theorem arithmeticSavings_le_totalSaving (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (processed es : List (ℕ × ℕ × ℕ)) :
    arithmeticSavings L P N t processed es ≤
      ZetaRieszCycleIteration.totalSaving
        (ZetaRieszCycleIteration.cycleResidual (bandWeight L P N t) processed) es := by
  induction es generalizing processed with
  | nil => exact le_rfl
  | cons e es ih =>
    have hn := ih (processed ++ [e])
    rw [cycleResidual_append] at hn
    change _ ≤ ZetaRieszCycleIteration.totalSaving
      (ZetaRieszCycleIteration.cycleStep
        (ZetaRieszCycleIteration.cycleResidual (bandWeight L P N t) processed) e) es at hn
    exact add_le_add (arithmeticCycleBudget_le_saving _ _ _ _ _ _) hn

/-- The whole original full-polynomial carrier receives an independent,
fully specified arithmetic saving budget, retaining every failed test,
remaining term and previous spent fraction. Sufficient source-scale
control of this complete upper bound is the outstanding global task. -/
theorem norm_actual_band_le_arithmetic_cycles (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      (∑ n ∈ zetaPrimeLogBand N, ‖bandWeight L P N t n‖) -
        arithmeticSavings L P N t [] (ZetaRieszCycleIteration.actualCycles N).toList := by
  have ha := arithmeticSavings_le_totalSaving L P N t []
    (ZetaRieszCycleIteration.actualCycles N).toList
  change _ ≤ ZetaRieszCycleIteration.totalSaving (bandWeight L P N t)
    (ZetaRieszCycleIteration.actualCycles N).toList at ha
  exact (ZetaRieszCycleIteration.norm_actual_band_le_exact_cycles L P N t).trans
    (sub_le_sub_left ha _)


/-- Every finite original support slice receives the same proved
arithmetic budget, with all unselected terms retained and every actual
cycle label checked. This does not assume positive aggregate saving. -/
theorem norm_actual_subset_le_arithmetic_list (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (S : Finset ℕ) (es : List (ℕ × ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.2.2 ∈ S ∧ ZetaRieszCycleIteration.distinctTriple e) :
    ‖∑ n ∈ S, bandWeight L P N t n‖ ≤
      (∑ n ∈ S, ‖bandWeight L P N t n‖) - arithmeticSavings L P N t [] es := by
  have ha := arithmeticSavings_le_totalSaving L P N t [] es
  change _ ≤ ZetaRieszCycleIteration.totalSaving (bandWeight L P N t) es at ha
  exact (ZetaRieszCycleIteration.norm_sum_le_total_saving S (bandWeight L P N t) es he).trans
    (sub_le_sub_left ha _)

/-- All original supported cycle lists, including prime-count-crossing
lists, receive the whole-carrier arithmetic bound for every full filter.
Only finite support bookkeeping remains in the list hypothesis. -/
theorem norm_actual_band_le_arithmetic_list (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ))
    (he : ∀ e ∈ es, e ∈ ZetaRieszCycleIteration.actualCycles N) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      (∑ n ∈ zetaPrimeLogBand N, ‖bandWeight L P N t n‖) - arithmeticSavings L P N t [] es := by
  have hs : (∑ n ∈ zetaPrimeLogBand N, bandWeight L P N t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
    unfold bandWeight zetaArithmeticBand
    exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  rw [← hs]
  exact norm_actual_subset_le_arithmetic_list L P N t (zetaPrimeLogBand N) es
    (fun e he' => ZetaRieszCycleIteration.actualCycles_valid (he e he'))


/-- The canonical arithmetic stage tests every original triple but
processes only those with a strictly positive independently proved initial
budget. Uncredited geometric steps cannot spend its later partner supply. -/
@[irreducible] def availableArithmeticCycles (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    Finset (ℕ × ℕ × ℕ) :=
  (ZetaRieszCycleIteration.actualCycles N).filter (fun e => 0 < arithmeticCycleBudget L P N t [] e)

/-- Every available arithmetic cycle retains three distinct original
labels and an independently positive initial local saving. -/
theorem availableArithmeticCycles_valid {L : ℝ} {P : Polynomial ℂ} {N : ℕ} {t : ℝ}
    {e : ℕ × ℕ × ℕ} (he : e ∈ availableArithmeticCycles L P N t) :
    e ∈ ZetaRieszCycleIteration.actualCycles N ∧ 0 < arithmeticCycleBudget L P N t [] e := by
  simpa only [availableArithmeticCycles, Finset.mem_filter] using he

/-- The entire original carrier has one fully specified arithmetic bound
after the available initial tests, with its full complex polynomial and
all unselected mass retained. No coverage or aggregate saving is assumed. -/
theorem norm_actual_band_le_available_arithmetic_cycles (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      (∑ n ∈ zetaPrimeLogBand N, ‖bandWeight L P N t n‖) -
        arithmeticSavings L P N t [] (availableArithmeticCycles L P N t).toList := by
  exact norm_actual_band_le_arithmetic_list L P N t _
    (fun _ he => (availableArithmeticCycles_valid (Finset.mem_toList.mp he)).1)

/-- The available arithmetic cycles retain the complete source at every
hypothetical right-half zero, using its full pole-jet polynomial without
exposure or simplicity. The independent aggregate bound remains open. -/
theorem tendsto_available_arithmetic_cycle_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Filter.Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ n ∈ zetaPrimeLogBand N,
        ZetaRieszCycleIteration.cycleResidual
          (bandWeight (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
            (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
          (availableArithmeticCycles (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
            (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im).toList n)
      Filter.atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hs (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
      (∑ n ∈ zetaPrimeLogBand N,
        ZetaRieszCycleIteration.cycleResidual (bandWeight L P N t)
          (availableArithmeticCycles L P N t).toList n) =
        zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
    rw [ZetaRieszCycleIteration.sum_cycleResidual _ _ _ (fun _ he =>
      ZetaRieszCycleIteration.actualCycles_valid
        (availableArithmeticCycles_valid (Finset.mem_toList.mp he)).1)]
    unfold bandWeight zetaArithmeticBand
    exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  have h := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  apply h.congr'
  filter_upwards [] with N
  rw [hs]
  push_cast
  rfl
end
end RiemannGaussian.ZetaRieszArithmeticCycles
