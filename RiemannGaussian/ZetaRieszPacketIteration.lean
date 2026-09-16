/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPacketSupply

/-!
# Repeated packet cancellation with actual remaining fractions

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszPacketIteration
noncomputable section
open scoped BigOperators Classical
open ZetaRieszCycleCore ZetaRieszCycleIteration ZetaRieszCycleCorrelation
open ZetaRieszMassTransport ZetaRieszRetainedFraction ZetaRieszConditionedEnergy
open ZetaRieszPacketCycle
open ZetaRieszPacketSupply

/-- The finite bookkeeping obligations for one original packet cycle. -/
def validPacket (S : Finset ℕ) (e : Finset ℕ × Finset ℕ × Finset ℕ) : Prop :=
  e.1 ⊆ S ∧ e.2.1 ⊆ S ∧ e.2.2 ⊆ S ∧ Disjoint e.1 e.2.1 ∧
    Disjoint e.1 e.2.2 ∧ Disjoint e.2.1 e.2.2

/-- Repeated packet cycles always use the remaining actual original atoms. -/
def packetResidual (f : ℕ → ℂ) : List (Finset ℕ × Finset ℕ × Finset ℕ) → ℕ → ℂ
  | [] => f
  | e :: es => packetResidual (packetStep f e.1 e.2.1 e.2.2) es

/-- All supported packet mass removals accumulate without an error term. -/
def packetTotalSaving (S : Finset ℕ) (f : ℕ → ℂ) : List (Finset ℕ × Finset ℕ × Finset ℕ) → ℝ
  | [] => 0
  | e :: es => packetSaving S f e.1 e.2.1 e.2.2 +
      packetTotalSaving S (packetStep f e.1 e.2.1 e.2.2) es

/-- The total packet saving is nonnegative for every original input. -/
theorem packetTotalSaving_nonneg (S : Finset ℕ) (f : ℕ → ℂ)
    (es : List (Finset ℕ × Finset ℕ × Finset ℕ)) : 0 ≤ packetTotalSaving S f es := by
  induction es generalizing f with
  | nil => exact le_rfl
  | cons e es ih => exact add_nonneg (packetSaving_nonneg ..) (ih _)

/-- Every packet sequence preserves the complete signed original sum. -/
theorem sum_packetResidual (S : Finset ℕ) (f : ℕ → ℂ)
    (es : List (Finset ℕ × Finset ℕ × Finset ℕ))
    (he : ∀ e ∈ es, validPacket S e) :
    (∑ n ∈ S, packetResidual f es n) = ∑ n ∈ S, f n := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨hA, hB, hC, hAB, hAC, hBC⟩ := he e (List.mem_cons_self ..)
    exact (ih _ (fun a ha => he a (List.mem_cons_of_mem _ ha))).trans
      (sum_packetStep S f hA hB hC hAB hAC hBC)

/-- The complete original absolute mass loses exactly the accumulated
packet saving, including all internal group cancellations. -/
theorem mass_packetResidual (S : Finset ℕ) (f : ℕ → ℂ)
    (es : List (Finset ℕ × Finset ℕ × Finset ℕ)) :
    (∑ n ∈ S, ‖packetResidual f es n‖) =
      (∑ n ∈ S, ‖f n‖) - packetTotalSaving S f es := by
  induction es generalizing f with
  | nil => simp [packetResidual, packetTotalSaving]
  | cons e es ih =>
    change (∑ n ∈ S, ‖packetResidual (packetStep f e.1 e.2.1 e.2.2) es n‖) = _
    rw [ih, mass_packetStep]
    simp only [packetTotalSaving]
    ring

/-- Every supported finite packet strategy has a proved whole-sum bound,
retaining all unselected and previously spent original terms. -/
theorem norm_sum_le_packet_total (S : Finset ℕ) (f : ℕ → ℂ)
    (es : List (Finset ℕ × Finset ℕ × Finset ℕ))
    (he : ∀ e ∈ es, validPacket S e) :
    ‖∑ n ∈ S, f n‖ ≤ (∑ n ∈ S, ‖f n‖) - packetTotalSaving S f es := by
  rw [← mass_packetResidual, ← sum_packetResidual S f es he]
  exact norm_sum_le _ _

/-- The literal scalar left on each original atom by a packet sequence. -/
def packetRetainedFraction (f : ℕ → ℂ) : List (Finset ℕ × Finset ℕ × Finset ℕ) → ℕ → ℝ
  | [] => fun _ => 1
  | e :: es => fun n => packetRetainedFraction (packetStep f e.1 e.2.1 e.2.2) es n *
      (1 - packetFraction f e.1 e.2.1 e.2.2 n)

/-- Repeated overlapping packets never restore or duplicate spent mass. -/
theorem packetRetainedFraction_bounds (f : ℕ → ℂ)
    (es : List (Finset ℕ × Finset ℕ × Finset ℕ)) (n : ℕ) :
    0 ≤ packetRetainedFraction f es n ∧ packetRetainedFraction f es n ≤ 1 := by
  induction es generalizing f with
  | nil => exact ⟨zero_le_one, le_rfl⟩
  | cons e es ih =>
    obtain ⟨h0, h1⟩ := packetFraction_bounds f e.1 e.2.1 e.2.2 n
    obtain ⟨hi0, hi1⟩ := ih (packetStep f e.1 e.2.1 e.2.2)
    change 0 ≤ _ * _ ∧ _ * _ ≤ 1
    refine ⟨mul_nonneg hi0 (sub_nonneg.mpr h1), ?_⟩
    exact (mul_le_mul_of_nonneg_right hi1 (sub_nonneg.mpr h1)).trans (by linarith)

/-- Every original ray survives the full packet history with its exact scalar. -/
theorem packetResidual_eq_retainedFraction (f : ℕ → ℂ)
    (es : List (Finset ℕ × Finset ℕ × Finset ℕ)) (n : ℕ) :
    packetResidual f es n = packetRetainedFraction f es n • f n := by
  induction es generalizing f with
  | nil => simp [packetResidual, packetRetainedFraction]
  | cons e es ih =>
    simp only [packetResidual, packetRetainedFraction, ih, packetStep, smul_smul]

/-- The actual full-filter arithmetic supply floor remains valid after
every previous packet cancellation, without taking a common minimum mass. -/
theorem prime_packet_floor_after_packets (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (es : List (Finset ℕ × Finset ℕ × Finset ℕ)) {n : ℕ} {z : ℂ}
    (hn : Squarefree n) (hn1 : n ≠ 1) (hz : ‖z‖ ≤ 1)
    (hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ n)
    (hangle : ∀ q ∈ Q, 0 ≤ area z (ray (bandWeight L P N t (q * n)))) :
    (∑ q ∈ Q, packetRetainedFraction (bandWeight L P N t) es (q * n) *
      (‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t (q * n)‖ *
        max 0 (|ZetaRieszTargetProfile.targetProfile L n x| -
          ZetaRieszFullCycleSupply.cofactorTargetError x q n)) *
        area z (ray (bandWeight L P N t (q * n)))) ≤
      ‖∑ q ∈ Q, packetResidual (bandWeight L P N t) es (q * n)‖ := by
  simp_rw [packetResidual_eq_retainedFraction]
  apply retained_projection_floor Q (fun q => bandWeight L P N t (q * n)) _ _ hz
    (fun q _ => (packetRetainedFraction_bounds _ _ _).1) _ hangle
  intro q hq
  exact ZetaRieszFullCycleSupply.norm_full_prime_partner_ge_cofactor_target
    L x P N t (hQ q hq).1 (hQ q hq).2 hn hn1

/-- Signed packet capacity bounds the full original Riesz band for every
complex polynomial filter and every supported finite packet strategy. -/
theorem norm_actual_band_le_packet_total (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (Finset ℕ × Finset ℕ × Finset ℕ))
    (he : ∀ e ∈ es, validPacket (zetaPrimeLogBand N) e) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      (∑ n ∈ zetaPrimeLogBand N, ‖bandWeight L P N t n‖) -
        packetTotalSaving (zetaPrimeLogBand N) (bandWeight L P N t) es := by
  have hs : (∑ n ∈ zetaPrimeLogBand N, bandWeight L P N t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
    unfold bandWeight zetaArithmeticBand
    exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  rw [← hs]
  exact norm_sum_le_packet_total _ _ es he

/-- Every moving supported packet strategy retains the full pole-jet
source at every right-half zero, without exposure or simplicity. -/
theorem tendsto_full_packet_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (es : ℕ → List (Finset ℕ × Finset ℕ × Finset ℕ))
    (he : ∀ N, ∀ e ∈ es N, validPacket (zetaPrimeLogBand N) e) :
    Filter.Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ n ∈ zetaPrimeLogBand N,
        packetResidual
          (bandWeight (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
            (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) (es N) n)
      Filter.atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hs (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
      (∑ n ∈ zetaPrimeLogBand N, packetResidual (bandWeight L P N t) (es N) n) =
        zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
    rw [sum_packetResidual _ _ _ (he N)]
    unfold bandWeight zetaArithmeticBand
    exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  have h := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  apply h.congr'
  filter_upwards [] with N
  rw [hs]
  push_cast
  rfl
end
end RiemannGaussian.ZetaRieszPacketIteration
