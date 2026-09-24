/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszQuintupleHinge
import RiemannGaussian.ZetaRieszOneSidedArithmetic

/-!
# The literal triple/quintuple pair in the direct finite carrier

The triple retains the proved factorial rectangle, its unique second
incidence and the smaller log-share box. The five-prime packet is selected
once per integer from the original nontriple carrier. All original masks,
allocation weights and the full phase remain. No completion is used.
-/

namespace RiemannGaussian.ZetaRieszParityPacket
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszTypeII ZetaRieszWideOwnerAudit
open ZetaRieszAnnulusJoint ZetaRieszSkewAllocation ZetaRieszPrimeEndpoint

/-- The proposed smaller box is a log-share restriction, not a replacement
for the already proved factorial-order rectangle. -/
def lowShareBox (n p r : ℕ) : Prop :=
  21*Real.log n ≤ 40*Real.log p ∧ 200*Real.log p ≤ 113*Real.log n ∧
    Real.log n ≤ 100*Real.log r ∧ 100*Real.log r ≤ 3*Real.log n

/-- The original unique second incidence, all physical prime conditions,
and the proposed smaller logarithmic box. -/
def tripleIncidences (u : ℝ) (N n : ℕ) : Finset ℕ :=
  (rectangleIncidences u N n).filter (fun q => lowShareBox n (largestPrime n) (smallPrime n q))

/-- An actual suballocation of the old rectangle; no positive reserve is
added to the direct carrier. -/
def tripleFraction (u : ℝ) (N K n : ℕ) : ℝ :=
  if n ∈ tripleBand u N K then
    ∑ q ∈ tripleIncidences u N n,
      rectangleMass N (Real.log (n/largestPrime n : ℕ)/Real.log n)
        (Real.log (smallPrime n q)/Real.log (n/largestPrime n : ℕ))
  else 0

theorem tripleFraction_bounds (u : ℝ) (N K n : ℕ) :
    0 ≤ tripleFraction u N K n ∧ tripleFraction u N K n ≤ 1 := by
  unfold tripleFraction
  split_ifs with hn
  · obtain ⟨_, hs, hc⟩ := Finset.mem_filter.mp hn
    have hb (q : ℕ) (hq : q ∈ tripleIncidences u N n) :
        0 ≤ rectangleMass N (Real.log (n/largestPrime n : ℕ)/Real.log n)
          (Real.log (smallPrime n q)/Real.log (n/largestPrime n : ℕ)) ∧
        rectangleMass N (Real.log (n/largestPrime n : ℕ)/Real.log n)
          (Real.log (smallPrime n q)/Real.log (n/largestPrime n : ℕ)) ≤ 1 := by
      have hq' := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      obtain ⟨_, _, _, hx, hr⟩ := second_log_data hs hc hq'
      exact ⟨(rectangleMass_bounds N hx.1 hx.2 hr.1 hr.2).1,
        (rectangleMass_bounds N hx.1 hx.2 hr.1 hr.2).2.trans
          (rectangleMarginal_bounds N hx.1 hx.2).2⟩
    refine ⟨Finset.sum_nonneg (fun q hq => (hb q hq).1), ?_⟩
    have hh := Finset.sum_le_sum (fun q hq => (hb q hq).2)
    have hc' : (tripleIncidences u N n).card ≤ 1 :=
      (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans
        (secondIncidences_card_le_one hs))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      hh.trans (show (∑ _q ∈ tripleIncidences u N n, (1 : ℝ)) ≤ 1 by
        simpa using (show ((tripleIncidences u N n).card : ℝ) ≤ 1 by exact_mod_cast hc'))
  · exact ⟨le_rfl, by norm_num⟩

/-- Literal five-prime labels. Existential prime coordinates cause no
incidence multiplicity: this is a filter of the original integer support. -/
def quintupleBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (narrowBand u N K).filter (fun n => n.primeFactors.card = 5 ∧
    ∃ p a b c r, QuintupleGeometry (SquarefreeVaughanLogSource.length u N) n p a b c r ∧
      lowShareBox n p r ∧ p ∈ intermediatePrimes u N ∧ a ∈ intermediatePrimes u N ∧
      b ∈ intermediatePrimes u N ∧ c ∈ intermediatePrimes u N ∧ r ∈ intermediatePrimes u N)

/-- The five-prime packet belongs to H, not to any completed series. -/
theorem quintupleBand_subset_nontriple (u : ℝ) (N K : ℕ) :
    quintupleBand u N K ⊆ narrowBand u N K \ tripleBand u N K := by
  intro n hn
  obtain ⟨hn, hc, _⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_sdiff.mpr ⟨hn, ?_⟩
  intro ht
  have hthree := (Finset.mem_filter.mp ht).2.2
  omega

/-- The exact quintuple coefficient is nonpositive, before its phase. -/
theorem quintupleBand_coefficient_nonpos {u : ℝ} {N K n : ℕ}
    (hn : n ∈ quintupleBand u N K) :
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n).re ≤ 0 := by
  obtain ⟨_, _, p, a, b, c, r, h, _⟩ := Finset.mem_filter.mp hn
  exact quintuple_coefficient_nonpos (SquarefreeVaughanLogSource.length_pos u N) h

/-- The triple fraction and five-prime indicator have disjoint supports. -/
theorem tripleFraction_eq_zero_on_quintuple {u : ℝ} {N K n : ℕ}
    (hn : n ∈ quintupleBand u N K) : tripleFraction u N K n = 0 := by
  exact if_neg (Finset.mem_sdiff.mp (quintupleBand_subset_nontriple u N K hn)).2

/-- A single suballocation in the actual finite carrier. -/
def packetSelection (u : ℝ) (N K n : ℕ) : ℝ :=
  if n ∈ quintupleBand u N K then 1 else tripleFraction u N K n

theorem packetSelection_bounds (u : ℝ) (N K n : ℕ) :
    0 ≤ packetSelection u N K n ∧ packetSelection u N K n ≤ 1 := by
  unfold packetSelection
  split_ifs
  · exact ⟨by norm_num, le_rfl⟩
  · exact tripleFraction_bounds u N K n

/-- The pair is the sum of its literal original contributions. In
arithmetic-coefficient orientation this is triple minus quintuple mass;
the negative hypothetical-zero triple source is not an arithmetic sign. -/
def packetAtom (u y : ℝ) (N K n : ℕ) : ℂ :=
  (packetSelection u N K n : ℂ) *
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The literal selected sum, before any freezing of its phases. -/
def packetResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ narrowBand u N K, packetAtom u y N K n

/-- The unselected part remains literally present, with its own full phase. -/
def packetRest (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ narrowBand u N K, ((1-packetSelection u N K n : ℝ) : ℂ) *
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem packet_direct_ledger (u y : ℝ) (N K : ℕ) :
    narrowResponse u y N K = packetResponse u y N K + packetRest u y N K := by
  unfold narrowResponse packetResponse packetRest packetAtom
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

/-- The signed real density includes the exact factorial kernel and
old allocation. It is not a count or an absolute-value replacement. -/
def packetDensity (u : ℝ) (N K n : ℕ) : ℝ :=
  packetSelection u N K n *
    ZetaRieszOneSidedArithmetic.weight (intermediatePrimes u N) N n *
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n).re

/-- Positive triple magnitude, including the old factorial suballocation. -/
def tripleDensity (u : ℝ) (N K n : ℕ) : ℝ :=
  tripleFraction u N K n * ZetaRieszOneSidedArithmetic.weight (intermediatePrimes u N) N n *
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n).re

/-- Positive quintuple magnitude. Its minus sign is kept in packetDensity. -/
def quintupleDensity (u : ℝ) (N K n : ℕ) : ℝ :=
  if n ∈ quintupleBand u N K then
    -ZetaRieszOneSidedArithmetic.weight (intermediatePrimes u N) N n *
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n).re
  else 0

theorem quintupleDensity_nonneg (u : ℝ) (N K n : ℕ) : 0 ≤ quintupleDensity u N K n := by
  unfold quintupleDensity
  split_ifs with hn
  · exact mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (ZetaRieszOneSidedArithmetic.weight_nonneg _ _ _))
      (quintupleBand_coefficient_nonpos hn)
  · exact le_rfl

theorem tripleDensity_nonneg (u : ℝ) (N K n : ℕ) : 0 ≤ tripleDensity u N K n := by
  by_cases hn : n ∈ tripleBand u N K
  · obtain ⟨_, hs, hc⟩ := Finset.mem_filter.mp hn
    by_cases hq : (tripleIncidences u N n).Nonempty
    · obtain ⟨q, hq⟩ := hq
      have hq' := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      have hr := second_neg_riesz hs hc hq'
      have hnp : ¬n.Prime := by
        intro hp
        rw [hp.primeFactors, Finset.card_singleton] at hc
        omega
      have hcoeff : 0 ≤ (SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length u N) n).re := by
        rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨hs, hnp⟩, Complex.ofReal_re,
          show -Real.log n*VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n =
            Real.log n*(-VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n) by ring,
          hr]
        exact div_nonneg (mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
          (SquarefreeVaughanLogSource.length_pos u N).le
      exact mul_nonneg (mul_nonneg (tripleFraction_bounds u N K n).1
        (ZetaRieszOneSidedArithmetic.weight_nonneg _ _ _)) hcoeff
    · have he := Finset.not_nonempty_iff_eq_empty.mp hq
      simp [tripleDensity, tripleFraction, hn, he]
  · simp [tripleDensity, tripleFraction, hn]

/-- This signed difference, rather than either absolute mass or a
hypothetical-zero source constant, is what must be compared in each cell. -/
theorem packetDensity_eq_difference (u : ℝ) (N K n : ℕ) :
    packetDensity u N K n = tripleDensity u N K n-quintupleDensity u N K n := by
  unfold packetDensity tripleDensity quintupleDensity packetSelection
  by_cases hn : n ∈ quintupleBand u N K
  · rw [if_pos hn, if_pos hn, tripleFraction_eq_zero_on_quintuple hn]
    ring
  · rw [if_neg hn, if_neg hn, sub_zero]

private theorem coefficient_real (L : ℝ) (n : ℕ) :
    ((SquarefreeVaughanLogSource.coefficient L n).re : ℂ) =
      SquarefreeVaughanLogSource.coefficient L n := by
  apply Complex.ext
  · simp
  · simp [ZetaRieszCosineCarrier.coefficient_im_eq_zero]

/-- Exact complex factorization of each selected atom. -/
theorem packetAtom_eq_density_phase (u y : ℝ) (N K n : ℕ) :
    packetAtom u y N K n = (packetDensity u N K n : ℂ) *
      ZetaArithmeticBandCorrelation.unitPhase (-y*Real.log n) := by
  have he : -((3/2+Complex.I*(y : ℂ))*(Real.log n : ℂ)) =
      ((-(3/2 : ℝ)*Real.log n : ℝ) : ℂ)+Complex.I*((-y*Real.log n : ℝ) : ℂ) := by
    push_cast
    ring
  unfold packetAtom packetDensity residualCoefficient ZetaRieszOneSidedArithmetic.weight
    ZetaRieszOneSidedArithmetic.amplitude zetaPrimeLogKernel zetaPrimeFeature
    ZetaArithmeticBandCorrelation.unitPhase
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  rw [coefficient_real]
  ring

/-- The selected quintuple density is nonpositive; phase is still separate. -/
theorem quintuple_density_nonpos {u : ℝ} {N K n : ℕ} (hn : n ∈ quintupleBand u N K) :
    packetDensity u N K n ≤ 0 := by
  unfold packetDensity
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (packetSelection_bounds u N K n).1
      (ZetaRieszOneSidedArithmetic.weight_nonneg _ _ _)) (quintupleBand_coefficient_nonpos hn)

end
end RiemannGaussian.ZetaRieszParityPacket
