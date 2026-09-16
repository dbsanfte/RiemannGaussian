/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTransportPhase
import RiemannGaussian.ZetaRieszTransportCoverage

/-!
# The whole original source in the transported pair sum

Every sent pair and remaining original amplitude stays explicit. Complete
fallback coverage controls the final unsent mass, but all fallback chord
costs remain in the whole bound. A source-scale bound for the sent sum and
a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszTransportSource
noncomputable section
open scoped BigOperators Classical
open ZetaRieszMassTransport
open ZetaRieszTransportCoverage

/-- Literal candidate membership discharges the support and distinctness
premises without restricting repeated use of a remaining vertex. -/
theorem prime_edges_valid {N : ℕ} (es : List (ℕ × ℕ))
    (he : ∀ e ∈ es, e ∈ ZetaRieszPrimeMatching.primePairEdges N) :
    ∀ e ∈ es, e.1 ∈ zetaPrimeLogBand N ∧ e.2 ∈ zetaPrimeLogBand N ∧ e.1 ≠ e.2 := by
  intro e hes
  have h := he e hes
  simp only [ZetaRieszPrimeMatching.primePairEdges, Finset.mem_filter, Finset.mem_product] at h
  exact ⟨h.1.1, h.1.2, h.2.1⟩

/-- The entire original carrier is bounded by a finite partial-mass
transport with all pair costs proved from its actual amplitudes. -/
theorem actual_band_le_transportCost (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ))
    (he : ∀ e ∈ es, e ∈ ZetaRieszPrimeMatching.primePairEdges N) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      transportCost (zetaPrimeLogBand N) (ZetaRieszConditionedEnergy.bandWeight L P N t) es := by
  have hs : (∑ n ∈ zetaPrimeLogBand N, ZetaRieszConditionedEnergy.bandWeight L P N t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
    unfold ZetaRieszConditionedEnergy.bandWeight zetaArithmeticBand
    exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  rw [← hs]
  exact norm_sum_le_transportCost _ _ _ (prime_edges_valid es he)

/-- The canonical list of every eligible original prime pair supplies a
fully defined bound; there is no unproved coverage or transport premise. -/
theorem actual_band_le_all_prime_transport (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      transportCost (zetaPrimeLogBand N) (ZetaRieszConditionedEnergy.bandWeight L P N t)
        (ZetaRieszPrimeMatching.primePairEdges N).toList := by
  exact actual_band_le_transportCost L P N t _ (fun _ he => Finset.mem_toList.mp he)

/-- Any finite sequence of distinct original labels can be used, including
prime-to-product and cross-prime-count pairs. No selection of coefficients
or arithmetic cancellation premise enters this whole-carrier estimate. -/
theorem actual_band_le_supported_transport (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ zetaPrimeLogBand N ∧ e.2 ∈ zetaPrimeLogBand N ∧ e.1 ≠ e.2) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      transportCost (zetaPrimeLogBand N) (ZetaRieszConditionedEnergy.bandWeight L P N t) es := by
  have hs : (∑ n ∈ zetaPrimeLogBand N, ZetaRieszConditionedEnergy.bandWeight L P N t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
    unfold ZetaRieszConditionedEnergy.bandWeight zetaArithmeticBand
    exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  rw [← hs]
  exact norm_sum_le_transportCost _ _ _ he

/-- The literal prime-pair phase stage followed by complete fallback
gives one fully specified upper bound for the entire original carrier.
No unmatched mass or fallback chord cost is omitted. -/
theorem actual_band_le_completed_prime_transport (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      transportCost (zetaPrimeLogBand N) (ZetaRieszConditionedEnergy.bandWeight L P N t)
        ((ZetaRieszPrimeMatching.primePairEdges N).toList ++ fullPairList (zetaPrimeLogBand N)) := by
  apply actual_band_le_supported_transport
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact prime_edges_valid _ (fun _ hh => Finset.mem_toList.mp hh) e h
  · exact fullPairList_valid _ e h

/-- The fully specified transported complex sum differs from the original
carrier by a uniformly controlled source-normalized error tending to zero.
Every pair interaction is retained in the sent sum before taking its norm. -/
theorem tendsto_actual_band_sub_sent (P : Polynomial ℂ) (height : ℕ → ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N)) P N (height N) -
      sentAfter (ZetaRieszConditionedEnergy.bandWeight (SquarefreeVaughanLogSource.length u N) P N (height N))
        ((ZetaRieszPrimeMatching.primePairEdges N).toList ++ fullPairList (zetaPrimeLogBand N))))
      Filter.atTop (nhds 0) := by
  have he := tendsto_actual_remaining_mass P height
    (fun N => (ZetaRieszPrimeMatching.primePairEdges N).toList) hu hu1
  apply squeeze_zero_norm (fun N => ?_) he
  let S := zetaPrimeLogBand N
  let f := ZetaRieszConditionedEnergy.bandWeight (SquarefreeVaughanLogSource.length u N) P N (height N)
  let es := (ZetaRieszPrimeMatching.primePairEdges N).toList ++ fullPairList S
  have hv : ∀ e ∈ es, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact prime_edges_valid _ (fun _ hh => Finset.mem_toList.mp hh) e h
    · exact fullPairList_valid _ e h
  have hs : (∑ n ∈ S, f n) = zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N)) P N (height N) := by
    unfold f S ZetaRieszConditionedEnergy.bandWeight zetaArithmeticBand
    exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  have hid := sum_eq_sent_add_remaining S f es hv
  rw [hs] at hid
  have hd : zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N)) P N (height N) - sentAfter f es =
      ∑ n ∈ S, remainingAfter f es n := by rw [hid]; ring
  change ‖(u : ℂ) ^ (N + 1) * (_ - sentAfter f es)‖ ≤ _
  rw [hd, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  exact mul_le_mul_of_nonneg_left (norm_sum_le S (fun n => remainingAfter f es n)) (pow_nonneg hu.le _)

/-- Every right-half zero would force the fully transported signed pair
sum to retain its full negative multiplicity. The unmatched error is paid
on the entire source interval; an independent bound for the sent sum or
its accumulated chord costs remains open. -/
theorem tendsto_actual_sent_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Filter.Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      sentAfter (ZetaRieszConditionedEnergy.bandWeight
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
        ((ZetaRieszPrimeMatching.primePairEdges N).toList ++ fullPairList (zetaPrimeLogBand N)))
      Filter.atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have he := tendsto_actual_band_sub_sent (zetaRightHalfPoleJetFilter rho hrho)
    (fun _ => rho.1.im) hu hu1
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  rw [hcast] at he
  have h := (SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho).sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [hcast]
  ring
end
end RiemannGaussian.ZetaRieszTransportSource
