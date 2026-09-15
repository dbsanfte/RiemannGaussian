/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCompletionRate
import RiemannGaussian.ZetaRieszMatchedMiddle

/-!
# A strictly larger matched head/pair block at the same signed cost

The broader independent completion band gives an actual larger block with
unchanged negative budget and proved persistence. All exposed-zero premises,
full multiplicity and every complementary carrier term remain explicit.
-/

namespace RiemannGaussian.ZetaRieszWiderMatched
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCompletion ZetaRieszPrimeCompletionPhase
open ZetaRieszMatchedMiddle ZetaRieszPrimeCompletionRate
open ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint ZetaExposedPrimeMoments

/-- The actual order band with both prime completion errors paid. -/
def completionOrder (N k : ℕ) : Prop := N ≤ 3 * k ∧ 32 * k ≤ 17 * N

/-- The balanced integer order supplies an eligible default eventually. -/
theorem completionOrder_half (N : ℕ) (hN : 2 ≤ N) : completionOrder N (N / 2) := by
  unfold completionOrder
  omega



/-- The exposed finite phase is uniform over the entire moving order
band. No order-dependent exceptional threshold is discarded. -/
theorem eventually_uniform_finite_phase (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, completionOrder N k →
      ‖weightedFinite (3 / 2 - rho.1.re) rho.1.im N k +
        (analyticZetaZeroMultiplicity rho : ℂ)‖ ≤ ε := by
  apply ZetaRieszInfinitePhysical.eventually_forall_of_all_selections
  intro f
  let k : ℕ → ℕ := fun N => if completionOrder N (f N) then f N else N / 2
  have hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 32 * k N ≤ 17 * N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    change completionOrder N (k N)
    by_cases hf : completionOrder N (f N)
    · simpa only [k, if_pos hf] using hf
    · simpa only [k, if_neg hf] using completionOrder_half N hN
  have h := ((tendsto_wider_weighted_finite rho hrho hexposed huh k hk).add_const
    (analyticZetaZeroMultiplicity rho : ℂ)).norm
  simp only [neg_add_cancel, norm_zero] at h
  filter_upwards [h.eventually (eventually_lt_nhds hε)] with N hN
  intro hf
  simpa only [weightedFinite, k, if_pos hf] using hN.le



/-- Both matched prime products are uniformly close to the same
multiplicity square on every eligible pair of moving orders. -/
theorem eventually_uniform_product_phases (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k l : ℕ,
      completionOrder N k → completionOrder N l → completionOrder N (k + 1) →
      ‖weightedFinite (3 / 2 - rho.1.re) rho.1.im N k *
          weightedFinite (3 / 2 - rho.1.re) rho.1.im N l -
            (analyticZetaZeroMultiplicity rho : ℂ) ^ 2‖ ≤
        (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 24 ∧
      ‖weightedFinite (3 / 2 - rho.1.re) rho.1.im N (k + 1) *
          weightedComplete (3 / 2 - rho.1.re) rho.1.im l -
            (analyticZetaZeroMultiplicity rho : ℂ) ^ 2‖ ≤
        (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 24 := by
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  filter_upwards [eventually_uniform_finite_phase rho hrho hexposed huh
    (ε := (analyticZetaZeroMultiplicity rho : ℝ) / 100) (div_pos hm (by norm_num)),
    eventually_uniform_complete_phase rho hrho hexposed
      (ε := (analyticZetaZeroMultiplicity rho : ℝ) / 100) (div_pos hm (by norm_num))] with N hf hc
  intro k l hk hl hsucc
  constructor
  · exact norm_product_sub_square_le hm.le (hf k hk) (hf l hl)
  · exact norm_product_sub_square_le hm.le (hf (k + 1) hsucc) (hc l hl.1)

/-- The physical head cost is bounded above and below on paired
completion orders. Its lower bound exceeds the pair's coefficient one half. -/
theorem relative_head_cost_bounds {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) (N M k : ℕ)
    (hN : 3 ≤ N) (hNM : N ≤ M) (hkM : k ≤ M)
    (hk : 32 * k ≤ 17 * N) (hl : 32 * (M - k) ≤ 17 * N)
    (hLN : (4 / 3 : ℝ) * N ≤ SquarefreeVaughanLogSource.length u N) :
    5 / 9 ≤ (k : ℝ) / (u * SquarefreeVaughanLogSource.length u N) ∧
      (k : ℝ) / (u * SquarefreeVaughanLogSource.length u N) ≤ 4 / 5 := by
  have hu0 : 0 < u := by linarith
  have hL0 := SquarefreeVaughanLogSource.length_pos u N
  have hup := ZetaRieszHeadAdaptive.annular_radius_le_three_fifths huh
  have hL := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
  have hlog : 2 * Real.log 2 ≤ (45 / 32 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hL45 : SquarefreeVaughanLogSource.length u N ≤ (45 / 32 : ℝ) * N := by
    nlinarith [mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) N)]
  have hupper : u * SquarefreeVaughanLogSource.length u N ≤ (27 / 32 : ℝ) * N := by
    calc
      _ ≤ (3 / 5 : ℝ) * SquarefreeVaughanLogSource.length u N :=
        mul_le_mul_of_nonneg_right hup hL0.le
      _ ≤ (3 / 5 : ℝ) * ((45 / 32 : ℝ) * N) :=
        mul_le_mul_of_nonneg_left hL45 (by norm_num)
      _ = _ := by ring
  have hlower : (2 / 3 : ℝ) * N ≤ u * SquarefreeVaughanLogSource.length u N := by
    nlinarith [mul_le_mul_of_nonneg_right hu hL0.le]
  have hkcast : 32 * (k : ℝ) ≤ 17 * N := by exact_mod_cast hk
  have hlcast : 32 * ((M : ℝ) - k) ≤ 17 * N := by
    simpa only [Nat.cast_sub hkM] using (show 32 * ((M - k : ℕ) : ℝ) ≤ 17 * N by exact_mod_cast hl)
  have hNMcast : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hden : 0 < u * SquarefreeVaughanLogSource.length u N := mul_pos hu0 hL0
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Close complex product phases and the literal relative head cost
give a two-sided signed budget for their matched combination. -/
theorem re_matched_bounds {A B : ℂ} {m r : ℝ}
    (hA : ‖A - (m : ℂ) ^ 2‖ ≤ m ^ 2 / 24)
    (hB : ‖B - (m : ℂ) ^ 2‖ ≤ m ^ 2 / 24)
    (hrl : 5 / 9 ≤ r) (hru : r ≤ 4 / 5) :
    -(17 / 48 : ℝ) * m ^ 2 ≤ (((1 / 2 : ℝ) : ℂ) * A - (r : ℂ) * B).re ∧
      (((1 / 2 : ℝ) : ℂ) * A - (r : ℂ) * B).re ≤ -(5 / 432 : ℝ) * m ^ 2 := by
  have he : ((m : ℂ) ^ 2).re = m ^ 2 := by simp [pow_two]
  have ha := (Complex.abs_re_le_norm (A - (m : ℂ) ^ 2)).trans hA
  have hb := (Complex.abs_re_le_norm (B - (m : ℂ) ^ 2)).trans hB
  rw [Complex.sub_re, he] at ha hb
  obtain ⟨ha0, ha1⟩ := abs_le.mp ha
  obtain ⟨hb0, hb1⟩ := abs_le.mp hb
  have hbpos : 0 ≤ B.re := by nlinarith [sq_nonneg m]
  have hrBhi := mul_le_mul_of_nonneg_right hru hbpos
  have hrBlo := mul_le_mul_of_nonneg_right hrl hbpos
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  constructor <;> nlinarith



/-- A two-sided signed estimate for the actual matched middle atom,
uniform in every eligible pair of orders after one common threshold.
The exposed-zero premises remain explicit; no whole-carrier floor follows. -/
theorem eventually_normalized_sharedAtom_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ M k : ℕ, N ≤ M → k ≤ M →
      completionOrder N k → completionOrder N (M - k) → completionOrder N (k + 1) →
      -(17 / 48 : ℝ) * (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 ≤
        ((k : ℂ) * ((M - k : ℕ) : ℂ) * ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ M *
          sharedAtom (3 / 2 - rho.1.re) rho.1.im N k (M - k)).re ∧
      ((k : ℂ) * ((M - k : ℕ) : ℂ) * ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ M *
          sharedAtom (3 / 2 - rho.1.re) rho.1.im N k (M - k)).re ≤
        -(5 / 432 : ℝ) * (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : (0 : ℝ) < 3 / 2 - rho.1.re := by linarith
  filter_upwards [eventually_uniform_product_phases rho hrho hexposed huh,
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0 (by norm_num : (0 : ℝ) ≤ 2 / 3) huh,
    eventually_ge_atTop 3] with N hproducts hLN hN
  intro M k hNM hkM hk hl hsucc
  obtain ⟨ha, hb⟩ := hproducts k (M - k) hk hl hsucc
  obtain ⟨hrl, hru⟩ := relative_head_cost_bounds hu huh N M k hN hNM hkM hk.2 hl.2 (by nlinarith [hLN])
  have he := normalized_sharedAtom_eq (3 / 2 - rho.1.re) rho.1.im N k (M - k) hu0.ne'
  rw [show k + (M - k) = M by omega] at he
  rw [he]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using
    re_matched_bounds ha hb hrl hru

/-- The unfiltered source's actual matched middle orders. The derivative
successor condition is retained rather than silently shifting the cutoff. -/
def matchedOrders (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 2)).filter (fun k => completionOrder N k ∧
    completionOrder N (N + 1 - k) ∧ completionOrder N (k + 1))

/-- Every selected atom belongs to both original surviving order ranges. -/
theorem matchedOrders_subset_middle (N : ℕ) :
    matchedOrders N ⊆ ZetaRieszPairOrders.middleOrders (N + 1) := by
  intro k hk
  obtain ⟨hkM, hk, hl, _⟩ := Finset.mem_filter.mp hk
  simp only [Finset.mem_range] at hkM
  unfold completionOrder at hk hl
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_range.mpr hkM
  · omega

/-- The exact integer interval contains every actual matched order; this is
an order-count bound, not a fraction of prime mass. -/
theorem matchedOrders_subset_interval (N : ℕ) :
    matchedOrders N ⊆ Finset.Icc (N + 1 - 17 * N / 32) (17 * N / 32 - 1) := by
  intro k hk
  obtain ⟨hkM, hk, hl, hs⟩ := Finset.mem_filter.mp hk
  simp only [Finset.mem_range] at hkM
  unfold completionOrder at hk hl hs
  apply Finset.mem_Icc.mpr
  omega

/-- The cardinality cost of the literal matched block is explicit. -/
theorem matchedOrders_card_bound (N : ℕ) (hN : 256 ≤ N) :
    16 * (matchedOrders N).card ≤ N := by
  have hcard := Finset.card_le_card (matchedOrders_subset_interval N)
  rw [Nat.card_Icc] at hcard
  omega

/-- Each matched order and its complement are positive. -/
theorem matchedOrders_pos {N k : ℕ} (hN : 0 < N) (hk : k ∈ matchedOrders N) :
    0 < k ∧ 0 < N + 1 - k := by
  obtain ⟨_, hk, hl, _⟩ := Finset.mem_filter.mp hk
  unfold completionOrder at hk hl
  omega

/-- The reciprocal factorial weights have a uniform per-order budget. -/
theorem matched_order_weight_le {N k : ℕ} (hN : 256 ≤ N) (hk : k ∈ matchedOrders N) :
    ((N + 1 : ℕ) : ℝ) / ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ)) ≤ 5 / N := by
  obtain ⟨hkpos, hlpos⟩ := matchedOrders_pos (by omega) hk
  obtain ⟨hkM, hk, hl, _⟩ := Finset.mem_filter.mp hk
  simp only [Finset.mem_range] at hkM
  have hkM' : k ≤ N + 1 := by omega
  have hkcast : 32 * (k : ℝ) ≤ 17 * N := by exact_mod_cast hk.2
  have hlcast : 32 * (((N + 1 : ℕ) : ℝ) - k) ≤ 17 * N := by
    simpa only [Nat.cast_sub hkM'] using
      (show 32 * ((N + 1 - k : ℕ) : ℝ) ≤ 17 * N by exact_mod_cast hl.2)
  have hNc : (256 : ℝ) ≤ N := by exact_mod_cast hN
  have hklo : (15 / 32 : ℝ) * N ≤ k := by push_cast at hlcast; nlinarith
  have hllo : (15 / 32 : ℝ) * N ≤ ((N + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkM']
    push_cast
    nlinarith
  have hprod := mul_le_mul hklo hllo (by positivity : (0 : ℝ) ≤ (15 / 32 : ℝ) * N)
    (by exact_mod_cast hkpos.le : (0 : ℝ) ≤ k)
  have hden : (0 : ℝ) < (k : ℝ) * ((N + 1 - k : ℕ) : ℝ) := by positivity
  apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < N)).mpr
  push_cast
  nlinarith

/-- The whole reciprocal-order sum costs at most five sixteenths. -/
theorem matched_order_sum_le (N : ℕ) (hN : 256 ≤ N) :
    (∑ k ∈ matchedOrders N, ((N + 1 : ℕ) : ℝ) /
      ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ))) ≤ 5 / 16 := by
  have hcard : 16 * ((matchedOrders N).card : ℝ) ≤ N := by
    exact_mod_cast matchedOrders_card_bound N hN
  calc
    _ ≤ ∑ _k ∈ matchedOrders N, (5 : ℝ) / N :=
      Finset.sum_le_sum (fun _ hk => matched_order_weight_le hN hk)
    _ = (matchedOrders N).card * (5 : ℝ) / N := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
      have h : (256 : ℝ) ≤ N := by exact_mod_cast hN
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < N)).mpr
      nlinarith

/-- The actual common middle part of the unfiltered prime head and
pair response, with its original product-logarithm prefactor. -/
def matchedBlock (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) * ∑ k ∈ matchedOrders N, sharedAtom u y N k (N + 1 - k)

/-- Source normalization of the whole block retains every reciprocal
order weight. Its real part is a finite signed sum, not an absolute-value surrogate. -/
theorem re_normalized_matchedBlock (u y : ℝ) (N : ℕ) (hN : 0 < N) :
    ((u : ℂ) ^ (N + 1) * matchedBlock u y N).re =
      ∑ k ∈ matchedOrders N, (((N + 1 : ℕ) : ℝ) /
        ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ))) *
          ((k : ℂ) * ((N + 1 - k : ℕ) : ℂ) * (u : ℂ) ^ (N + 1) *
            sharedAtom u y N k (N + 1 - k)).re := by
  unfold matchedBlock
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hkpos, hlpos⟩ := matchedOrders_pos hN hk
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hl0 : ((N + 1 - k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : (u : ℂ) ^ (N + 1) * (((N + 1 : ℕ) : ℂ) * sharedAtom u y N k (N + 1 - k)) =
      ((((N + 1 : ℕ) : ℝ) / ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((k : ℂ) * ((N + 1 - k : ℕ) : ℂ) * (u : ℂ) ^ (N + 1) * sharedAtom u y N k (N + 1 - k)) := by
    push_cast
    field_simp
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The actual matched block is nonempty from this explicit structural
threshold; its later signed estimate is not an empty-support assertion. -/
theorem half_mem_matchedOrders (N : ℕ) (hN : 256 ≤ N) :
    N / 2 ∈ matchedOrders N := by
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_range.mpr (by omega)
  · dsimp only [completionOrder]
    omega

/-- The complete actual matched middle block has a concrete signed
budget at the original source normalization. It is strictly negative,
but no more negative than one eighth of the multiplicity square.
The phase threshold is eventual and depends on the exposed zero. -/
theorem eventually_matchedBlock_re_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 8 ≤
        (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          matchedBlock (3 / 2 - rho.1.re) rho.1.im N).re ∧
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          matchedBlock (3 / 2 - rho.1.re) rho.1.im N).re < 0 := by
  filter_upwards [eventually_normalized_sharedAtom_bounds rho hrho hexposed huh,
    eventually_ge_atTop 256] with N hsource hN
  let m : ℝ := analyticZetaZeroMultiplicity rho
  let w : ℕ → ℝ := fun k => ((N + 1 : ℕ) : ℝ) / ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ))
  let v : ℕ → ℝ := fun k => ((k : ℂ) * ((N + 1 - k : ℕ) : ℂ) *
    ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      sharedAtom (3 / 2 - rho.1.re) rho.1.im N k (N + 1 - k)).re
  have hm : 0 < m := by
    dsimp only [m]
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hw (k : ℕ) (hk : k ∈ matchedOrders N) : 0 < w k := by
    obtain ⟨hkpos, hlpos⟩ := matchedOrders_pos (by omega) hk
    dsimp [w]
    positivity
  have hws : (∑ k ∈ matchedOrders N, w k) ≤ 5 / 16 := matched_order_sum_le N hN
  have hv (k : ℕ) (hk : k ∈ matchedOrders N) :
      -(17 / 48 : ℝ) * m ^ 2 ≤ v k ∧ v k ≤ -(5 / 432 : ℝ) * m ^ 2 := by
    obtain ⟨hkM, hk, hl, hsucc⟩ := Finset.mem_filter.mp hk
    have hkM' : k ≤ N + 1 := by have h := Finset.mem_range.mp hkM; omega
    exact hsource (N + 1) k (by omega) hkM' hk hl hsucc
  rw [re_normalized_matchedBlock _ _ N (by omega)]
  change -m ^ 2 / 8 ≤ (∑ k ∈ matchedOrders N, w k * v k) ∧
    (∑ k ∈ matchedOrders N, w k * v k) < 0
  constructor
  · calc
      _ ≤ (-(17 / 48 : ℝ) * m ^ 2) * ∑ k ∈ matchedOrders N, w k := by
        nlinarith [mul_le_mul_of_nonneg_left hws (by positivity : (0 : ℝ) ≤ (17 / 48) * m ^ 2)]
      _ = ∑ k ∈ matchedOrders N, w k * (-(17 / 48 : ℝ) * m ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ ≤ _ := Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hv k hk).1 (hw k hk).le)
  · calc
      _ < ∑ _k ∈ matchedOrders N, (0 : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty ⟨N / 2, half_mem_matchedOrders N hN⟩
        intro k hk
        have hvneg : v k < 0 := by nlinarith [(hv k hk).2, sq_pos_of_pos hm]
        exact mul_neg_of_pos_of_neg (hw k hk) hvneg
      _ = 0 := by simp

/-- Every matched order also belongs to the literal surviving head. -/
theorem matchedOrders_subset_head (N : ℕ) :
    matchedOrders N ⊆ (Finset.range (N + 2)).filter (fun k => 8 * k < 7 * (N + 1)) := by
  intro k hk
  obtain ⟨hkM, _, hkh⟩ := Finset.mem_filter.mp (matchedOrders_subset_middle N hk)
  exact Finset.mem_filter.mpr ⟨hkM, hkh⟩


/-- The exact unfiltered carrier left after separating the bounded
matched block. Every unpaired arithmetic label and both complementary
factorial-order masks remain explicit, with their original signs. -/
def unmatchedJoint (u y : ℝ) (N : ℕ) : ℂ :=
  ZetaRieszCentralPair.centralUnpairedResponse 1 u y N + ((N + 1 : ℕ) : ℂ) *
    ((1 / 2 : ℂ) * ∑ k ∈ ZetaRieszPairOrders.middleOrders (N + 1) \ matchedOrders N,
      finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) *
        finiteMoment (intermediatePrimes u N) (N + 1 - k) (3 / 2 + Complex.I * y) -
      (1 / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ∑ k ∈ (Finset.range (N + 2)).filter (fun k => 8 * k < 7 * (N + 1)) \ matchedOrders N,
          ((k + 1 : ℕ) : ℂ) *
            finiteMoment (intermediatePrimes u N) (k + 1) (3 / 2 + Complex.I * y) *
              ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y))

/-- The original middle carrier splits into the explicitly retained
unmatched carrier and the actual bounded block, at every original order. -/
theorem middleJoint_one_eq_unmatched_add_matched (u y : ℝ) (N : ℕ) :
    ZetaRieszPairOrders.middleJoint 1 u y N = unmatchedJoint u y N + matchedBlock u y N := by
  have hsupport : (1 : Polynomial ℂ).support = {0} := by
    ext k
    by_cases hk : k = 0 <;> simp [Polynomial.mem_support_iff, Polynomial.coeff_one, hk]
  have hp := Finset.sum_sdiff (f := fun k => finiteMoment (intermediatePrimes u N) k
      (3 / 2 + Complex.I * y) * finiteMoment (intermediatePrimes u N) (N + 1 - k)
        (3 / 2 + Complex.I * y)) (matchedOrders_subset_middle N)
  have hh := Finset.sum_sdiff (f := fun k => ((k + 1 : ℕ) : ℂ) *
      finiteMoment (intermediatePrimes u N) (k + 1) (3 / 2 + Complex.I * y) *
        ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)) (matchedOrders_subset_head N)
  rw [ZetaRieszPairOrders.middleJoint_eq_unpaired_add_form, unmatchedJoint, matchedBlock, sum_sharedAtom_eq]
  simp only [ZetaRieszPairOrders.jointPrimeForm, hsupport,
    Finset.sum_singleton, Polynomial.coeff_one_zero, one_mul, Nat.add_zero]
  rw [← hp, ← hh]
  ring

/-- The two exact remaining pieces together retain the entire exposed
source. The bounded matched block is retained; no decay is asserted. -/
theorem tendsto_unmatched_add_matched_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (unmatchedJoint (3 / 2 - rho.1.re) rho.1.im N +
        matchedBlock (3 / 2 - rho.1.re) rho.1.im N))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simpa only [middleJoint_one_eq_unmatched_add_matched] using
    ZetaRieszPairOrders.tendsto_middleJoint_exposed rho hrho hexposed huh

/-- The larger block contains every previously bounded matched order.
The original successor condition is preserved on both sides. -/
theorem old_matchedOrders_subset (N : ℕ) :
    ZetaRieszMatchedMiddle.matchedOrders N ⊆ matchedOrders N := by
  intro k hk
  obtain ⟨hkM, hk, hl, hs⟩ := Finset.mem_filter.mp hk
  apply Finset.mem_filter.mpr
  refine ⟨hkM, ?_⟩
  dsimp only [completionOrder]
  dsimp only [ZetaRieszMatchedMiddle.completionOrder] at hk hl hs
  omega

/-- An explicit interior integer interval inside the actual matched block. -/
def interiorOrders (N : ℕ) : Finset ℕ :=
  Finset.Icc (15 * N / 32 + 2) (17 * N / 32 - 2)

/-- Both completion endpoints and the shifted head order hold on the
entire interior interval, not only at one selected middle order. -/
theorem interiorOrders_subset (N : ℕ) (hN : 256 ≤ N) :
    interiorOrders N ⊆ matchedOrders N := by
  intro k hk
  obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_range.mpr (by omega)
  · dsimp only [completionOrder]
    omega

/-- The matched block contains a definite number of distinct orders. -/
theorem matchedOrders_card_lower (N : ℕ) (hN : 256 ≤ N) :
    N ≤ 32 * (matchedOrders N).card := by
  have hcard := Finset.card_le_card (interiorOrders_subset N hN)
  rw [interiorOrders, Nat.card_Icc] at hcard
  omega

/-- Complementary positive factorial orders have a quantitative lower
reciprocal weight, with their original total order retained. -/
theorem matched_order_weight_lower {N k : ℕ} (hN : 0 < N) (hk : k ∈ matchedOrders N) :
    (2 : ℝ) / N ≤ ((N + 1 : ℕ) : ℝ) / ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ)) := by
  obtain ⟨hkpos, hlpos⟩ := matchedOrders_pos hN hk
  have hkM : k ≤ N + 1 := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    omega
  have hM : (k : ℝ) + ((N + 1 - k : ℕ) : ℝ) = (N + 1 : ℕ) := by
    rw [Nat.cast_sub hkM]
    ring
  have hNc : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hprod : 4 * (k : ℝ) * ((N + 1 - k : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((k : ℝ) - ((N + 1 - k : ℕ) : ℝ))]
  have hupper : ((N + 1 : ℕ) : ℝ) ≤ 2 * N := by push_cast; linarith
  have hs := mul_le_mul_of_nonneg_left hupper (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < N) (by positivity)).mpr
  nlinarith

/-- The exact reciprocal-order sum has a positive fixed lower bound. -/
theorem matched_order_sum_lower (N : ℕ) (hN : 256 ≤ N) :
    (1 / 16 : ℝ) ≤ ∑ k ∈ matchedOrders N, ((N + 1 : ℕ) : ℝ) /
      ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ)) := by
  have hcard : (N : ℝ) ≤ 32 * ((matchedOrders N).card : ℝ) := by
    exact_mod_cast matchedOrders_card_lower N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (matchedOrders N).card * (2 : ℝ) / N := by
      apply (le_div_iff₀ hN0).mpr
      nlinarith
    _ = ∑ _k ∈ matchedOrders N, (2 : ℝ) / N := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun _ hk => matched_order_weight_lower (by omega) hk)

/-- Actual order density makes the source-conditioned negative block
persist at a fixed fraction of the multiplicity square. -/
theorem eventually_matchedBlock_persistent_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 8 ≤
        (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          matchedBlock (3 / 2 - rho.1.re) rho.1.im N).re ∧
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          matchedBlock (3 / 2 - rho.1.re) rho.1.im N).re ≤
        -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 1536 := by
  filter_upwards [eventually_normalized_sharedAtom_bounds rho hrho hexposed huh,
    eventually_matchedBlock_re_bounds rho hrho hexposed huh,
    eventually_ge_atTop 256] with N hsource hblock hN
  refine ⟨hblock.1, ?_⟩
  let m : ℝ := analyticZetaZeroMultiplicity rho
  let w : ℕ → ℝ := fun k => ((N + 1 : ℕ) : ℝ) / ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ))
  let v : ℕ → ℝ := fun k => ((k : ℂ) * ((N + 1 - k : ℕ) : ℂ) *
    ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      sharedAtom (3 / 2 - rho.1.re) rho.1.im N k (N + 1 - k)).re
  have hw (k : ℕ) : 0 ≤ w k := by dsimp [w]; positivity
  have hws : (1 / 16 : ℝ) ≤ ∑ k ∈ matchedOrders N, w k := matched_order_sum_lower N hN
  have hv (k : ℕ) (hk : k ∈ matchedOrders N) : v k ≤ -(5 / 432 : ℝ) * m ^ 2 := by
    obtain ⟨hkM, hk, hl, hsucc⟩ := Finset.mem_filter.mp hk
    have hkM' : k ≤ N + 1 := by have h := Finset.mem_range.mp hkM; omega
    exact (hsource (N + 1) k (by omega) hkM' hk hl hsucc).2
  rw [re_normalized_matchedBlock _ _ N (by omega)]
  change (∑ k ∈ matchedOrders N, w k * v k) ≤ -m ^ 2 / 1536
  calc
    _ ≤ ∑ k ∈ matchedOrders N, w k * (-(5 / 432 : ℝ) * m ^ 2) :=
      Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hv k hk) (hw k))
    _ = (-(5 / 432 : ℝ) * m ^ 2) * ∑ k ∈ matchedOrders N, w k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hws (by positivity : (0 : ℝ) ≤ (5 / 432) * m ^ 2)]

/-- Under the same hypothetical zero, the actual matched block cannot
be discarded as a vanishing error in the source normalization. -/
theorem not_tendsto_matchedBlock_zero (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ¬ Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      matchedBlock (3 / 2 - rho.1.re) rho.1.im N) atTop (nhds 0) := by
  intro hzero
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hzero
  have hle := le_of_tendsto hre
    ((eventually_matchedBlock_persistent_bounds rho hrho hexposed huh).mono fun _ h => h.2)
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  simp only [Complex.zero_re] at hle
  nlinarith [sq_pos_of_pos hm]

/-- Removing the persistent block changes the original source: the
complement alone cannot retain the full negative multiplicity limit. -/
theorem not_tendsto_unmatched_full_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ¬ Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      unmatchedJoint (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  intro hsource
  apply not_tendsto_matchedBlock_zero rho hrho hexposed huh
  have h := (tendsto_unmatched_add_matched_exposed rho hrho hexposed huh).sub hsource
  simpa only [mul_add, add_sub_cancel_left, sub_self] using h


/-- A concrete order belongs to the enlarged block and is excluded by
the old successor cut, proving actual strict enlargement. -/
theorem wider_order_not_old (N : ℕ) (hN : 256 ≤ N) :
    17 * N / 32 - 1 ∈ matchedOrders N ∧
      17 * N / 32 - 1 ∉ ZetaRieszMatchedMiddle.matchedOrders N := by
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · dsimp only [completionOrder]
      omega
  · intro h
    obtain ⟨_, _, _, hsucc⟩ := Finset.mem_filter.mp h
    dsimp only [ZetaRieszMatchedMiddle.completionOrder] at hsucc
    omega


end
end RiemannGaussian.ZetaRieszWiderMatched
