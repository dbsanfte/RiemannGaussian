/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaAdjacentRatio
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredTailSharpAsymptotic

/-!
# Eta tail bounds uniform in the ordinate

Exact neighboring ratios sum the alternating phases before any absolute
estimate. Their variation telescopes, giving a bound by `2 X^(-Re(s))`
once the physical cutoff `X` is at least `norm(s)`. The complete complex
boundary multiplier and signed remainder remain available.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Set Topology
open scoped Classical

/-- The complex endpoint after exact adjacent-ratio summation. -/
def pairedEtaAdjacentBoundary (s : ℂ) (x : ℝ) : ℂ :=
  pairedEtaAdjacentInverse s x * (x : ℂ) ^ (-s)

/-- The full two-step signed variation remainder, retaining both complex
power values and the inverse multiplier at all three neighboring points. -/
def pairedEtaAdjacentDefect (s : ℂ) (x : ℝ) : ℂ :=
  (pairedEtaAdjacentInverse s x - pairedEtaAdjacentInverse s (x + 1)) *
      ((x + 1 : ℝ) : ℂ) ^ (-s) +
  (pairedEtaAdjacentInverse s (x + 2) - pairedEtaAdjacentInverse s (x + 1)) *
      ((x + 2 : ℝ) : ℂ) ^ (-s)

/-- One actual paired power difference is a boundary difference plus
the exact signed variation of the adjacent multiplier. -/
theorem cpow_pair_eq_adjacent_boundary_add_defect (s : ℂ) {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    (x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s) =
      pairedEtaAdjacentBoundary s x - pairedEtaAdjacentBoundary s (x + 2) +
        pairedEtaAdjacentDefect s x := by
  have h1 := pairedEtaAdjacentInverse_mul_add s hx hscale
  have h2 := pairedEtaAdjacentInverse_mul_add s
    (show 0 < x + 1 by linarith) (show ‖s‖ ≤ x + 1 by linarith)
  rw [show x + 1 + 1 = x + 2 by ring] at h2
  unfold pairedEtaAdjacentBoundary pairedEtaAdjacentDefect
  linear_combination -h1 + h2

/-- The exact boundary has no height factor in its norm. -/
theorem norm_pairedEtaAdjacentBoundary_le {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    ‖pairedEtaAdjacentBoundary s x‖ ≤ x ^ (-s.re) := by
  rw [pairedEtaAdjacentBoundary, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  simpa using mul_le_mul_of_nonneg_right
    (norm_pairedEtaAdjacentInverse_le_one hx hscale) (Real.rpow_nonneg hx.le _)

/-- Coupling the two inverse differences makes their exact logarithmic
cost telescope across a full pair. The common initial endpoint controls
the power amplitudes throughout the retained tail. -/
theorem norm_pairedEtaAdjacentDefect_le {s : ℂ} (hs : 0 ≤ s.re)
    {X x : ℝ} (hX : 0 < X) (hscale : ‖s‖ ≤ X) (hx : X ≤ x) :
    ‖pairedEtaAdjacentDefect s x‖ ≤
      ‖s‖ * X ^ (-s.re) * (pairedEtaStepLog x - pairedEtaStepLog (x + 2)) := by
  have hx0 := hX.trans_le hx
  have h1 := norm_pairedEtaAdjacentInverse_sub_le hs hx0 (hscale.trans hx)
    (show x ≤ x + 1 by linarith)
  have h2 := norm_pairedEtaAdjacentInverse_sub_le hs
    (show 0 < x + 1 by linarith) (show ‖s‖ ≤ x + 1 by linarith)
    (show x + 1 ≤ x + 2 by linarith)
  rw [norm_sub_rev] at h1
  have hp (u : ℝ) (hu : X ≤ u) : ‖(u : ℂ) ^ (-s)‖ ≤ X ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hX.trans_le hu), Complex.neg_re]
    exact Real.rpow_le_rpow_of_nonpos hX hu (neg_nonpos.mpr hs)
  unfold pairedEtaAdjacentDefect
  calc
    _ ≤ _ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul]
    _ ≤ (‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog (x + 1))) * X ^ (-s.re) +
        (‖s‖ * (pairedEtaStepLog (x + 1) - pairedEtaStepLog (x + 2))) * X ^ (-s.re) := by
      exact add_le_add
        (mul_le_mul h1 (hp (x + 1) (by linarith)) (norm_nonneg _) ((norm_nonneg _).trans h1))
        (mul_le_mul h2 (hp (x + 2) (by linarith)) (norm_nonneg _) ((norm_nonneg _).trans h2))
    _ = _ := by ring

/-- The exact partial eta tail retains its two endpoint phases and every
interior signed variation term. -/
theorem pairedEtaCorePartialSum_sub_eq_adjacent (s : ℂ) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    pairedEtaCorePartialSum (M + N) s - pairedEtaCorePartialSum N s =
      pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ) -
        pairedEtaAdjacentBoundary s ((2 * (M + N) + 1 : ℕ) : ℝ) +
      ∑ n ∈ Finset.range M, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hx : ((2 * N + 1 : ℕ) : ℝ) ≤ ((2 * (M + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
    have h := cpow_pair_eq_adjacent_boundary_add_defect s
      (x := ((2 * (M + N) + 1 : ℕ) : ℝ)) (by positivity) (hscale.trans hx)
    have hη : pairedEtaCorePartialSum (M + 1 + N) s =
        pairedEtaCorePartialSum (M + N) s + pairedEtaCoreSummand s (M + N) := by
      rw [show M + 1 + N = (M + N) + 1 by omega]
      exact Finset.sum_range_succ _ _
    rw [hη, Finset.sum_range_succ]
    have hn : 2 * (M + 1 + N) + 1 = (2 * (M + N) + 1) + 2 := by omega
    rw [hn]
    simp only [pairedEtaCoreSummand] at h ⊢
    push_cast at h ih ⊢
    rw [show (2 * ((M : ℂ) + N) + 1 + 1 : ℂ) = 2 * ((M : ℂ) + N) + 2 by ring] at h
    linear_combination ih + h

private theorem sum_norm_adjacent_defect_le {s : ℂ} (hs : 0 ≤ s.re) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑ n ∈ Finset.range M,
      ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        (pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) -
          pairedEtaStepLog ((2 * (M + N) + 1 : ℕ) : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hx : ((2 * N + 1 : ℕ) : ℝ) ≤ ((2 * (M + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
    have h := norm_pairedEtaAdjacentDefect_le hs (by positivity) hscale hx
    rw [Finset.sum_range_succ]
    have hn : 2 * (M + 1 + N) + 1 = (2 * (M + N) + 1) + 2 := by omega
    rw [hn]
    push_cast at h ih ⊢
    calc
      _ ≤ _ := add_le_add ih h
      _ = _ := by ring

private theorem sum_norm_adjacent_defect_le_const {s : ℂ} (hs : 0 ≤ s.re) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑ n ∈ Finset.range M,
      ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) := by
  apply (sum_norm_adjacent_defect_le hs N M hscale).trans
  apply mul_le_mul_of_nonneg_left
    (sub_le_self _ (pairedEtaStepLog_bounds (by positivity)).1)
  positivity

/-- The complete signed inverse-variation remainder is absolutely
convergent on every safe physical tail, uniformly allowing large ordinates. -/
theorem summable_pairedEtaAdjacentDefect_tail {s : ℂ} (hs : 0 ≤ s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    Summable (fun n : ℕ => pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)) := by
  apply Summable.of_norm
  exact summable_of_sum_range_le (fun _ => norm_nonneg _)
    (fun M => sum_norm_adjacent_defect_le_const hs N M hscale)

/-- The entire absolute variation cost is controlled by one exact
logarithmic step at the starting endpoint. -/
theorem tsum_norm_pairedEtaAdjacentDefect_tail_le {s : ℂ} (hs : 0 ≤ s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑' n : ℕ, ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
    (fun M => sum_norm_adjacent_defect_le_const hs N M hscale)

private theorem tendsto_adjacent_boundary_zero {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    Tendsto (fun M : ℕ => pairedEtaAdjacentBoundary s ((2 * (M + N) + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun M : ℕ => ((2 * (M + N) + 1 : ℕ) : ℝ) ^ (-s.re))
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · apply Filter.Eventually.of_forall
    intro M
    apply norm_pairedEtaAdjacentBoundary_le (by positivity)
    apply hscale.trans
    exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
  · exact (tendsto_pairedEtaOddEndpoint_rpow_zero hs).comp (tendsto_add_atTop_nat N)

/-- Exact adjacent-ratio summation of the actual infinite eta tail.
The boundary keeps the full complex phase and the signed remainder is
proved absolutely convergent before passing to the limit. -/
theorem pairedEtaCore_tail_eq_adjacent {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    pairedEtaCore s - pairedEtaCorePartialSum N s =
      pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ) +
        ∑' n : ℕ, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  have he := ((summable_pairedEtaCoreSummand hs).tendsto_sum_tsum_nat.comp
    (tendsto_add_atTop_nat N)).sub_const (pairedEtaCorePartialSum N s)
  change Tendsto (fun M => pairedEtaCorePartialSum (M + N) s - pairedEtaCorePartialSum N s)
    atTop (nhds (pairedEtaCore s - pairedEtaCorePartialSum N s)) at he
  simp_rw [pairedEtaCorePartialSum_sub_eq_adjacent s N _ hscale] at he
  have hb := tendsto_adjacent_boundary_zero hs N hscale
  have hr := (summable_pairedEtaAdjacentDefect_tail hs.le N hscale).tendsto_sum_tsum_nat
  have ht := ((tendsto_const_nhds
    (x := pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ))).sub hb).add hr
  simpa using tendsto_nhds_unique he ht

/-- The full complex error after exact adjacent summation costs only one
norm of the ordinate-bearing argument times one logarithmic step. -/
theorem norm_pairedEtaCore_tail_sub_adjacent_le {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s -
        pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ)‖ ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) := by
  rw [pairedEtaCore_tail_eq_adjacent hs N hscale, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm (summable_pairedEtaAdjacentDefect_tail hs.le N hscale).norm).trans
    (tsum_norm_pairedEtaAdjacentDefect_tail_le hs.le N hscale)

/-- The entire actual eta tail has a height-independent constant once
the physical cutoff is at least the norm of the complex argument. -/
theorem norm_pairedEtaCore_tail_le_two {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      2 * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  let X : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hX : 0 < X := by dsimp [X]; positivity
  have hl := pairedEtaStepLog_bounds hX
  have hbudget : ‖s‖ * pairedEtaStepLog X ≤ 1 := by
    calc
      _ ≤ X * (1 / X) := mul_le_mul hscale hl.2 hl.1 hX.le
      _ = 1 := by field_simp
  rw [pairedEtaCore_tail_eq_adjacent hs N hscale]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ X ^ (-s.re) + ‖s‖ * X ^ (-s.re) * pairedEtaStepLog X :=
      add_le_add (norm_pairedEtaAdjacentBoundary_le hX hscale)
        ((norm_tsum_le_tsum_norm (summable_pairedEtaAdjacentDefect_tail hs.le N hscale).norm).trans
          (tsum_norm_pairedEtaAdjacentDefect_tail_le hs.le N hscale))
    _ ≤ 2 * X ^ (-s.re) := by
      have h := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hX.le (-s.re))
      nlinarith only [h]

/-- At any actual nontrivial zero, a cutoff at least its complex norm
forces the literal finite eta sum below the same uniform power bound. -/
theorem norm_pairedEtaCorePartialSum_zero_le_two (rho : NontrivialZetaZero) (N : ℕ)
    (hscale : ‖rho.1‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    ‖pairedEtaCorePartialSum N rho.1‖ ≤
      2 * (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) := by
  have h := norm_pairedEtaCore_tail_le_two (NontrivialZetaZero.zero_lt_re rho) N hscale
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    (NontrivialZetaZero.zero_lt_re rho) rho.2.2.2, rho.2.1, mul_zero, zero_sub, norm_neg] at h
  exact h

/-- Complex endpoint normalization preserves the exact adjacent multiplier
and removes the power amplitude from the full signed remainder estimate. -/
theorem norm_pairedEtaCoreNormalizedTail_sub_adjacent_le {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    ‖pairedEtaCoreNormalizedTail N s - pairedEtaAdjacentInverse s ((2 * N + 1 : ℕ) : ℝ)‖ ≤
      ‖s‖ * pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) := by
  let X : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hX : 0 < X := by dsimp [X]; positivity
  have hc : (X : ℂ) ^ s * (X : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) (Complex.ofReal_ne_zero.mpr hX.ne'),
      add_neg_cancel, Complex.cpow_zero]
  have he : pairedEtaCoreNormalizedTail N s - pairedEtaAdjacentInverse s X =
      (X : ℂ) ^ s * (pairedEtaCore s - pairedEtaCorePartialSum N s -
        pairedEtaAdjacentBoundary s X) := by
    unfold pairedEtaCoreNormalizedTail
    change (X : ℂ) ^ s * (pairedEtaCore s - pairedEtaCorePartialSum N s) -
      pairedEtaAdjacentInverse s X = _
    unfold pairedEtaAdjacentBoundary
    linear_combination (pairedEtaAdjacentInverse s X) * hc
  change ‖pairedEtaCoreNormalizedTail N s - pairedEtaAdjacentInverse s X‖ ≤ _
  rw [he, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  have h := norm_pairedEtaCore_tail_sub_adjacent_le hs N hscale
  have hp : X ^ s.re * X ^ (-s.re) = 1 := by
    rw [← Real.rpow_add hX, add_neg_cancel, Real.rpow_zero]
  calc
    _ ≤ X ^ s.re * (‖s‖ * X ^ (-s.re) * pairedEtaStepLog X) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hX.le _)
    _ = ‖s‖ * pairedEtaStepLog X * (X ^ s.re * X ^ (-s.re)) := by ring
    _ = _ := by rw [hp, mul_one]

/-- The normalized actual eta tail approaches the Euler half endpoint
with a cost linear in `norm(s)/X`, uniformly for growing ordinates and
cutoffs. The preceding theorem retains its richer complex multiplier. -/
theorem norm_pairedEtaCoreNormalizedTail_sub_half_le_scale {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    ‖pairedEtaCoreNormalizedTail N s - 1 / 2‖ ≤
      3 * ‖s‖ / (2 * ((2 * N + 1 : ℕ) : ℝ)) := by
  let X : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hX : 0 < X := by dsimp [X]; positivity
  have h1 := norm_pairedEtaCoreNormalizedTail_sub_adjacent_le hs N hscale
  have h2 := norm_pairedEtaAdjacentInverse_sub_half_le hs.le hX hscale
  have ht := norm_sub_le_norm_sub_add_norm_sub (pairedEtaCoreNormalizedTail N s)
    (pairedEtaAdjacentInverse s X) (1 / 2)
  have hl := mul_le_mul_of_nonneg_left (pairedEtaStepLog_bounds hX).2 (norm_nonneg s)
  change ‖pairedEtaCoreNormalizedTail N s - 1 / 2‖ ≤ 3 * ‖s‖ / (2 * X)
  calc
    _ ≤ ‖s‖ * pairedEtaStepLog X + ‖s‖ * pairedEtaStepLog X / 2 :=
      ht.trans (add_le_add h1 h2)
    _ ≤ (3 / 2) * (‖s‖ * (1 / X)) := by linarith
    _ = _ := by ring

/-- The Euler half endpoint is uniform along arbitrary moving complex
arguments and cutoffs when the cutoff dominates the argument norm. The
ordinates may be unbounded and the real parts need not stay in a compact
subinterval of the positive half-plane. -/
theorem tendsto_pairedEtaCoreNormalizedTail_of_norm_div_endpoint_zero
    {α : Type*} {l : Filter α} {s : α → ℂ} {N : α → ℕ}
    (hs : ∀ᶠ i in l, 0 < (s i).re)
    (hratio : Tendsto (fun i => ‖s i‖ / ((2 * N i + 1 : ℕ) : ℝ)) l (nhds 0)) :
    Tendsto (fun i => pairedEtaCoreNormalizedTail (N i) (s i)) l (nhds (1 / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (g := fun i => (3 / 2 : ℝ) * (‖s i‖ / ((2 * N i + 1 : ℕ) : ℝ)))
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [hs, hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi hsmall
    have hX : (0 : ℝ) < ((2 * N i + 1 : ℕ) : ℝ) := by positivity
    have hscale : ‖s i‖ ≤ ((2 * N i + 1 : ℕ) : ℝ) := by
      have h := (div_lt_iff₀ hX).mp hsmall
      linarith
    apply (norm_pairedEtaCoreNormalizedTail_sub_half_le_scale hi (N i) hscale).trans_eq
    ring
  · simpa using hratio.const_mul (3 / 2 : ℝ)

end
end RiemannGaussian
