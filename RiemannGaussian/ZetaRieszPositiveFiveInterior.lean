/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFivePositiveHead
import RiemannGaussian.ZetaRieszCapacityPhaseBudget
import RiemannGaussian.ZetaRieszCapacityCheck

/-!
# The exact positive-five interior debit

The ordered cofactor hinge is retained before any harmonic integration.
The moving physical length stays in a sharper rational bin near the
actual factorial saddle. These inequalities target the remaining literal
positive-five cost; they do not assert its unproved complete integral budget.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveInterior
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- The actual floor-dependent length stays in the narrow bin suggested
by the quantitative probe, throughout a bounded-width saddle window. -/
theorem eventually_saddle_cutoff_ratio {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 2*(N : ℝ)-1 ≤ t → t ≤ 2*N+1 →
      (693/1000 : ℝ) ≤ SquarefreeVaughanLogSource.length u N/t ∧
      SquarefreeVaughanLogSource.length u N/t ≤ 1733/2500 := by
  have hUr : ZetaRieszWideOwnerAudit.radiusCeiling < Real.exp (-(27721/40000 : ℝ)) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mp
    have h := Real.log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (0 : ℝ) < 2*ZetaRieszWideOwnerAudit.radiusCeiling)
    rw [Real.log_mul (by norm_num) (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])] at h
    dsimp [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    linarith [Real.log_two_gt_d9]
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 27721/40000)
    (hU.trans_lt hUr),eventually_ge_atTop (20000 : ℕ)] with N hlo hN t ht htu
  have hn : (20000 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 < t := by linarith
  have hhi := ZetaRieszHeadOrders.length_le_two_log_two hu (show 2 ≤ N by omega)
  constructor
  · apply (le_div_iff₀ ht0).mpr
    nlinarith only [hlo,htu,hn]
  · apply (div_le_iff₀ ht0).mpr
    nlinarith [Real.log_two_lt_d9]

/-- Sorting the four cofactor logarithms evaluates their positive
balance with every saturation chamber and every boundary retained. -/
theorem ordered_balance_eq {q a b r d : ℝ} (hrb : r ≤ b) (hba : b ≤ a) (haq : a ≤ q) :
    min d q+min d a+min d b+min d r-3*d =
      min d (min r (min (r+b-d) (min (r+b+a-2*d) (r+b+a+q-3*d)))) := by
  rcases le_total d r with h | h
  · simp only [min_eq_left (h.trans (hrb.trans (hba.trans haq))),
      min_eq_left (h.trans (hrb.trans hba)),min_eq_left (h.trans hrb),min_eq_left h]
    rw [min_eq_left (le_min h (le_min (by linarith) (le_min (by linarith) (by linarith))))]
    ring
  rcases le_total d b with h' | h'
  · rw [min_eq_left (h'.trans (hba.trans haq)),min_eq_left (h'.trans hba),
      min_eq_left h',min_eq_right h]
    rw [min_eq_left (show r ≤ min (r+b-d) (min (r+b+a-2*d) (r+b+a+q-3*d)) from
      le_min (by linarith) (le_min (by linarith) (by linarith))),min_eq_right h]
    ring
  rcases le_total d a with h'' | h''
  · rw [min_eq_left (h''.trans haq),min_eq_left h'',min_eq_right h',min_eq_right h]
    rw [min_eq_left (show r+b-d ≤ min (r+b+a-2*d) (r+b+a+q-3*d) from
      le_min (by linarith) (by linarith)),min_eq_right (by linarith : r+b-d ≤ r),
      min_eq_right (by linarith : r+b-d ≤ d)]
    ring
  rcases le_total d q with h''' | h'''
  · rw [min_eq_left h''',min_eq_right h'',min_eq_right h',min_eq_right h]
    rw [min_eq_left (by linarith : r+b+a-2*d ≤ r+b+a+q-3*d),
      min_eq_right (by linarith : r+b+a-2*d ≤ r+b-d),
      min_eq_right (by linarith : r+b+a-2*d ≤ r),
      min_eq_right (by linarith : r+b+a-2*d ≤ d)]
    ring
  · rw [min_eq_right h''',min_eq_right h'',min_eq_right h',min_eq_right h]
    rw [min_eq_right (by linarith : r+b+a+q-3*d ≤ r+b+a-2*d),
      min_eq_right (by linarith : r+b+a+q-3*d ≤ r+b-d),
      min_eq_right (by linarith : r+b+a+q-3*d ≤ r),
      min_eq_right (by linarith : r+b+a+q-3*d ≤ d)]
    ring

/-- The least-prime fibre is a translated cap. The translation retains
the pair and triple deficits that a least-log norm bound would lose. -/
theorem ordered_balance_eq_shifted_cap {q a b r d : ℝ}
    (hrb : r ≤ b) (hba : b ≤ a) (haq : a ≤ q) :
    max 0 (min d q+min d a+min d b+min d r-3*d) =
      max 0 (min (r-max 0 (max (d-b) (2*d-b-a))) (min d (r+b+a+q-3*d))) := by
  rw [ordered_balance_eq hrb hba haq]
  have he : r-max 0 (max (d-b) (2*d-b-a)) =
      min r (min (r+b-d) (r+b+a-2*d)) := by
    simp only [max_def,min_def]
    split_ifs <;> linarith
  rw [he]
  congr 1
  ac_rfl

/-- The translated cap is exactly a difference of two ordinary caps.
The pair deficit is subtracted before harmonic integration. -/
theorem shifted_cap_eq_cap_sub {x r c : ℝ} (hc : 0 ≤ c) :
    max 0 (min (x-r) c) = min x (r+c)-min x r := by
  rcases le_total x r with h | h
  · rw [min_eq_left (show x ≤ r+c by linarith),min_eq_left h,
      min_eq_left (by linarith : x-r ≤ c),max_eq_left (by linarith)]
    ring
  rcases le_total x (r+c) with h' | h'
  · rw [min_eq_left h',min_eq_right h,min_eq_left (by linarith),
      max_eq_right (by linarith)]
  · rw [min_eq_right h',min_eq_right h,min_eq_right (by linarith),max_eq_right hc]
    ring

/-- Exact harmonic integration retains the translated-cap cancellation,
including the integrable zero endpoint. -/
theorem shifted_cap_integral_eq {a b S r c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbS : b < S) (hr : 0 ≤ r) (hc : 0 ≤ c) :
    (∫ x : ℝ in a..b, max 0 (min (x-r) c)/(x*(S-x))) =
      (∫ x : ℝ in a..b, min x (r+c)/(x*(S-x)))-
      (∫ x : ℝ in a..b, min x r/(x*(S-x))) := by
  have hbig := ZetaRieszOrderedCapacity.cap_integrable_nonneg ha hab hbS (add_nonneg hr hc)
  have hsmall := ZetaRieszOrderedCapacity.cap_integrable_nonneg ha hab hbS hr
  rw [← intervalIntegral.integral_sub hbig hsmall]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [shifted_cap_eq_cap_sub hc,sub_div]

/-- Two kernel-checked harmonic cap certificates bound their difference
without destroying the pair-deficit subtraction. This controls the entire
curved fibre, rather than sampled least-prime shares. -/
theorem checked_shifted_cap_integral_le (c : ZetaRieszCapacityCheck.Cap)
    (r lower upper : ℚ) (hc : ZetaRieszCapacityCheck.check c = true)
    (hs : ZetaRieszCapacityCheck.check {c with height := r, lower := lower, upper := upper} = true)
    (hr : r ≤ c.height) :
    (∫ x : ℝ in (c.a : ℝ)..(c.b : ℝ),
      max 0 (min (x-r) ((c.height : ℝ)-r))/(x*((c.total : ℝ)-x))) ≤
      (c.upper : ℝ)-lower := by
  have hg : 0 ≤ c.a ∧ c.a < c.b ∧ c.b < c.total ∧ 0 < c.height := by
    simp only [ZetaRieszCapacityCheck.check,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact hc.1
  have hr0 : (0 : ℝ) ≤ r := by
    have hgr : 0 < r := by
      simp only [ZetaRieszCapacityCheck.check,Bool.and_eq_true,decide_eq_true_eq] at hs
      exact hs.1.2.2.2
    exact_mod_cast hgr.le
  rw [shifted_cap_integral_eq (by exact_mod_cast hg.1) (by exact_mod_cast hg.2.1.le)
    (by exact_mod_cast hg.2.2.1) hr0 (by exact_mod_cast sub_nonneg.mpr hr)]
  have hu := (ZetaRieszCapacityCheck.check_sound hc).2
  have hl := (ZetaRieszCapacityCheck.check_sound hs).1
  rw [show (r : ℝ)+((c.height : ℝ)-r) = c.height by ring]
  exact sub_le_sub hu hl

/-- Positivity forces the exact three outer-coordinate restrictions
used by the interior cubature. No broad coefficient norm is substituted. -/
theorem positive_cap_root_bounds {p q a b r lam : ℝ}
    (hrb : r ≤ b) (haq : a ≤ q) (htotal : p+q+a+b+r = 1)
    (hpos : 0 < max 0 (min (lam-p) (min r (min (r+b-(lam-p))
      (min (r+b+a-2*(lam-p)) (r+b+a+q-3*(lam-p))))))) :
    (3*lam-1)/2 < p ∧ (lam-p)/2 < b ∧ a < (1-lam)/2 := by
  have hf : 0 < min (lam-p) (min r (min (r+b-(lam-p))
      (min (r+b+a-2*(lam-p)) (r+b+a+q-3*(lam-p))))) :=
    (lt_max_iff.mp hpos).resolve_left (lt_irrefl _)
  rcases lt_min_iff.mp hf with ⟨_,hf⟩
  rcases lt_min_iff.mp hf with ⟨_,hf⟩
  rcases lt_min_iff.mp hf with ⟨hpair,hf⟩
  rcases lt_min_iff.mp hf with ⟨_,hfull⟩
  constructor
  · linarith only [htotal,hfull]
  constructor <;> linarith only [htotal,hpair,hrb,haq]

/-- Exact evaluation of the positive part of the actual five-prime
coefficient in sorted cofactor coordinates. No original mask is changed. -/
theorem positive_coefficient_eq_cap {n q a b r : ℕ} (hs : Squarefree n)
    (hcount : n.primeFactors.card = 5)
    (hcofactor : n.primeFactors.erase (ZetaRieszPrimeEndpoint.largestPrime n) = {q,a,b,r})
    (hrb : r < b) (hba : b < a) (haq : a < q)
    {L : ℝ} (hL : 0 < L) (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) :
    let d := L-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)
    max 0 (SquarefreeVaughanLogSource.coefficient L n).re =
      (Real.log n/L)*max 0 (min (Real.log r-max 0 (max (d-Real.log b)
        (2*d-Real.log b-Real.log a))) (min d
        (Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-3*d))) := by
  let P := ZetaRieszPrimeEndpoint.largestPrime n
  have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hP : P ∈ n.primeFactors := by
    dsimp [P]
    rw [ZetaRieszPrimeEndpoint.largestPrime,dif_pos hne]
    exact Finset.max'_mem _ _
  have hq : q ≠ a := by omega
  have hqb : q ≠ b := by omega
  have hqr : q ≠ r := by omega
  have hab : a ≠ b := by omega
  have har : a ≠ r := by omega
  have hbr : b ≠ r := by omega
  have hlog := Finset.sum_erase_add n.primeFactors (fun p : ℕ => Real.log p) hP
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs,hcofactor] at hlog
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    hq,hqb,hqr,hab,har,hbr,or_self,not_false_eq_true] at hlog
  have hr0 : 0 < (r : ℝ) := by
    have hrmem : r ∈ n.primeFactors := Finset.mem_of_mem_erase (by rw [hcofactor]; simp)
    exact_mod_cast (Nat.prime_of_mem_primeFactors hrmem).pos
  have hba0 : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have haa0 : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hrlog : Real.log (r : ℝ) ≤ Real.log b :=
    Real.log_le_log hr0 (by exact_mod_cast hrb.le)
  have hbalog : Real.log (b : ℝ) ≤ Real.log a :=
    Real.log_le_log hba0 (by exact_mod_cast hba.le)
  have haqlog : Real.log (a : ℝ) ≤ Real.log q :=
    Real.log_le_log haa0 (by exact_mod_cast haq.le)
  have hm (x d : ℝ) : min d x = x-max 0 (x-d) := by
    simp only [min_def,max_def]
    split_ifs <;> linarith
  have hbalance := ordered_balance_eq_shifted_cap hrlog hbalog haqlog
    (d := L-Real.log P)
  have htotal : Real.log (r : ℝ)+Real.log b+Real.log a+Real.log q =
      Real.log n-Real.log P := by linarith only [hlog]
  rw [htotal] at hbalance
  conv_lhs at hbalance => rw [hm,hm,hm,hm]
  rw [← ZetaRieszFivePrimeReserve.positiveAllowance_eq hcount hL hLlo hLhi]
  simp only [ZetaRieszFivePrimeReserve.positiveAllowance,if_pos hs,hcofactor,
    Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    hq,hqb,hqr,hab,har,hbr,or_self,not_false_eq_true]
  congr 1
  convert hbalance using 1
  congr 1
  dsimp [P] at hlog ⊢
  linarith only [hlog]

end
end RiemannGaussian.ZetaRieszPositiveFiveInterior
