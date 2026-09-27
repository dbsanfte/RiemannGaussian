/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOrderedCapacity
import RiemannGaussian.CertifiedIntervalProgram

/-!
# Checked cap-integral budgets for the signed four/five comparison

The checker encloses the exact capped harmonic integral, including a zero
lower endpoint. Its soundness theorem controls whole parameter cells, not
sampled values. A complete angular cover and the actual prime-population
comparison are separate obligations; the checker alone proves neither.
-/

namespace RiemannGaussian.ZetaRieszCapacityCheck
open LeanCert.Core LeanCert.Engine
open ZetaRieszOrderedCapacity

/-- Rational parameters and proposed bounds on a cap integral. -/
structure Cap where
  /-- Lower endpoint of the least-share integration interval. -/
  a : ℚ
  /-- Upper endpoint of the least-share integration interval. -/
  b : ℚ
  /-- Total share of the two small prime legs. -/
  total : ℚ
  /-- Height of the clipped coefficient. -/
  height : ℚ
  /-- Proposed lower bound on the whole integral. -/
  lower : ℚ
  /-- Proposed upper bound on the whole integral. -/
  upper : ℚ
  deriving Repr

/-- Exact closed-form expression; all divisions of rational parameters
are checked for their intended positive domain by `check`. -/
def expression (c : Cap) : Expr :=
  let seam := max c.a (min c.height c.b)
  .add (.log (.const ((c.total-c.a)/(c.total-seam))))
    (.mul (.const (c.height/c.total))
      (.log (.const (c.b*(c.total-seam)/(seam*(c.total-c.b))))))

/-- Fixed outward-rounded arithmetic. No compiler-trusting evaluation is
used to assert acceptance of any certificate. -/
def config : DyadicConfig := {precision := -40, taylorDepth := 12}

/-- Reject an invalid geometric domain or an unsuccessful interval check. -/
def check (c : Cap) : Bool :=
  decide (0 ≤ c.a ∧ c.a < c.b ∧ c.b < c.total ∧ 0 < c.height) &&
  match evalIntervalDyadicChecked (expression c) (fun _ => default) config with
  | .error _ => false
  | .ok I => decide (c.lower ≤ I.lo.toRat ∧ I.hi.toRat ≤ c.upper)

private theorem expression_eq (c : Cap) :
    Expr.eval (fun _ => 0) (expression c) =
      let seam := max (c.a : ℝ) (min (c.height : ℝ) (c.b : ℝ))
      Real.log (((c.total : ℝ)-c.a)/(c.total-seam))+
        ((c.height : ℝ)/c.total)*Real.log
          ((c.b : ℝ)*(c.total-seam)/(seam*(c.total-c.b))) := by
  simp [expression,Expr.eval,Rat.cast_max,Rat.cast_min]

/-- Every accepted cap certificate encloses its actual real integral.
The numerical computation is connected to the integral by an exact theorem. -/
theorem check_sound {c : Cap} (hc : check c = true) :
    (c.lower : ℝ) ≤
      (∫ x : ℝ in (c.a : ℝ)..(c.b : ℝ), min x (c.height : ℝ)/(x*(c.total-x))) ∧
    (∫ x : ℝ in (c.a : ℝ)..(c.b : ℝ), min x (c.height : ℝ)/(x*(c.total-x))) ≤
      (c.upper : ℝ) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  have ha : (0 : ℝ) ≤ c.a := by exact_mod_cast hc.1.1
  have hab : (c.a : ℝ) < c.b := by exact_mod_cast hc.1.2.1
  have hbS : (c.b : ℝ) < c.total := by exact_mod_cast hc.1.2.2.1
  have hm : (0 : ℝ) < c.height := by exact_mod_cast hc.1.2.2.2
  have hi : (∫ x : ℝ in (c.a : ℝ)..(c.b : ℝ),
      min x (c.height : ℝ)/(x*(c.total-x))) =
      Expr.eval (fun _ => 0) (expression c) := by
    rw [expression_eq]
    rcases ha.eq_or_lt with ha | ha
    · rw [← ha]
      have hb : (0 : ℝ) < c.b := by linarith
      have hseam : max 0 (min (c.height : ℝ) c.b) = min (c.height : ℝ) c.b :=
        max_eq_right (le_min hm.le hb.le)
      simpa only [hseam,sub_zero] using cap_integral_zero_eq hb hbS hm
    · exact cap_integral_eq ha hab.le hbS
  cases he : evalIntervalDyadicChecked (expression c) (fun _ => default) config with
  | error e => simp [he] at hc
  | ok I =>
    have hb : c.lower ≤ I.lo.toRat ∧ I.hi.toRat ≤ c.upper := by
      simpa only [he,decide_eq_true_eq] using hc.2
    have henv : envMemDyadic (fun _ => (0 : ℝ)) (fun _ => default) := by
      intro i
      simp [Membership.mem,default,IntervalDyadic.singleton,
        LeanCert.Core.Dyadic.zero,LeanCert.Core.Dyadic.toRat]
    have hm := evalIntervalDyadicChecked_correct (expression c) _ _ henv config
      (by norm_num [config]) I he
    rw [hi]
    have hl : (c.lower : ℝ) ≤ (I.lo.toRat : ℝ) := by exact_mod_cast hb.1
    have hu : (I.hi.toRat : ℝ) ≤ (c.upper : ℝ) := by exact_mod_cast hb.2
    exact ⟨hl.trans hm.1,hm.2.trans hu⟩

/-- One accepted upper certificate controls every smaller curved fibre
with an enlarged total and reduced cap. -/
theorem integral_le_of_check {c : Cap} (hc : check c = true)
    {a b S m : ℝ} (ha : (c.a : ℝ) ≤ a) (hab : a ≤ b)
    (hb : b ≤ (c.b : ℝ)) (hS : (c.total : ℝ) ≤ S)
    (hm : 0 ≤ m) (hmh : m ≤ (c.height : ℝ)) :
    (∫ x : ℝ in a..b, min x m/(x*(S-x))) ≤ (c.upper : ℝ) := by
  have hg : 0 ≤ c.a ∧ c.a < c.b ∧ c.b < c.total ∧ 0 < c.height := by
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact hc.1
  exact (cap_integral_mono_parameters (by exact_mod_cast hg.1) ha hab hb
    (by exact_mod_cast hg.2.2.1) hS hm hmh).trans (check_sound hc).2

/-- A lower certificate controls every larger fibre with a smaller total
and larger cap. In particular this retains all points inside a supply cell. -/
theorem le_integral_of_check {c : Cap} (hc : check c = true)
    {a b S m : ℝ} (ha : 0 ≤ a) (haa : a ≤ (c.a : ℝ))
    (hbb : (c.b : ℝ) ≤ b) (hbS : b < S) (hS : S ≤ (c.total : ℝ))
    (hm : (c.height : ℝ) ≤ m) :
    (c.lower : ℝ) ≤ ∫ x : ℝ in a..b, min x m/(x*(S-x)) := by
  have hg : 0 ≤ c.a ∧ c.a < c.b ∧ c.b < c.total ∧ 0 < c.height := by
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact hc.1
  exact (check_sound hc).1.trans
    (cap_integral_mono_parameters ha haa (by exact_mod_cast hg.2.1.le) hbb hbS hS
      (by exact_mod_cast hg.2.2.2.le) hm)

private def supplyCap : Cap :=
  ⟨2/25,9/100,29/100,433/10000,31/1250,1/40⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem supplyCap_checked : check supplyCap = true := by decide +kernel

/-- A checked common fibre in the first, tightest cutoff bin has this
strict positive credit, uniformly over the entire outer rectangle. This
is an integral budget, not yet a payment by actual prime labels. -/
theorem first_bin_fibre_credit {v z : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 4401/10000)
    (hz : 27/100 ≤ z ∧ z ≤ 2701/10000) :
    (11/5000 : ℝ) ≤
      ∫ r : ℝ in (2/25 : ℝ)..(9/100 : ℝ),
        min r (max 0 (min (6827/10000-v) (1-3433/5000-z)))/
          (r*(1-v-z-r))*
        Real.log ((v-max (1-v-z-r) (max (1-6827/10000-z) (v-1/2)))/
          max (1-v-z-r) (max (1-6827/10000-z) (v-1/2))) := by
  have hcap : (31/1250 : ℝ) ≤
      ∫ r : ℝ in (2/25 : ℝ)..(9/100 : ℝ), min r (433/10000)/(r*(29/100-r)) := by
    simpa only [supplyCap,Rat.cast_div,Rat.cast_ofNat] using (check_sound supplyCap_checked).1
  have hlog : (9/100 : ℝ) ≤ Real.log ((11/25-21/100)/(21/100)) := by
    have h := (log_rational_bounds_sharp (x := (23/21 : ℝ)) (by norm_num) 2).1
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hbound := five_fibre_lower
    (S := 1-v-z) (S₁ := (29/100 : ℝ))
    (m := max 0 (min (6827/10000-v) (1-3433/5000-z)))
    (m₀ := (433/10000 : ℝ)) (v := v) (v₀ := (11/25 : ℝ))
    (z := z) (lo := (6827/10000 : ℝ)) (d₀ := (21/100 : ℝ))
    (a := (2/25 : ℝ)) (b := (9/100 : ℝ))
    (by norm_num) (by norm_num) (by linarith [hv.2,hz.2])
    (by linarith [hv.1,hz.1]) (by norm_num)
    ((le_min (by linarith [hv.2]) (by linarith [hz.2])).trans (le_max_right _ _))
    hv.1 (by linarith [hv.1,hz.1]) (by linarith [hz.1]) (by linarith [hv.2])
    (by norm_num)
  apply le_trans _ hbound
  calc
    (11/5000 : ℝ) ≤ (9/100)*(31/1250) := by norm_num
    _ ≤ _ := mul_le_mul hlog hcap (by norm_num) (by linarith only [hlog])

end RiemannGaussian.ZetaRieszCapacityCheck
