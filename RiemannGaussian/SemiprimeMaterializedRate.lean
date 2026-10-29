/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeScheduledSupportRate
import RiemannGaussian.SemiprimeScheduledCounter

/-! # Aggregate rate for the actual materialized public counter

This bounds a resource envelope, not an implementation's running time. The
literal support count and scheduled summary/head/arity bounds are retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace RiemannGaussian.SemiprimeMaterializedRate
open Filter
open scoped Topology
open SemiprimeCounterRate SemiprimeSourceLayoutRate SemiprimeScheduledSupportRate

/-- Exact integer-log decay used by the scheduled source summary bound. -/
def decay (lam : ℕ) : ℝ := (Nat.clog 2 lam : ℝ)^2 / Real.sqrt (lam : ℝ)

/-- The actual ceiling-log expression, rather than a smooth surrogate, vanishes. -/
theorem decay_zero : Tendsto decay atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := (tendsto_rpow_neg_atTop (show (0 : ℝ)<1/4 by norm_num)).comp hn
  apply squeeze_zero' (Eventually.of_forall (fun n => by dsimp [decay]; positivity)) ?_ hl
  filter_upwards [eventually_clog_power_le_rpow 2 (1/4) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n h hpos
  have hp : (0 : ℝ)<n := Nat.cast_pos.mpr (by omega)
  have he : (n : ℝ)^(1/4 : ℝ)/Real.sqrt (n : ℝ)=(n : ℝ)^(-(1/4) : ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_sub hp]
    norm_num
  change (Nat.clog 2 n : ℝ)^2 / Real.sqrt (n : ℝ)≤(n : ℝ)^(-(1/4) : ℝ)
  rw [← he]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- Actual summary envelope from the proved total-rank estimate. -/
def summaryEnvelope (n : ℕ) : ℝ :=
  Real.exp (48*(n : ℝ)*decay (Nat.clog 2 n)*Real.log 2)

/-- The original head bound, rounded upward only in the real exponent. -/
def headEnvelope (n : ℕ) : ℝ :=
  Real.exp ((2*(n : ℝ)/scheduledGroupCount (Nat.clog 2 n))*Real.log 2)

/-- Degree-d polynomial preprocessing plus literal supports and the public
summary, head and growing-scope truth-table envelopes. -/
def budget (d n : ℕ) : ℝ := (n : ℝ)^d +
  SemiprimeCounterEnumeration.weightedCount n (cutoff n) + summaryEnvelope n +
  headEnvelope n + Real.exp (512*(n : ℝ)^(3/4 : ℝ)*Real.log 2)

/-- Every prescribed exponential rate absorbs the scheduled summary bound. -/
theorem summary_subexponential (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, summaryEnvelope n≤Real.exp (ε*(n : ℝ)) := by
  have hl := ((decay_zero.comp tendsto_clog_two_atTop).const_mul (48*Real.log 2))
  simp only [mul_zero] at hl
  filter_upwards [hl.eventually (gt_mem_nhds hε)] with n hn
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hn.le (show (0 : ℝ)≤n by positivity)
  simp only [Function.comp_apply] at hm
  convert hm using 1
  ring

/-- The actual head exponent is dominated by the source summary envelope. -/
theorem eventually_head_le_summary :
    ∀ᶠ n : ℕ in atTop, headEnvelope n≤ summaryEnvelope n := by
  filter_upwards [(tendsto_clog_two_atTop.comp tendsto_clog_two_atTop).eventually
    (eventually_ge_atTop 64)] with n hn
  have hi := source_inverse_group_budget hn
  apply Real.exp_le_exp.mpr
  dsimp [headEnvelope,summaryEnvelope,decay]
  have hh := mul_le_mul_of_nonneg_left hi (show (0 : ℝ)≤2*n by positivity)
  have hlog := Real.log_nonneg (show (1 : ℝ)≤2 by norm_num)
  have hm := mul_le_mul_of_nonneg_right hh hlog
  have hnon : (0 : ℝ)≤(n : ℝ)*(Nat.clog 2 (Nat.clog 2 n) : ℝ)^2 /
      Real.sqrt (Nat.clog 2 n : ℝ)*Real.log 2 := by positivity
  ring_nf at hm hnon ⊢
  linarith

/-- A fixed polynomial in the graph size is absorbed without a unit-cost
arithmetic premise. This is only the numerical envelope. -/
theorem polynomial_subexponential (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^d≤Real.exp (ε*(n : ℝ)) := by
  have h := tendsto_natCast_atTop_atTop.eventually (eventually_polynomial_exp_rho_le (d : ℝ) 0 ε hε)
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hpos
  simpa [Real.rpow_natCast] using hn

/-- The actual growing-scope envelope is subexponential. -/
theorem scope_subexponential (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (512*(n : ℝ)^(3/4 : ℝ)*Real.log 2)≤Real.exp (ε*(n : ℝ)) := by
  have h := tendsto_natCast_atTop_atTop.eventually (eventually_polynomial_counter_with_arity_le 0 0 (512*Real.log 2) ε hε)
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hpos
  simpa [mul_assoc,mul_left_comm,mul_comm] using hn

/-- Five actual resource components together satisfy every exponential target. -/
theorem budget_subexponential (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, budget d n≤Real.exp (ε*(n : ℝ)) := by
  have he : 0<ε/2 := by positivity
  have hc := tendsto_natCast_atTop_atTop.eventually (eventually_constant_polynomial_exp_rho_le 5 0 0 (ε/2) he)
  filter_upwards [polynomial_subexponential d (ε/2) he,
    scheduled_support_subexponential (ε/2) he,summary_subexponential (ε/2) he,
    eventually_head_le_summary,scope_subexponential (ε/2) he,hc] with n hp hs hy hh hw hc
  have hhead := hh.trans hy
  have hsum : budget d n≤5*Real.exp ((ε/2)*(n : ℝ)) := by dsimp [budget]; linarith
  have hfive : (5 : ℝ)≤Real.exp ((ε/2)*(n : ℝ)) := by simpa using hc
  calc
    budget d n≤5*Real.exp ((ε/2)*(n : ℝ)) := hsum
    _≤Real.exp ((ε/2)*(n : ℝ))*Real.exp ((ε/2)*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _=Real.exp (ε*(n : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

/-- Fixed powers, polynomial bit widths, and a fixed leading constant preserve
subexponential growth of the fully materialized resource budget. -/
theorem fixed_polynomial_subexponential (d a k : ℕ) (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      C*(n : ℝ)^a*(budget d n)^k≤Real.exp (ε*(n : ℝ)) := by
  let δ := ε/((k : ℝ)+1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hp := tendsto_natCast_atTop_atTop.eventually
    (eventually_constant_polynomial_exp_rho_le C (a : ℝ) 0 δ hδ)
  filter_upwards [budget_subexponential d δ hδ,hp,eventually_ge_atTop (1 : ℕ)]
    with n hs hp hn
  have hbudget : 0≤budget d n := by
    have hs0 : (0 : ℝ)≤SemiprimeCounterEnumeration.weightedCount n (cutoff n) := by positivity
    have hy0 : 0 ≤ summaryEnvelope n := Real.exp_nonneg _
    have hh0 : 0 ≤ headEnvelope n := Real.exp_nonneg _
    dsimp only [budget]
    positivity
  have hpow : (budget d n)^k≤(Real.exp (δ*(n : ℝ)))^k := by gcongr
  have hp' : C*(n : ℝ)^a≤Real.exp (δ*(n : ℝ)) := by
    simpa [Real.rpow_natCast] using hp
  calc
    C*(n : ℝ)^a*(budget d n)^k≤
        Real.exp (δ*(n : ℝ))*(budget d n)^k :=
      mul_le_mul_of_nonneg_right hp' (pow_nonneg hbudget k)
    _≤Real.exp (δ*(n : ℝ))*(Real.exp (δ*(n : ℝ)))^k :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _=Real.exp (ε*(n : ℝ)) := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      dsimp [δ]
      field_simp
      ring

/-- Literal public network size tends to infinity, from the proved input-edge
injection; this is not a separately supplied graph-size assumption. -/
theorem public_size_atTop : Tendsto SemiprimeMacroParameters.variableCount atTop atTop := by
  apply tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => n) ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
  exact SemiprimeMacroParameters.input_le_variableCount (by omega)

/-- Every fixed polynomial in the actual public aggregate is exponentially
negligible in the ORIGINAL input bit length. -/
theorem public_fixed_polynomial_subexponential (d a k : ℕ) (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ L : ℕ in atTop,
      C*(SemiprimeMacroParameters.variableCount L : ℝ)^a*
        (budget d (SemiprimeMacroParameters.variableCount L))^k≤Real.exp (ε*(L : ℝ)) := by
  have he : 0<ε/6400 := by positivity
  filter_upwards [public_size_atTop.eventually
    (fixed_polynomial_subexponential d a k C (ε/6400) he),eventually_ge_atTop (1 : ℕ)]
    with L h hL
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hb : (SemiprimeMacroParameters.variableCount L : ℝ)≤6400*(L : ℝ) := by
    exact_mod_cast SemiprimeMacroParameters.variableCount_le (show 0<L by omega)
  nlinarith

/-- The literal public summary cardinality is dominated by the acquired
scheduled envelope, using the actual constructed rank theorem. -/
theorem public_summary_le {L : ℕ} (hL : 0<L)
    (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount L)
      (SemiprimeMacroParameters.scopeBound L))
    (hν : 64≤Nat.clog 2 (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)))
    (t : Fin (SemiprimeScheduledCounter.publicParameters hL hg).Q) :
    (SemiprimeConstructedCounter.summaryCount
      (SemiprimeScheduledCounter.publicParameters hL hg) t : ℝ)≤
      summaryEnvelope (SemiprimeMacroParameters.variableCount L) := by
  apply (Real.le_exp_log _).trans
  apply Real.exp_le_exp.mpr
  convert SemiprimeScheduledCounter.public_summary_log_bound hL hg hν t using 1
  simp only [decay]
  ring

/-- Actual original-coordinate head cardinalities satisfy the scheduled bound;
no independent small-head hypothesis is supplied. -/
theorem public_head_card_le {L : ℕ} (hL : 0<L)
    (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount L)
      (SemiprimeMacroParameters.scopeBound L))
    (t : Fin (SemiprimeScheduledCounter.publicParameters hL hg).Q)
    (g : Fin (SemiprimeScheduledCounter.publicParameters hL hg).r) :
    (Fintype.card {v // (SemiprimeConstructedCounter.layout
      (SemiprimeScheduledCounter.publicParameters hL hg)).head t v=g} : ℚ)≤
      3*(SemiprimeMacroParameters.variableCount L : ℚ)/
        (2*(scheduledGroupCount (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)) : ℚ)) := by
  exact SemiprimeSourceLayout.builtLayout_head_bound _ _ _ _ _ 2
    (SemiprimeMacroParameters.scopeBound L)
    (SemiprimeScheduledCounter.packingGuard (SemiprimeMacroParameters.scopeBound L) hg
      (SemiprimeScheduledCounter.public_occurrences hL) SemiprimeMacroParameters.actual_arity_le
      (SemiprimeScheduledCounter.public_incidence_card hL)) t g


/-- Literal per-node/per-head resource sum. Taking a maximum over the finitely
many nodes and heads has the same uniform upper bound proved below. -/
def actualBudget (d L : ℕ) (hL : 0<L)
    (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount L)
      (SemiprimeMacroParameters.scopeBound L))
    (t : Fin (SemiprimeScheduledCounter.publicParameters hL hg).Q)
    (g : Fin (SemiprimeScheduledCounter.publicParameters hL hg).r) : ℝ :=
  let n := SemiprimeMacroParameters.variableCount L
  (n : ℝ)^d + SemiprimeCounterEnumeration.weightedCount n (cutoff n) +
    SemiprimeConstructedCounter.summaryCount (SemiprimeScheduledCounter.publicParameters hL hg) t +
    (2 : ℝ)^Fintype.card {v // (SemiprimeConstructedCounter.layout
      (SemiprimeScheduledCounter.publicParameters hL hg)).head t v=g} +
    (2 : ℝ)^SemiprimeMacroParameters.scopeBound L

/-- Actual acquired summary cardinalities, actual head truth-table sizes and
actual public scopes lie in the aggregate envelope. -/
theorem actualBudget_le (d L : ℕ) (hL : 0<L)
    (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount L)
      (SemiprimeMacroParameters.scopeBound L))
    (hν : 64≤Nat.clog 2 (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)))
    (t : Fin (SemiprimeScheduledCounter.publicParameters hL hg).Q)
    (g : Fin (SemiprimeScheduledCounter.publicParameters hL hg).r) :
    actualBudget d L hL hg t g≤budget d (SemiprimeMacroParameters.variableCount L) := by
  have hy := public_summary_le hL hg hν t
  have hh := public_head_card_le hL hg t g
  have hhR :
      (Fintype.card {v // (SemiprimeConstructedCounter.layout
        (SemiprimeScheduledCounter.publicParameters hL hg)).head t v=g} : ℝ)≤
        3*(SemiprimeMacroParameters.variableCount L : ℝ)/
          (2*(scheduledGroupCount (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)) : ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast] using
      ((Rat.cast_le (K := ℝ)).mpr hh)
  have hr : (0 : ℝ)<scheduledGroupCount (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)) := by
    exact_mod_cast (show 0<scheduledGroupCount (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)) by
      have := (scheduled_parameter_ranges hν).1; omega)
  have hhead : (2 : ℝ)^Fintype.card {v // (SemiprimeConstructedCounter.layout
      (SemiprimeScheduledCounter.publicParameters hL hg)).head t v=g}≤
      headEnvelope (SemiprimeMacroParameters.variableCount L) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2)]
    apply Real.exp_le_exp.mpr
    have hh' : (Fintype.card {v // (SemiprimeConstructedCounter.layout
        (SemiprimeScheduledCounter.publicParameters hL hg)).head t v=g} : ℝ)≤
        2*(SemiprimeMacroParameters.variableCount L : ℝ)/
          scheduledGroupCount (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)) := by
      apply hhR.trans
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<2*scheduledGroupCount
        (Nat.clog 2 (SemiprimeMacroParameters.variableCount L))) hr).mpr
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hh' (Real.log_nonneg (show (1 : ℝ)≤2 by norm_num))
    nlinarith
  have hscope : (2 : ℝ)^SemiprimeMacroParameters.scopeBound L≤
      Real.exp (512*(SemiprimeMacroParameters.variableCount L : ℝ)^(3/4 : ℝ)*Real.log 2) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2)]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right (SemiprimeMacroParameters.scopeBound_le_variableCount_rpow hL)
      (Real.log_nonneg (show (1 : ℝ)≤2 by norm_num))
    nlinarith
  dsimp only [actualBudget,budget]
  linarith

/-- The literal public sum, not independent supplied subexponential factors,
retains every fixed polynomial overhead in the original bit length. -/
theorem actual_fixed_polynomial_subexponential (d a k : ℕ) (C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ L : ℕ in atTop, ∀ (hL : 0<L)
      (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount L)
        (SemiprimeMacroParameters.scopeBound L))
      (t : Fin (SemiprimeScheduledCounter.publicParameters hL hg).Q)
      (g : Fin (SemiprimeScheduledCounter.publicParameters hL hg).r),
      C*(SemiprimeMacroParameters.variableCount L : ℝ)^a*(actualBudget d L hL hg t g)^k≤
        Real.exp (ε*(L : ℝ)) := by
  have hv := (tendsto_clog_two_atTop.comp tendsto_clog_two_atTop).comp public_size_atTop
  filter_upwards [public_fixed_polynomial_subexponential d a k C ε hε,
    hv.eventually (eventually_ge_atTop 64)] with L h hν
  intro hL hg t g
  apply le_trans ?_ h
  have hb := actualBudget_le d L hL hg hν t g
  have hn : 0≤actualBudget d L hL hg t g := by
    dsimp only [actualBudget]
    positivity
  gcongr

/-- Natural input bit length tends to infinity; no real-log surrogate is used
when instantiating the actual public compiler. -/
theorem size_atTop : Tendsto Nat.size atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (2^m)] with N hN
  exact (Nat.lt_size.mpr hN).le

/-- The proved public graph envelope, at its ACTUAL integer input bit length,
is eventually below every positive power of the original input. -/
theorem public_fixed_polynomial_subpower (d a k : ℕ) (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      C*(SemiprimeMacroParameters.variableCount N.size : ℝ)^a*
        (budget d (SemiprimeMacroParameters.variableCount N.size))^k≤(N : ℝ)^ε := by
  have hδ : 0<ε*Real.log 2/2 := by positivity
  filter_upwards [size_atTop.eventually
    (public_fixed_polynomial_subexponential d a k C (ε*Real.log 2/2) hδ),
    eventually_ge_atTop (2 : ℕ)] with N h hN
  have hpos : 0<N.size := Nat.size_pos.mpr (by omega)
  have hlow : 2^(N.size-1)≤N := Nat.lt_size.mp (by omega)
  have hl := Real.log_le_log (by positivity : (0 : ℝ)<2^(N.size-1))
    (show (2 : ℝ)^(N.size-1)≤N by exact_mod_cast hlow)
  rw [Real.log_pow,Nat.cast_sub hpos,Nat.cast_one] at hl
  have hl2 : Real.log 2≤Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hn : (0 : ℝ)<N := by positivity
  apply h.trans
  rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- In particular, any fixed polynomial resource ledger instantiated with the
actual aggregate has a sixth-power numerical bound. This does not identify a
program's clock with that ledger. -/
theorem public_fixed_polynomial_sixth (d a k : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C*(SemiprimeMacroParameters.variableCount N.size : ℝ)^a*
        (budget d (SemiprimeMacroParameters.variableCount N.size))^k≤(N : ℝ)^(1/6 : ℝ) :=
  public_fixed_polynomial_subpower d a k C (1/6) (by norm_num)

/-- The original integer input's ACTUAL finite summary/head/scope sum has the
same subpower rate, uniformly over constructed source nodes and heads. -/
theorem actual_fixed_polynomial_subpower (d a k : ℕ) (C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (hL : 0<N.size)
      (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount N.size)
        (SemiprimeMacroParameters.scopeBound N.size))
      (t : Fin (SemiprimeScheduledCounter.publicParameters hL hg).Q)
      (g : Fin (SemiprimeScheduledCounter.publicParameters hL hg).r),
      C*(SemiprimeMacroParameters.variableCount N.size : ℝ)^a*
        (actualBudget d N.size hL hg t g)^k≤(N : ℝ)^ε := by
  have hv := ((tendsto_clog_two_atTop.comp tendsto_clog_two_atTop).comp public_size_atTop).comp size_atTop
  filter_upwards [public_fixed_polynomial_subpower d a k C ε hε,
    hv.eventually (eventually_ge_atTop 64)] with N h hν
  intro hL hg t g
  apply le_trans ?_ h
  have hb := actualBudget_le d N.size hL hg hν t g
  have hn : 0≤actualBudget d N.size hL hg t g := by
    dsimp only [actualBudget]
    positivity
  gcongr

/-- Sixth-power rate for the literal acquired public resource sum, still only
an analytic theorem until an executed clock is bounded by this expression. -/
theorem actual_fixed_polynomial_sixth (d a k : ℕ) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ N : ℕ in atTop, ∀ (hL : 0<N.size)
      (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount N.size)
        (SemiprimeMacroParameters.scopeBound N.size))
      (t : Fin (SemiprimeScheduledCounter.publicParameters hL hg).Q)
      (g : Fin (SemiprimeScheduledCounter.publicParameters hL hg).r),
      C*(SemiprimeMacroParameters.variableCount N.size : ℝ)^a*
        (actualBudget d N.size hL hg t g)^k≤(N : ℝ)^(1/6 : ℝ) :=
  actual_fixed_polynomial_subpower d a k C (1/6) hC (by norm_num)

end RiemannGaussian.SemiprimeMaterializedRate
