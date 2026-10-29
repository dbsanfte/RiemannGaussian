/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeConstructedCounter
import RiemannGaussian.SemiprimeSourceLayoutRate
import RiemannGaussian.SemiprimeMacroParameters

/-!
# Actual scheduled constructed counters

The public schedule is used directly to build the source-layout parameters.
Packing and total-rank budgets are derived from original occurrence and scope
facts, rather than supplied as assumptions about selected constraints.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeScheduledCounter
open Filter
open scoped Topology
open RiemannGaussian.SemiprimeCounterRate
open RiemannGaussian.SemiprimeCounterTail
open RiemannGaussian.SemiprimeSourceLayoutRate
open RiemannGaussian.SemiprimeSourceLayout
open RiemannGaussian.SemiprimeConstructedCounter
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local instance] Classical.propDecidable

/-- The actual rational tolerance, before casting into spectral estimates. -/
def scheduledEpsilon (n : ℕ) : ℚ :=
  1 / (scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n : ℕ)

theorem scheduledEpsilon_cast (n : ℕ) :
    (scheduledEpsilon n : ℝ) = sourceEpsilon (Nat.clog 2 n) := by
  simp [scheduledEpsilon, sourceEpsilon]

variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]
variable {arity : E → ℕ} {coordinate : (e : E) → Fin (arity e) → A}

/-- Literal scheduled parameters with occurrence bound two. -/
def parameters (w : ℕ) (hg : sourceLayoutGuard (Fintype.card A) w)
    (hocc : ∀ a, (Finset.univ.filter
      (fun i : Incidence arity => coordinate i.1 i.2 = a)).card ≤ 2) :
    Parameters arity coordinate where
  r := scheduledGroupCount (Nat.clog 2 (Fintype.card A))
  Q := scheduledPointCount (Nat.clog 2 (Fintype.card A))
  R := scheduledDegree (Nat.clog 2 (Fintype.card A))
  B := 2
  epsilon := scheduledEpsilon (Fintype.card A)
  groups := hg.2.2.1
  nodes := hg.2.2.2.1
  degree := hg.2.2.2.2.1
  size := hg.2.2.2.2.2.1
  occurrences := hocc

/-- The actual factor fibre consists of exactly the original ports of that factor. -/
def factorFibreEquiv (e : E) :
    {i : Incidence arity // i.1 = e} ≃ Fin (arity e) where
  toFun i := i.property ▸ i.val.2
  invFun j := ⟨⟨e, j⟩, rfl⟩
  left_inv i := by
    rcases i with ⟨⟨e', j⟩, h⟩
    change e' = e at h
    subst e'
    rfl
  right_inv _ := rfl

theorem factor_fibre_card (e : E) :
    (Finset.univ.filter (fun i : Incidence arity => i.1 = e)).card = arity e := by
  simpa only [Fintype.card_subtype, Fintype.card_fin] using
    Fintype.card_congr (factorFibreEquiv (arity := arity) e)

/-- The scheduled universal alphabet has exactly the scheduled dimension. -/
theorem universal_card (n : ℕ) :
    Fintype.card (UniversalType (scheduledGroupCount (Nat.clog 2 n))
      (scheduledPointCount (Nat.clog 2 n)) 1) = scheduledDimension n := by
  rw [OAI.Algorithms.SubexponentialSAT.MulticolorTypes.card_universalType]
  simp only [scheduledDimension, Nat.reduceAdd, Nat.mul_comm]

/-- The published packing guards follow from actual graph occurrences,
scopes and total incidences at the literal schedule. -/
theorem packingGuard (w : ℕ) (hg : sourceLayoutGuard (Fintype.card A) w)
    (hocc : ∀ a, (Finset.univ.filter
      (fun i : Incidence arity => coordinate i.1 i.2 = a)).card ≤ 2)
    (hscope : ∀ e, arity e ≤ w)
    (hM : Fintype.card (Incidence arity) = 2 * Fintype.card A) :
    PackingGuard (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst
      (parameters w hg hocc).r (parameters w hg hocc).Q
      (parameters w hg hocc).epsilon 2 w := by
  rcases hg with ⟨hn, hw, hr, hQ, hR, hRQ, heps, hepshi, hload, hheads, hwidth⟩
  have hepsq : 0 < scheduledEpsilon (Fintype.card A) := by
    exact_mod_cast (show (0 : ℝ) < (scheduledEpsilon (Fintype.card A) : ℝ) by
      rw [scheduledEpsilon_cast]; exact heps)
  refine ⟨hepsq, hocc, ?_, ?_, hn, ?_, ?_⟩
  · intro e
    simpa only [factor_fibre_card] using hscope e
  · rw [hM]; omega
  · change 4 * ((2 + w : ℕ) : ℚ) *
        (Fintype.card (UniversalType (scheduledGroupCount (Nat.clog 2 (Fintype.card A)))
          (scheduledPointCount (Nat.clog 2 (Fintype.card A))) 1) : ℚ) ^ 2 ≤
      (scheduledEpsilon (Fintype.card A)) ^ 2 * (Fintype.card (Incidence arity) : ℚ)
    rw [universal_card, hM]
    have hl : (4 * (2 + w) * scheduledDimension (Fintype.card A) ^ 2 *
        (scheduledGroupCount (Nat.clog 2 (Fintype.card A)) * Nat.clog 2 (Fintype.card A)) ^ 2 : ℚ) ≤
        2 * Fintype.card A := by exact_mod_cast hload
    have hden : (0 : ℚ) <
        (scheduledGroupCount (Nat.clog 2 (Fintype.card A)) * Nat.clog 2 (Fintype.card A) : ℕ) := by
      exact one_div_pos.mp hepsq
    simp only [scheduledEpsilon, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hl ⊢
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul]
    have hd : (0 : ℚ) < (scheduledGroupCount (Nat.clog 2 (Fintype.card A)) : ℚ) *
        (Nat.clog 2 (Fintype.card A) : ℚ) := by exact_mod_cast hden
    exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr hl
  · change 16 * (scheduledPointCount (Nat.clog 2 (Fintype.card A)) : ℚ) *
      (scheduledGroupCount (Nat.clog 2 (Fintype.card A)) : ℚ) ^ 2 ≤ Fintype.card A
    exact_mod_cast hheads

/-- No rank-budget assumption: the actual selected rank satisfies the source bound. -/
theorem actual_rank_budget (w : ℕ) (hg : sourceLayoutGuard (Fintype.card A) w)
    (hocc : ∀ a, (Finset.univ.filter
      (fun i : Incidence arity => coordinate i.1 i.2 = a)).card ≤ 2)
    (hscope : ∀ e, arity e ≤ w)
    (hM : Fintype.card (Incidence arity) = 2 * Fintype.card A)
    (t : Fin (parameters w hg hocc).Q) :
    totalRank (parameters w hg hocc) t *
      (scheduledGroupCount (Nat.clog 2 (Fintype.card A)) * Nat.clog 2 (Fintype.card A)) ≤
      4 * Fintype.card A := by
  have hwidth := hg.2.2.2.2.2.2.2.2.2.2
  have hw' : 32 * (((parameters w hg hocc).Q - 1 : ℕ) : ℝ) *
      Real.log (2 / ((parameters w hg hocc).epsilon : ℝ)) ≤
        ((parameters w hg hocc).R : ℝ) ^ 2 := by
    simpa only [parameters, scheduledEpsilon_cast] using hwidth
  have hr := totalRank_le (parameters w hg hocc) w
    (packingGuard w hg hocc hscope hM) hw' t
  rw [hM] at hr
  have heps : 0 < scheduledEpsilon (Fintype.card A) := by
    have h := hg.2.2.2.2.2.2.1
    exact_mod_cast (show (0 : ℝ) < (scheduledEpsilon (Fintype.card A) : ℝ) by
      rw [scheduledEpsilon_cast]; exact h)
  have hd : (0 : ℚ) <
      (scheduledGroupCount (Nat.clog 2 (Fintype.card A)) * Nat.clog 2 (Fintype.card A) : ℕ) :=
    one_div_pos.mp heps
  have hm := mul_le_mul_of_nonneg_right hr (le_of_lt hd)
  have he : (2 * (parameters w hg hocc).epsilon *
      (2 * Fintype.card A : ℕ)) *
        (scheduledGroupCount (Nat.clog 2 (Fintype.card A)) * Nat.clog 2 (Fintype.card A) : ℕ) =
      (4 * Fintype.card A : ℚ) := by
    change (2 * (1 / _) * _) * _ = _
    field_simp
    push_cast
    ring
  rw [he] at hm
  exact_mod_cast hm

/-- The actual complete summary enumeration has the scheduled logarithmic envelope. -/
theorem actual_summary_log_bound (w : ℕ) (hg : sourceLayoutGuard (Fintype.card A) w)
    (hocc : ∀ a, (Finset.univ.filter
      (fun i : Incidence arity => coordinate i.1 i.2 = a)).card ≤ 2)
    (hscope : ∀ e, arity e ≤ w)
    (hM : Fintype.card (Incidence arity) = 2 * Fintype.card A)
    (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 (Fintype.card A)))
    (t : Fin (parameters w hg hocc).Q) :
    Real.log (summaryCount (parameters w hg hocc) t : ℝ) ≤
      (48 * (Fintype.card A : ℝ) * (Nat.clog 2 (Nat.clog 2 (Fintype.card A)) : ℝ) ^ 2 /
        Real.sqrt (Nat.clog 2 (Fintype.card A) : ℝ)) * Real.log 2 := by
  have hb := actual_rank_budget w hg hocc hscope hM t
  have hr := source_summary_binary_rate hν hb
  have hc := summary_count_le (parameters w hg hocc) t
  have hh : height (parameters w hg hocc) = sourceHeight (Nat.clog 2 (Fintype.card A)) := by
    simp only [height, parameters, sourceHeight]

  rw [hh] at hc
  have hc' : summaryCount (parameters w hg hocc) t ≤
      sourceSignatureBase (Fintype.card A) ^ totalRank (parameters w hg hocc) t := by
    simpa only [sourceSignatureBase, Nat.mul_assoc] using hc
  have hp : 0 < summaryCount (parameters w hg hocc) t := by
    rw [summary_count]
    apply Finset.prod_pos
    intro g _
    apply pow_pos
    exact Nat.succ_pos _
  have hl := Real.log_le_log (show (0 : ℝ) < summaryCount (parameters w hg hocc) t by
      exact_mod_cast hp) (show (summaryCount (parameters w hg hocc) t : ℝ) ≤
        (sourceSignatureBase (Fintype.card A) : ℝ) ^ totalRank (parameters w hg hocc) t by
      exact_mod_cast hc')
  rw [Real.log_pow] at hl
  exact hl.trans hr

/-- The concrete public graph, with its actual edge count, eventually meets every
real source-layout guard. No graph-size or eventual-guard premise is supplied. -/
theorem eventually_public_graph_guard :
    ∀ᶠ L : ℕ in atTop, sourceLayoutGuard
      (SemiprimeMacroParameters.variableCount L) (SemiprimeMacroParameters.scopeBound L) := by
  have hE : Tendsto SemiprimeMacroParameters.variableCount atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_gt_atTop 0] with L hL
    exact SemiprimeMacroParameters.input_le_variableCount hL
  have h := hE.eventually (eventually_source_layout_guard 512 (by norm_num))
  filter_upwards [h, eventually_gt_atTop 0] with L hg hL
  apply hg
  · unfold SemiprimeMacroParameters.scopeBound
    positivity
  · exact SemiprimeMacroParameters.scopeBound_le_variableCount_rpow hL

/-- The source Python constructor's INTEGER sufficient spectral-width test. -/
theorem integer_spectral_width {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) :
    32 * (scheduledPointCount lam - 1) *
      Nat.clog 2 (2 * scheduledGroupCount lam * lam) ≤ scheduledDegree lam ^ 2 := by
  have hr := (scheduled_parameter_ranges hν).1
  have hrLam : scheduledGroupCount lam ≤ lam :=
    (Nat.div_le_self _ _).trans (Nat.sqrt_le_self lam)
  have hl : lam ≤ 2 ^ Nat.clog 2 lam := Nat.le_pow_clog (by decide) lam
  have hprod : 2 * scheduledGroupCount lam * lam ≤ 2 ^ (2 * Nat.clog 2 lam + 1) := by
    have hm := Nat.mul_le_mul (hrLam.trans hl) hl
    have he : (2 ^ Nat.clog 2 lam : ℕ) * 2 ^ Nat.clog 2 lam * 2 =
        2 ^ (2 * Nat.clog 2 lam + 1) := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    nlinarith
  have hc : Nat.clog 2 (2 * scheduledGroupCount lam * lam) ≤ 2 * Nat.clog 2 lam + 1 :=
    Nat.clog_le_of_le_pow hprod
  have hQ : 128 * Nat.clog 2 lam * (scheduledPointCount lam - 1) ≤ lam := by
    calc
      _ ≤ 128 * Nat.clog 2 lam * scheduledPointCount lam :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ lam := by
        simpa [scheduledPointCount, Nat.mul_comm] using Nat.div_mul_le_self lam (128 * Nat.clog 2 lam)
  have hs := scheduledCeilSqrt_sq_ge lam
  unfold scheduledDegree
  have hm := Nat.mul_le_mul_left (32 * (scheduledPointCount lam - 1)) hc
  nlinarith

/-- The source tolerance fits the counter's half-input Taylor budget at this schedule. -/
theorem integer_tolerance_load {n : ℕ} (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 n)) :
    scheduledEpsilon n * (2 * n : ℕ) ≤ (n : ℚ) / 2 := by
  have hr := (scheduled_parameter_ranges hν).1
  have hrLam : scheduledGroupCount (Nat.clog 2 n) ≤ Nat.clog 2 n :=
    (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)
  have hd : 4 ≤ scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n := by nlinarith
  have hdq : (4 : ℚ) ≤
      (scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n : ℕ) := by exact_mod_cast hd
  unfold scheduledEpsilon
  push_cast
  have hdpos : (0 : ℚ) < (scheduledGroupCount (Nat.clog 2 n) : ℚ) * Nat.clog 2 n := by
    exact_mod_cast (show 0 < scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n by omega)
  rw [one_div_mul_eq_div, div_le_div_iff₀ hdpos (by norm_num : (0 : ℚ) < 2)]
  push_cast at hdq
  nlinarith

/-- Both additional executable source guards eventually hold at actual graph sizes. -/
theorem eventually_public_executable_guards :
    ∀ᶠ L : ℕ in atTop,
      let n := SemiprimeMacroParameters.variableCount L
      let lam := Nat.clog 2 n
      sourceLayoutGuard n (SemiprimeMacroParameters.scopeBound L) ∧
      32 * (scheduledPointCount lam - 1) * Nat.clog 2 (2 * scheduledGroupCount lam * lam) ≤
        scheduledDegree lam ^ 2 ∧ scheduledEpsilon n * (2 * n : ℕ) ≤ (n : ℚ) / 2 := by
  have hE : Tendsto SemiprimeMacroParameters.variableCount atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_gt_atTop 0] with L hL
    exact SemiprimeMacroParameters.input_le_variableCount hL
  have hν := (tendsto_clog_two_atTop.comp (tendsto_clog_two_atTop.comp hE)).eventually
    (eventually_ge_atTop 64)
  filter_upwards [eventually_public_graph_guard, hν] with L hg hl
  exact ⟨hg, integer_spectral_width hl, integer_tolerance_load hl⟩

/-- Actual input digit capacity of the public two-axis graph. -/
theorem public_digit_capacity {L : ℕ} (hL : 0 < L) :
    SemiprimeMacroParameters.digitCount L ≤
      SemiprimeMacroParameters.firstAxis L * SemiprimeMacroParameters.secondAxis L := by
  rw [SemiprimeMacroParameters.axes_product]
  have hd := (SemiprimeMacroParameters.digitCount_bounds hL).2
  have hn := SemiprimeMacroParameters.transform_eq_four_radixBits hL
  omega

/-- The literal public graph's actual ordered-port coordinate map. -/
def publicCoordinate {L : ℕ} (hL : 0 < L)
    (v : SemiprimeMacroGraph.SubdividedVertex
      (SemiprimeMacroParameters.firstAxis L) (SemiprimeMacroParameters.secondAxis L)
      (SemiprimeMacroParameters.digitCount L))
    (i : Fin (SemiprimeMacroGraph.subdividedArity v)) :
    SemiprimeMacroGraph.Edge (SemiprimeMacroParameters.firstAxis L)
      (SemiprimeMacroParameters.secondAxis L) (SemiprimeMacroParameters.digitCount L) :=
  SemiprimeMacroGraph.orderedEdgeAt (SemiprimeMacroParameters.digitCount_bounds hL).1
    (public_digit_capacity hL) ⟨v, i⟩

/-- Original ordered graph scopes use every Boolean edge exactly twice. -/
theorem public_occurrences {L : ℕ} (hL : 0 < L)
    (a : SemiprimeMacroGraph.Edge (SemiprimeMacroParameters.firstAxis L)
      (SemiprimeMacroParameters.secondAxis L) (SemiprimeMacroParameters.digitCount L)) :
    (Finset.univ.filter (fun i : Incidence SemiprimeMacroGraph.subdividedArity =>
      publicCoordinate hL i.1 i.2 = a)).card ≤ 2 := by
  have h := SemiprimeMacroGraph.ordered_edge_occurrence_two
    (SemiprimeMacroParameters.digitCount_bounds hL).1 (public_digit_capacity hL) a
  have h' : (∑ i : Incidence SemiprimeMacroGraph.subdividedArity,
      if publicCoordinate hL i.1 i.2 = a then (1 : ℕ) else 0) = 2 := by
    rw [Fintype.sum_sigma]
    exact h
  simpa only [Finset.card_filter] using h'.le

/-- No incidence-count assumption is needed for the actual public graph. -/
theorem public_incidence_card {L : ℕ} (hL : 0 < L) :
    Fintype.card (Incidence (SemiprimeMacroGraph.subdividedArity
      (r := SemiprimeMacroParameters.firstAxis L) (t := SemiprimeMacroParameters.secondAxis L)
      (digits := SemiprimeMacroParameters.digitCount L))) =
      2 * SemiprimeMacroParameters.variableCount L := by
  have h := Fintype.card_congr (SemiprimeMacroGraph.subdividedOrderedEndpointEquiv
    (SemiprimeMacroParameters.firstAxis L) (SemiprimeMacroParameters.secondAxis L)
    (SemiprimeMacroParameters.digitCount L) (SemiprimeMacroParameters.digitCount_bounds hL).1
    (public_digit_capacity hL))
  rw [Fintype.card_prod, Fintype.card_bool] at h
  simpa only [Incidence, SemiprimeMacroParameters.variableCount, Nat.mul_comm] using h.symm

/-- The actual public graph parameters are constructed, including occurrence certificates. -/
def publicParameters {L : ℕ} (hL : 0 < L)
    (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount L)
      (SemiprimeMacroParameters.scopeBound L)) :
    Parameters SemiprimeMacroGraph.subdividedArity (publicCoordinate hL) :=
  parameters (SemiprimeMacroParameters.scopeBound L) hg (public_occurrences hL)

/-- Concrete public summary cost, with actual graph rank proved internally. -/
theorem public_summary_log_bound {L : ℕ} (hL : 0 < L)
    (hg : sourceLayoutGuard (SemiprimeMacroParameters.variableCount L)
      (SemiprimeMacroParameters.scopeBound L))
    (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)))
    (t : Fin (publicParameters hL hg).Q) :
    Real.log (summaryCount (publicParameters hL hg) t : ℝ) ≤
      (48 * (SemiprimeMacroParameters.variableCount L : ℝ) *
        (Nat.clog 2 (Nat.clog 2 (SemiprimeMacroParameters.variableCount L)) : ℝ) ^ 2 /
        Real.sqrt (Nat.clog 2 (SemiprimeMacroParameters.variableCount L) : ℝ)) * Real.log 2 :=
  actual_summary_log_bound (SemiprimeMacroParameters.scopeBound L) hg
    (public_occurrences hL) SemiprimeMacroParameters.actual_arity_le
    (public_incidence_card hL) hν t

end RiemannGaussian.SemiprimeScheduledCounter
