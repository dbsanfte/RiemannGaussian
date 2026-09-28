/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTransitionSixPeriod

/-!
# Several complete signed six-prime periods at the same total cost

These are disjoint copies of the already proved literal population. The
precision is chosen before the moment order, so adding finitely many periods
does not increase its eventual relative radial cost. No credit is repeated.
-/

namespace RiemannGaussian.ZetaRieszMultiPeriodSix
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- The number of full periods whose centers fit in a half-unit interval. -/
def periodCount (y : ℝ) : ℕ := ⌊|y|/(4*Real.pi)⌋₊+1

/-- Successive centers are exactly one phase period apart. -/
def center (v y : ℝ) (i : ℕ) : ℝ := v+i*(2*Real.pi/|y|)

/-- Only the union of the existing literal populations is paid. -/
def population (v y : ℝ) : Finset ℕ := (Finset.range (periodCount y)).biUnion
  (fun i => ZetaRieszTransitionSixPeriod.population (center v y i) y)

/-- At the smallest admissible height at least five full periods fit. -/
theorem five_le_periodCount {y : ℝ} (hy : 54 ≤ |y|) : 5 ≤ periodCount y := by
  have h : (4 : ℝ) ≤ |y|/(4*Real.pi) :=
    (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr (by nlinarith [Real.pi_lt_d4])
  have hn : 4 ≤ ⌊|y|/(4*Real.pi)⌋₊ := (Nat.le_floor_iff (by positivity)).mpr h
  dsimp only [periodCount]
  omega

/-- Every chosen center stays between the original center and half a unit later. -/
theorem center_bounds {v y : ℝ} {i : ℕ} (hi : i ∈ Finset.range (periodCount y)) :
    v ≤ center v y i ∧ center v y i ≤ v+1/2 := by
  have hiN : i ≤ ⌊|y|/(4*Real.pi)⌋₊ := by
    have hh := Finset.mem_range.mp hi
    dsimp only [periodCount] at hh
    omega
  have hiR : (i : ℝ) ≤ |y|/(4*Real.pi) :=
    (Nat.cast_le.mpr hiN).trans (Nat.floor_le (by positivity))
  have hstep : 0 ≤ 2*Real.pi/|y| := by positivity
  have hupper : (i : ℝ)*(2*Real.pi/|y|) ≤ 1/2 := by
    by_cases hy : y = 0
    · simp [hy]
    · have hy0 : 0 < |y| := abs_pos.mpr hy
      calc
        _ ≤ (|y|/(4*Real.pi))*(2*Real.pi/|y|) := mul_le_mul_of_nonneg_right hiR hstep
        _ = 1/2 := by field_simp; norm_num
  dsimp only [center]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep)
  · linarith

/-- The shifted centers retain exactly the original negative phase peak. -/
theorem center_phase {v y : ℝ} (hy : y ≠ 0) (i : ℕ) :
    Real.cos (y*center v y i) = Real.cos (y*v) := by
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have he : y*center v y i = y*v-(i : ℝ)*(2*Real.pi) := by
      dsimp only [center]
      rw [abs_of_neg hyneg]
      field_simp
      ring
    rw [he,Real.cos_sub_nat_mul_two_pi]
  · have he : y*center v y i = y*v+(i : ℝ)*(2*Real.pi) := by
      dsimp only [center]
      rw [abs_of_pos hypos]
      field_simp
    rw [he,Real.cos_add_nat_mul_two_pi]

/-- Half-open logarithmic periods share no arithmetic labels. -/
theorem disjoint_periods {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {i j : ℕ} (hi : i ∈ Finset.range (periodCount y))
    (hj : j ∈ Finset.range (periodCount y)) (hij : i ≠ j) :
    Disjoint (ZetaRieszTransitionSixPeriod.population (center v y i) y)
      (ZetaRieszTransitionSixPeriod.population (center v y j) y) := by
  have hy0 : 0 < |y| := by linarith
  have hstep : 0 < 2*Real.pi/|y| := by positivity
  have hsep {a b : ℕ} (hab : a < b) :
      center v y a+Real.pi/|y| ≤ center v y b-Real.pi/|y| := by
    have hh : (a : ℝ)+1 ≤ b := by exact_mod_cast hab
    have ht := mul_le_mul_of_nonneg_right hh hstep.le
    dsimp only [center]
    ring_nf at ht ⊢
    linarith
  apply Finset.disjoint_left.mpr
  intro n hn hm
  have hni := ZetaRieszTransitionSixPeriod.population_data
    (hv.trans (center_bounds hi).1) hy hn
  have hnj := ZetaRieszTransitionSixPeriod.population_data
    (hv.trans (center_bounds hj).1) hy hm
  rcases lt_or_gt_of_ne hij with hij | hji
  · linarith [hsep hij,hni.2.2.2.1,hnj.2.2.1]
  · linarith [hsep hji,hnj.2.2.2.1,hni.2.2.1]

/-- The signed sum over the union is an exact sum of signed full periods. -/
theorem sum_population {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) (f : ℕ → ℂ) :
    ∑ n ∈ population v y, f n = ∑ i ∈ Finset.range (periodCount y),
      ∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n := by
  apply Finset.sum_biUnion
  intro i hi j hj hij
  exact disjoint_periods hv hy hi hj hij

/-- The factorial radial weight is decreasing to the right of its saddle. -/
theorem radial_mono {N : ℕ} {v w : ℝ} (hv : 0 < v) (hs : 2*(N : ℝ) ≤ v)
    (hvw : v ≤ w) :
    Real.exp (-w/2)*w^N/N.factorial ≤ Real.exp (-v/2)*v^N/N.factorial := by
  have hw : 0 < w := hv.trans_le hvw
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hw hv)) (Nat.cast_nonneg N)
  rw [Real.log_div hw.ne' hv.ne'] at hlog
  have hq : (N : ℝ)/v ≤ 1/2 := (div_le_iff₀ hv).mpr (by linarith)
  have hproduct := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hvw)
    (show (N : ℝ)/v-1/2 ≤ 0 by linarith)
  have he : (N : ℝ)*(w/v-1)-(w-v)/2 =
      (w-v)*((N : ℝ)/v-1/2) := by field_simp
  have hexp : -w/2+(N : ℝ)*Real.log w ≤ -v/2+(N : ℝ)*Real.log v := by linarith
  have hpow (t : ℝ) (ht : 0 < t) : t^N = Real.exp ((N : ℝ)*Real.log t) := by
    rw [Real.exp_nat_mul,Real.exp_log ht]
  rw [hpow w hw,hpow v hv,← Real.exp_add,← Real.exp_add]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)

/-- All periods together have arbitrarily small relative signed cost,
with the original allocation, phase, and moving prime mask retained. -/
theorem eventually_period_cost_small {y ε : ℝ} (hy : 54 ≤ |y|) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (v L : ℝ),
      2*(N : ℝ) ≤ v → v ≤ 2*N+1/2 → Real.cos (y*v) = -1 →
      (67/100 : ℝ)*(v+1/2) ≤ L →
      (∀ i ∈ Finset.range (periodCount y), ∀ a ∈ ZetaRieszTransitionSixPeriod.cofactors (center v y i),
        ∀ p ∈ ZetaRieszAllowancePrimeBoxes.logPrimes
          (center v y i-Real.pi/|y|-Real.log a) (2*Real.pi/|y|), p ∈ A) →
      (∑ i ∈ Finset.range (periodCount y),
        |(∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re|) ≤
        ε*(Real.pi/(4*|y|))*(Real.exp (-v/2)*v^N/N.factorial) := by
  have hc : 0 < periodCount y := lt_of_lt_of_le (by decide : 0 < 5) (five_le_periodCount hy)
  have hcR : (0 : ℝ) < periodCount y := by exact_mod_cast hc
  have hy0 : 0 < |y| := by linarith
  filter_upwards [ZetaRieszTransitionSixPeriod.eventually_residual_population_small hy
    (div_pos hε hcR),eventually_ge_atTop (1000 : ℕ)] with N hN hlarge A v L hv hvu hpeak hL hA
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hrow (i : ℕ) (hi : i ∈ Finset.range (periodCount y)) := hN A (center v y i) L
    (hv.trans (center_bounds hi).1) (by linarith [(center_bounds (v := v) hi).2])
    ((center_phase (abs_pos.mp hy0) i).trans hpeak)
    (by linarith [(center_bounds (v := v) hi).2]) (hA i hi)
  calc
    _ ≤ ∑ i ∈ Finset.range (periodCount y),
        (ε/(periodCount y : ℝ))*(Real.pi/(4*|y|))*(Real.exp (-v/2)*v^N/N.factorial) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hrow i hi).trans (mul_le_mul_of_nonneg_left
        (radial_mono hv0 hv (center_bounds hi).1) (by positivity))
    _ = _ := by simp; field_simp

/-- All previous six-prime labels remain in the enlarged payment. -/
theorem previous_population_subset (v y : ℝ) :
    ZetaRieszTransitionSixPeriod.population v y ⊆ population v y := by
  intro n hn
  apply Finset.mem_biUnion.mpr
  refine ⟨0,by simp [periodCount],?_⟩
  simpa only [center,Nat.cast_zero,zero_mul,add_zero] using hn

/-- Every constituent has the original squarefree, count and prime-share masks. -/
theorem population_data {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) {n : ℕ}
    (hn : n ∈ population v y) :
    Squarefree n ∧ n.primeFactors.card = 6 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+1/2+Real.pi/|y| ∧
      (∀ a ∈ n.primeFactors, Real.log a ≤ (1189/2000 : ℝ)*Real.log n) := by
  obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
  have hd := ZetaRieszTransitionSixPeriod.population_data (hv.trans (center_bounds hi).1) hy hn
  exact ⟨hd.1,hd.2.1,by linarith [(center_bounds (v := v) hi).1,hd.2.2.1],
    by linarith [(center_bounds (v := v) hi).2,hd.2.2.2.1],hd.2.2.2.2⟩

/-- The extra periods contain actual labels eventually, not just formal sets. -/
theorem eventually_added_population_nonempty {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v →
      (population v y\ZetaRieszTransitionSixPeriod.population v y).Nonempty := by
  filter_upwards [ZetaRieszTransitionSixPeriod.eventually_added_population_nonempty hy,
    eventually_ge_atTop (100 : ℕ)] with N hN hlarge v hv
  have hNR : (100 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv100 : 100 ≤ v := by linarith
  have hc := five_le_periodCount hy
  have hi : 1 ∈ Finset.range (periodCount y) := Finset.mem_range.mpr (by omega)
  have hzero : 0 ∈ Finset.range (periodCount y) := Finset.mem_range.mpr (by omega)
  obtain ⟨n,hn⟩ := hN (center v y 1) (hv.trans (center_bounds hi).1)
  have hn' := (Finset.mem_sdiff.mp hn).1
  refine ⟨n,Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨1,hi,hn'⟩,?_⟩⟩
  intro hold
  have hd := disjoint_periods hv100 hy hzero hi (by decide : (0 : ℕ) ≠ 1)
  have hold' : n ∈ ZetaRieszTransitionSixPeriod.population (center v y 0) y := by
    simpa only [center,Nat.cast_zero,zero_mul,add_zero] using hold
  exact Finset.disjoint_left.mp hd hold' hn'

/-- The sum of signed period costs is paid on the actual dyadic core,
at exactly the previous one-period budget. -/
theorem eventually_signed_population_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (_hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (_hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+1/2 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      population v y ⊆ ZetaRieszParityPacket.coreBand u N K ∧
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        u^(N+1)*(∑ i ∈ Finset.range (periodCount y),
          |(∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y,
            ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
              (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re|) ≤
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|))) := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_period_cost_small hy (by norm_num : (0 : ℝ) < 1/100000)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszTransitionSixPeriod.eventually_owner_mem hu hU hy),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)), eventually_ge_atTop (32 : ℕ)] with j hraw hL hA hN hj
  intro v
  dsimp only
  intro hv hslo hshi _hlo _hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hv0 : 0 < v := by change 2*(N : ℝ) ≤ v at hslo; linarith
  have hy0 : 0 < |y| := by linarith
  have hpi : Real.pi/|y| ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  change 2*(137/200 : ℝ)*N ≤ L at hL
  have hLl : (67/100 : ℝ)*(v+1/2) ≤ L := by change v ≤ 2*(N : ℝ)+1/2 at hshi; linarith
  have hcore : population v y ⊆ ZetaRieszParityPacket.coreBand u N
      (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
    intro n hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    have hc := center_bounds (v := v) hi
    apply ZetaRieszTransitionSixPeriod.population_subset_core j hj hu hU hy
      (by change 2*(N : ℝ) ≤ v at hslo; linarith) (by linarith) ?_ ?_ hn
    · change (39/20 : ℝ)*N ≤ center v y i-Real.pi/|y|
      change 2*(N : ℝ) ≤ v at hslo
      linarith
    · change center v y i+Real.pi/|y| ≤ (203/100 : ℝ)*N
      change v ≤ 2*(N : ℝ)+1/2 at hshi
      linarith
  let V := Real.exp (-v/2)*v^N/N.factorial
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨hcore,V,hV,le_rfl,?_⟩
  have hb := hraw (ZetaRieszAnnulusJoint.intermediatePrimes u N) v L hslo hshi hv hLl
    (fun i hi => hA (center v y i) (hslo.trans (center_bounds hi).1)
      (by linarith [(center_bounds (v := v) hi).2]))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (show 0 ≤ u by linarith) _)).trans_eq
  congr 1
  dsimp only [V]
  field_simp
  dsimp only [N]
  ring

/-- An exact signed payment retains the favorable part of EVERY period. -/
theorem scaled_floor_after_signed_payment {S : Finset ℕ} (f : ℕ → ℂ)
    {v y a d g whole : ℝ} (ha : 0 ≤ a) (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (hD : population v y ⊆ S)
    (hcost : a*(∑ i ∈ Finset.range (periodCount y),
      |(∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re|) ≤ d)
    (hpaid : a*(∑ n ∈ S, f n).re+g ≤ whole) :
    a*((∑ n ∈ S\population v y, f n).re+
      ∑ i ∈ Finset.range (periodCount y),
        max (∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re 0)+g-d ≤ whole := by
  have he := congrArg Complex.re (Finset.sum_sdiff hD (f := f))
  rw [sum_population hv hy] at he
  simp only [Complex.add_re,Complex.re_sum] at he
  have hm : (∑ i ∈ Finset.range (periodCount y),
      max (∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re 0) ≤
      (∑ i ∈ Finset.range (periodCount y),
        (∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re)+
      (∑ i ∈ Finset.range (periodCount y),
        |(∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply max_le
    · linarith [abs_nonneg ((∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re)]
    · linarith [neg_abs_le ((∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re)]
  have hm' := mul_le_mul_of_nonneg_left hm ha
  have he' := congrArg (fun t => a*t) he
  simp only [Complex.re_sum] at hm' hcost hpaid ⊢
  nlinarith only [he',hm',hcost,hpaid]

/-- The matching upper payment retains every favorable negative period. -/
theorem scaled_ceiling_after_signed_payment {S : Finset ℕ} (f : ℕ → ℂ)
    {v y a d g whole : ℝ} (ha : 0 ≤ a) (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (hD : population v y ⊆ S)
    (hcost : a*(∑ i ∈ Finset.range (periodCount y),
      |(∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re|) ≤ d)
    (hpaid : whole ≤ a*(∑ n ∈ S, f n).re-g) :
    whole ≤ a*((∑ n ∈ S\population v y, f n).re+
      ∑ i ∈ Finset.range (periodCount y),
        min (∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re 0)-g+d := by
  have he := congrArg Complex.re (Finset.sum_sdiff hD (f := f))
  rw [sum_population hv hy] at he
  simp only [Complex.add_re,Complex.re_sum] at he
  have hm : (∑ i ∈ Finset.range (periodCount y),
        (∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re)-
      (∑ i ∈ Finset.range (periodCount y),
        |(∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re|) ≤
      (∑ i ∈ Finset.range (periodCount y),
        min (∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply le_min
    · linarith [abs_nonneg ((∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re)]
    · linarith [le_abs_self ((∑ n ∈ ZetaRieszTransitionSixPeriod.population (center v y i) y, f n).re)]
  have hm' := mul_le_mul_of_nonneg_left hm ha
  have he' := congrArg (fun t => a*t) he
  simp only [Complex.re_sum] at hm' hcost hpaid ⊢
  nlinarith only [he',hm',hcost,hpaid]

/-- The new squarefree six-prime population cannot overlap any supply cell,
without adding an ordering or numerical-cover premise. -/
theorem disjoint_supply {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (t h z : ℝ) (lo H : Fin 4 → ℝ) :
    Disjoint (population v y) (ZetaRieszJointPrimeCells.supplyCell t h z lo H) := by
  apply Finset.disjoint_left.mpr
  intro n hn hs
  have hd := population_data hv hy hn
  have hcard : n.primeFactors.card = n.primeFactorsList.length :=
    List.toFinset_card_of_nodup hd.1.nodup_primeFactorsList
  have hc := ZetaRieszJointTriplePayment.supply_count hs
  rw [ArithmeticFunction.cardFactors_apply,← hcard,hd.2.1] at hc
  omega

/-- Four-prime payments and the new six-prime payment have distinct labels. -/
theorem disjoint_adverse {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L t h z a : ℝ) :
    Disjoint (population v y) (ZetaRieszFourBoundaryCover.adversePopulation S L t h z a) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hf).2.2.1
  omega

/-- Full positive-five interior payments have no six-prime labels. -/
theorem disjoint_interior {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z δ : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveSignedPayment.periodPopulation S L v' z m δ) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- The small-prime five-factor boundary is disjoint from the six-primes. -/
theorem disjoint_head {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveBoundary.periodPopulation S L v' z m) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- Every prime share of the multiple periods is below the paid owner band. -/
theorem disjoint_owner {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S A : Finset ℕ) :
    Disjoint (population v y) (ZetaRieszJointOwnerPayment.population S A) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨_,_,hn1,_,p,hp,_,_,hlo,_⟩ := Finset.mem_filter.mp hf
  have hc := (population_data hv hy hn).2.2.2.2 p hp
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  nlinarith


/-- The multiple six-prime periods has no labels in the previously paid
balanced-triple population. -/
theorem disjoint_balanced {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (t h : ℝ) :
    Disjoint (population v y) (ZetaRieszBroadTripleBudget.population S t h) := by
  apply Finset.disjoint_left.mpr
  intro n hn hb
  have hc := (population_data hv hy hn).2.1
  have hb := (Finset.mem_filter.mp hb).2.2.1
  omega

/-- Nor can it overlap the previously paid unbalanced-triple period. -/
theorem disjoint_triple {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) :
    Disjoint (population v y) (ZetaRieszTriplePeriod.population v y) := by
  apply Finset.disjoint_left.mpr
  intro n hn ht
  have hc := (population_data hv hy hn).2.1
  have ht := (ZetaRieszTriplePeriod.population_data hv hy ht).2.1
  omega



end
end RiemannGaussian.ZetaRieszMultiPeriodSix
