/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorGrowingSchurAudit
import RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# A signed, phase-compatible actual-prime CRT completion obstruction

The literal successor incidence minus its periodic CRT mean is joined
BEFORE taking a real part. Two adjacent actual prime bands lie in the
same narrow height-phase sector but cannot meet consecutive native rows.
Their signed completion boundary is negative at linear scale, not just
large in norm. The full prime-power definition and literal mask remain.

This refutes a UNIFORM payment over bounded correlated masks. It does NOT
bound the whole unmasked correlation or any prescribed RH carrier, and
does not infer a nonlinear zero response from linear prime moments.
-/

namespace RiemannGaussian.ArithmeticOperatorSignedCrtAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGrowingSchurAudit ArithmeticOperatorCoprimeDiagonalAudit
open ArithmeticOperatorCrtBoundaryAudit SuzukiCarryCorrelation PrimeWindow
open scoped BigOperators Classical Topology ComplexConjugate

/-- Both endpoint ranges, every actual prime power, and the full phase. -/
def signedBoundary (X : ℕ) (y : ℝ) (W : ℕ → ℕ → ℂ) : ℂ :=
  ∑ d∈Finset.Icc 1 (X+1),∑ e∈Finset.Icc 1 (X+1),
    W d e*((ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d)*
      conj ((ArithmeticFunction.vonMangoldt e : ℂ)*primePhase y e)*
      (((incidenceCount X 1 d e : ℝ)-crtMean X d e : ℝ) : ℂ)

/-- An arbitrary-array ledger, with no claim of Gamma compatibility. -/
theorem masked_boundary_identity (X : ℕ) (W : ℕ → ℕ → ℂ) (f g : ℕ → ℂ) :
    (∑ d∈Finset.Icc 1 (X+1),∑ e∈Finset.Icc 1 (X+1),
      W d e*f d*conj (g e)*(incidenceCount X 1 d e : ℂ))-
    (∑ d∈Finset.Icc 1 (X+1),∑ e∈Finset.Icc 1 (X+1),
      W d e*f d*conj (g e)*(crtMean X d e : ℂ))=
    ∑ d∈Finset.Icc 1 (X+1),∑ e∈Finset.Icc 1 (X+1),
      W d e*f d*conj (g e)*
        (((incidenceCount X 1 d e : ℝ)-crtMean X d e : ℝ) : ℂ) := by
  simp_rw [Complex.ofReal_sub,Complex.ofReal_natCast,mul_sub,Finset.sum_sub_distrib]

/-- Half of the previously proved phase-band width. -/
def halfWidth (y : ℝ) : ℝ := Real.exp (1/(8*|y|))

/-- The lower half of the native phase-compatible prime band. -/
def lowerPrimes (y : ℝ) (J : ℕ) : Finset ℕ :=
  primesInWindow (smallPhaseScale y J) (halfWidth y)

/-- The disjoint upper half, with its own literal floor endpoints. -/
def upperPrimes (y : ℝ) (J : ℕ) : Finset ℕ :=
  primesInWindow (halfWidth y*smallPhaseScale y J) (halfWidth y)

/-- Bounded correlated mask: nothing outside these exact two bands is paid. -/
def bandMask (y : ℝ) (J : ℕ) (d e : ℕ) : ℂ :=
  if d∈lowerPrimes y J ∧ e∈upperPrimes y J then 1 else 0

/-- An even ORIGINAL native cutoff, permitting the exact successor audit. -/
def rowQuarter (y : ℝ) (J : ℕ) : ℕ :=
  Nat.ceil (bandWidth y*smallPhaseScale y J/4)

/-- The complete even upper row endpoint, retained before CRT completion. -/
def rowCutoff (y : ℝ) (J : ℕ) : ℕ := 4*rowQuarter y J

theorem halfWidth_gt_one {y : ℝ} (hy : y≠0) : 1<halfWidth y :=
  Real.one_lt_exp_iff.mpr (div_pos (by norm_num)
    (mul_pos (by norm_num) (abs_pos.mpr hy)))

theorem halfWidth_sq {y : ℝ} (hy : y≠0) : (halfWidth y)^2=bandWidth y := by
  rw [pow_two,halfWidth,←Real.exp_add]
  unfold bandWidth
  congr 1
  field_simp [abs_ne_zero.mpr hy]
  ring

theorem bandWidth_lt_two {y : ℝ} (hy : 1≤|y|) : bandWidth y<2 := by
  have ha : 0< |y| := by linarith
  have hh : 1/(4*|y|)≤(1/4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*|y|)).mpr
    linarith
  have hh' : 1/(4*|y|)<Real.log 2 := hh.trans_lt (by linarith [Real.log_two_gt_d9])
  simpa [bandWidth] using (Real.exp_lt_exp.mpr hh').trans_eq
    (Real.exp_log (by norm_num : (0 : ℝ)<2))

theorem lower_subset_phase {y : ℝ} (hy : y≠0) (J : ℕ) :
    lowerPrimes y J⊆phasePrimes y J := by
  have hA := halfWidth_gt_one hy
  have hAB : halfWidth y≤bandWidth y := by rw [←halfWidth_sq hy]; nlinarith
  intro p hp
  obtain ⟨hi,hr⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨(Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono
    (mul_le_mul_of_nonneg_right hAB (Real.exp_pos _).le))) hi,hr⟩

theorem upper_subset_phase {y : ℝ} (hy : y≠0) (J : ℕ) :
    upperPrimes y J⊆phasePrimes y J := by
  have hA := halfWidth_gt_one hy
  intro p hp
  obtain ⟨hi,hr⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  have he : halfWidth y*(halfWidth y*smallPhaseScale y J)=
      bandWidth y*smallPhaseScale y J := by rw [←halfWidth_sq hy]; ring
  rw [he] at hi
  have hb : smallPhaseScale y J≤halfWidth y*smallPhaseScale y J := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA.le
      (show 0≤smallPhaseScale y J from (Real.exp_pos _).le)
  exact ⟨(Finset.Ioc_subset_Ioc (Nat.floor_mono hb) le_rfl) hi,hr⟩

theorem lower_upper_distinct {y : ℝ} (hy : y≠0) {J p q : ℕ}
    (hp : p∈lowerPrimes y J) (hq : q∈upperPrimes y J) : p<q := by
  have hA := zero_lt_one.trans (halfWidth_gt_one hy)
  obtain ⟨_,hu,_⟩ := mem_primesInWindow_bounds (Real.exp_pos _).le hA.le hp
  obtain ⟨hl,_,_⟩ := mem_primesInWindow_bounds (mul_pos hA (Real.exp_pos _)).le hA.le hq
  exact_mod_cast hu.trans_lt hl

theorem bandMask_norm_le (y : ℝ) (J d e : ℕ) : ‖bandMask y J d e‖≤1 := by
  unfold bandMask
  split_ifs <;> norm_num

theorem rowCutoff_tendsto {y : ℝ} (hy : y≠0) : Tendsto (rowCutoff y) atTop atTop := by
  have ht := ((phaseScale_tendsto hy).const_mul_atTop
    (zero_lt_one.trans (bandWidth_gt_one hy))).atTop_div_const (by norm_num : (0 : ℝ)<4)
  exact tendsto_atTop_mono (fun J => by change rowQuarter y J≤4*rowQuarter y J; omega)
    (tendsto_nat_ceil_atTop.comp ht)

/-- Exact physical containment, including the even upper endpoint. -/
theorem eventually_native_bounds {y : ℝ} (hy : 1≤|y|) :
    ∀ᶠ J in atTop,1≤rowQuarter y J ∧ (rowCutoff y J : ℝ)≤3*smallPhaseScale y J ∧
      ∀ p∈phasePrimes y J,2*rowQuarter y J<p ∧ p≤rowCutoff y J := by
  have hy0 : y≠0 := by intro he; subst y; norm_num at hy
  have hB := bandWidth_lt_two hy
  have hg : 0<2-bandWidth y := by linarith
  filter_upwards [(phaseScale_tendsto hy0).eventually
    (eventually_gt_atTop (max 4 (4/(2-bandWidth y))))] with J hx
  have hx4 : 4<smallPhaseScale y J := (le_max_left _ _).trans_lt hx
  have hxg : 4/(2-bandWidth y)<smallPhaseScale y J := (le_max_right _ _).trans_lt hx
  have hpos : 0<smallPhaseScale y J := Real.exp_pos _
  have hH : (rowQuarter y J : ℝ)<bandWidth y*smallPhaseScale y J/4+1 :=
    Nat.ceil_lt_add_one (by unfold bandWidth smallPhaseScale; positivity)
  have hHU : bandWidth y*smallPhaseScale y J/4≤(rowQuarter y J : ℝ) := Nat.le_ceil _
  have hH1 : 1≤rowQuarter y J := Nat.one_le_ceil_iff.mpr (by
    unfold bandWidth smallPhaseScale
    positivity)
  refine ⟨hH1,?_,?_⟩
  · simp only [rowCutoff,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith
  · intro p hp
    obtain ⟨_,hl,hu⟩ := phase_prime_bounds hy0 hp
    have hsmall := (div_lt_iff₀ hg).mp hxg
    have hlow : (2*rowQuarter y J : ℕ)<p := by
      have hr : 2*(rowQuarter y J : ℝ)<(p : ℝ) := by nlinarith
      exact_mod_cast hr
    have hupper : p≤rowCutoff y J := by
      have hr : (p : ℝ)≤4*(rowQuarter y J : ℝ) := by linarith
      exact_mod_cast hr
    exact ⟨hlow,hupper⟩

/-- Exact height-phase product, with no norm or phase conjugation of the packet. -/
theorem prime_phase_pair_re (y : ℝ) (p q : ℕ) :
    (primePhase y p*conj (primePhase y q)).re=
      Real.cos (y*(Real.log q-Real.log p)) := by
  have he : primePhase y p*conj (primePhase y q)=
      Complex.exp (Complex.I*(y*(Real.log (q : ℝ)-Real.log (p : ℝ)) : ℝ)) := by
    unfold primePhase
    rw [←Complex.exp_conj,←Complex.exp_add]
    congr 1
    simp only [map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  rw [he,Complex.exp_re]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,mul_zero,
    zero_add,sub_zero,Real.exp_zero]

/-- The adjacent phase halves retain a positive joint REAL correlation. -/
theorem phase_pair_real_lower {y : ℝ} (hy : y≠0) {J p q : ℕ}
    (hp : p∈lowerPrimes y J) (hq : q∈upperPrimes y J) :
    (1/2 : ℝ)≤(primePhase y p*conj (primePhase y q)).re := by
  obtain ⟨ha0,ha1⟩ := phase_angle_bounds hy (lower_subset_phase hy J hp)
  obtain ⟨hb0,hb1⟩ := phase_angle_bounds hy (upper_subset_phase hy J hq)
  have hd : (y*(Real.log q-Real.log p))^2≤1/16 := by
    have hh : -(1/4 : ℝ)≤|y| *(Real.log q-Real.log p) ∧
        |y| *(Real.log q-Real.log p)≤1/4 := by constructor <;> nlinarith
    have hs : (|y| *(Real.log q-Real.log p))^2≤1/16 := by nlinarith [sq_nonneg (|y| *(Real.log q-Real.log p))]
    simpa only [mul_pow,sq_abs] using hs
  rw [prime_phase_pair_re]
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := y*(Real.log q-Real.log p))]

/-- The literal boundary of one actual pair, before any estimate. -/
def boundaryAtom (X : ℕ) (y : ℝ) (p q : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt p : ℂ)*primePhase y p)*
    conj ((ArithmeticFunction.vonMangoldt q : ℂ)*primePhase y q)*
    (((incidenceCount X 1 p q : ℝ)-crtMean X p q : ℝ) : ℂ)

/-- Exact simultaneous-incidence failure, actual prime weights and full phase. -/
theorem boundaryAtom_prime_eq {H p q : ℕ} (hH : 1≤H) (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hpl : 2*H<p) (hql : 2*H<q) (hpu : p≤4*H) (y : ℝ) :
    boundaryAtom (4*H) y p q=
      -((((4*H : ℕ) : ℝ)/((p : ℝ)*q)*Real.log p*Real.log q : ℝ) : ℂ)*
        (primePhase y p*conj (primePhase y q)) := by
  rw [boundaryAtom,incidenceCount_large_odd_primes hH hp hq hpl hql hpu,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    ArithmeticFunction.vonMangoldt_apply_prime hq,crtMean,
    ite_eq_left ((Nat.coprime_primes hp hq).mpr hpq)]
  simp only [Nat.cast_zero,zero_sub,map_mul,Complex.conj_ofReal,
    Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast]
  ring

theorem boundaryAtom_real_eq {H p q : ℕ} (hH : 1≤H) (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hpl : 2*H<p) (hql : 2*H<q) (hpu : p≤4*H) (y : ℝ) :
    (boundaryAtom (4*H) y p q).re=
      -(((4*H : ℕ) : ℝ)/((p : ℝ)*q)*Real.log p*Real.log q)*
        (primePhase y p*conj (primePhase y q)).re := by
  rw [boundaryAtom_prime_eq hH hp hq hpq hpl hql hpu]
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,neg_zero,zero_mul,sub_zero]

/-- The two native bands form one joined signed correlation, not an
allowance for the unselected population. -/
def bandBoundary (y : ℝ) (J : ℕ) : ℂ :=
  ∑ p∈lowerPrimes y J,∑ q∈upperPrimes y J,boundaryAtom (rowCutoff y J) y p q

theorem signedBoundary_bandMask_eq {y : ℝ} (hy : y≠0) {J : ℕ}
    (hphys : ∀ p∈phasePrimes y J,p≤rowCutoff y J) :
    signedBoundary (rowCutoff y J) y (bandMask y J)=bandBoundary y J := by
  let V := Finset.Icc 1 (rowCutoff y J+1)
  have hsub (P : Finset ℕ) (hP : P⊆phasePrimes y J) : P⊆V := by
    intro p hp
    have hr := (phase_prime_bounds hy (hP hp)).1
    exact Finset.mem_Icc.mpr ⟨hr.one_le,(hphys p (hP hp)).trans (by omega)⟩
  have hf (P : Finset ℕ) (hP : P⊆V) : V.filter (fun p => p∈P)=P := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => hp.2,fun hp => ⟨hP hp,hp⟩⟩
  have hlow := hf (lowerPrimes y J) (hsub _ (lower_subset_phase hy J))
  have hupp := hf (upperPrimes y J) (hsub _ (upper_subset_phase hy J))
  have he (d e : ℕ) : bandMask y J d e*
      ((ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d)*
      conj ((ArithmeticFunction.vonMangoldt e : ℂ)*primePhase y e)*
      (((incidenceCount (rowCutoff y J) 1 d e : ℝ)-crtMean (rowCutoff y J) d e : ℝ) : ℂ)=
    if d∈lowerPrimes y J then
      if e∈upperPrimes y J then boundaryAtom (rowCutoff y J) y d e else 0 else 0 := by
    by_cases hd : d∈lowerPrimes y J <;> by_cases hh : e∈upperPrimes y J <;>
      simp [bandMask,boundaryAtom,hd,hh]
  unfold signedBoundary bandBoundary
  change (∑ d∈V,∑ e∈V,_)=_
  simp_rw [he,Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [←Finset.sum_filter,hlow]
  apply Finset.sum_congr rfl
  intro p _
  rw [←Finset.sum_filter,hupp]

/-- Pointwise sign is used only inside this exact phase-compatible mask.
The whole complex pair is joined before reading its real part. -/
theorem boundaryAtom_band_upper {y : ℝ} (hy : y≠0) {J : ℕ}
    (hH : 1≤rowQuarter y J)
    (hphys : ∀ p∈phasePrimes y J,2*rowQuarter y J<p ∧ p≤rowCutoff y J)
    {p q : ℕ} (hp : p∈lowerPrimes y J) (hq : q∈upperPrimes y J) :
    (boundaryAtom (rowCutoff y J) y p q).re≤
      -(Real.log p*Real.log q/(2*(rowCutoff y J : ℝ))) := by
  have hpP := (phase_prime_bounds hy (lower_subset_phase hy J hp)).1
  have hqP := (phase_prime_bounds hy (upper_subset_phase hy J hq)).1
  obtain ⟨hpl,hpu⟩ := hphys p (lower_subset_phase hy J hp)
  obtain ⟨hql,hqu⟩ := hphys q (upper_subset_phase hy J hq)
  rw [show rowCutoff y J=4*rowQuarter y J from rfl,
    boundaryAtom_real_eq hH hpP hqP (lower_upper_distinct hy hp hq).ne hpl hql hpu]
  have hX0 : (0 : ℝ)<((4*rowQuarter y J : ℕ) : ℝ) := by positivity
  have hp0 : (0 : ℝ)<(p : ℝ) := by exact_mod_cast hpP.pos
  have hq0 : (0 : ℝ)<(q : ℝ) := by exact_mod_cast hqP.pos
  have hpR : (p : ℝ)≤((4*rowQuarter y J : ℕ) : ℝ) := by exact_mod_cast hpu
  have hqR : (q : ℝ)≤((4*rowQuarter y J : ℕ) : ℝ) := by exact_mod_cast hqu
  have hd : 1/((4*rowQuarter y J : ℕ) : ℝ)≤
      ((4*rowQuarter y J : ℕ) : ℝ)/((p : ℝ)*q) := by
    apply (div_le_div_iff₀ hX0 (mul_pos hp0 hq0)).mpr
    simpa only [one_mul] using mul_le_mul hpR hqR hq0.le hX0.le
  have hc := mul_le_mul hd (phase_pair_real_lower hy hp hq)
    (by norm_num : (0 : ℝ)≤1/2)
    (div_nonneg hX0.le (mul_pos hp0 hq0).le)
  have hlogs : 0≤Real.log p*Real.log q :=
    mul_nonneg (Real.log_nonneg (by exact_mod_cast hpP.one_le))
      (Real.log_nonneg (by exact_mod_cast hqP.one_le))
  have hh := mul_le_mul_of_nonneg_right hc hlogs
  convert neg_le_neg hh using 1 <;> ring

/-- All pair incidences are summed BEFORE the signed logarithmic mass
is used. Nothing is asserted about an unmasked completion. -/
theorem bandBoundary_real_upper {y : ℝ} (hy : y≠0) {J : ℕ}
    (hH : 1≤rowQuarter y J)
    (hphys : ∀ p∈phasePrimes y J,2*rowQuarter y J<p ∧ p≤rowCutoff y J) :
    (bandBoundary y J).re≤
      -((∑ p∈lowerPrimes y J,Real.log p)*(∑ q∈upperPrimes y J,Real.log q)/
        (2*(rowCutoff y J : ℝ))) := by
  rw [bandBoundary,Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc
    _ ≤ ∑ p∈lowerPrimes y J,∑ q∈upperPrimes y J,
        -(Real.log p*Real.log q/(2*(rowCutoff y J : ℝ))) :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq =>
        boundaryAtom_band_upper hy hH hphys hp hq))
    _ = _ := by
      symm
      simp only [Finset.sum_neg_distrib,Finset.sum_div,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]

theorem eventually_two_log_masses {y : ℝ} (hy : y≠0) :
    ∀ᶠ J in atTop,
      (halfWidth y-1)/2*smallPhaseScale y J≤∑ p∈lowerPrimes y J,Real.log p ∧
      (halfWidth y-1)/2*smallPhaseScale y J≤∑ q∈upperPrimes y J,Real.log q := by
  have hA := halfWidth_gt_one hy
  have ht := (theta_interval_div_tendsto (zero_lt_one.trans hA)).comp (phaseScale_tendsto hy)
  have ht' := (theta_interval_div_tendsto (zero_lt_one.trans hA)).comp
    ((phaseScale_tendsto hy).const_mul_atTop (zero_lt_one.trans hA))
  have hl := ht.eventually (eventually_gt_nhds
    (by linarith : (halfWidth y-1)/2<halfWidth y-1))
  have hu := ht'.eventually (eventually_gt_nhds
    (by linarith : (halfWidth y-1)/2<halfWidth y-1))
  filter_upwards [hl,hu] with J hl hu
  have hx0 : 0<smallPhaseScale y J := Real.exp_pos _
  have hl' := (lt_div_iff₀ hx0).mp hl
  have hu' := (lt_div_iff₀ (mul_pos (zero_lt_one.trans hA) hx0)).mp hu
  rw [←sum_log_primesInWindow hx0.le hA.le] at hl'
  rw [←sum_log_primesInWindow (mul_pos (zero_lt_one.trans hA) hx0).le hA.le] at hu'
  refine ⟨hl'.le,?_⟩
  apply le_trans ?_ hu'.le
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0≤(halfWidth y-1)/2)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hA.le hx0.le

/-- An explicit POSITIVE height-dependent linear cost for this mask. -/
def linearCost (y : ℝ) : ℝ := (halfWidth y-1)^2/72

theorem linearCost_pos {y : ℝ} (hy : y≠0) : 0<linearCost y := by
  unfold linearCost
  exact div_pos (sq_pos_of_pos (by linarith [halfWidth_gt_one hy])) (by norm_num)

/-- The SIGNED boundary is negative at LINEAR native scale. PNT merely
locates actual prime rows; their exact phases reinforce rather than cancel. -/
theorem eventually_signed_boundary_lower {y : ℝ} (hy : 1≤|y|) :
    ∀ᶠ J in atTop,linearCost y*(rowCutoff y J : ℝ)≤
      -(signedBoundary (rowCutoff y J) y (bandMask y J)).re := by
  have hy0 : y≠0 := by intro he; subst y; norm_num at hy
  filter_upwards [eventually_native_bounds hy,eventually_two_log_masses hy0] with J hN hM
  obtain ⟨hH,hX,hphys⟩ := hN
  rw [signedBoundary_bandMask_eq hy0 (fun p hp => (hphys p hp).2)]
  have hB := bandBoundary_real_upper hy0 hH hphys
  have hX0 : 0<(rowCutoff y J : ℝ) := by unfold rowCutoff; positivity
  have hgap : 0<halfWidth y-1 := by linarith [halfWidth_gt_one hy0]
  have hb0 : 0≤(halfWidth y-1)*(rowCutoff y J : ℝ)/6 := by positivity
  have hP : (halfWidth y-1)*(rowCutoff y J : ℝ)/6≤
      ∑ p∈lowerPrimes y J,Real.log p := by
    apply le_trans ?_ hM.1
    nlinarith
  have hQ : (halfWidth y-1)*(rowCutoff y J : ℝ)/6≤
      ∑ q∈upperPrimes y J,Real.log q := by
    apply le_trans ?_ hM.2
    nlinarith
  have hm := mul_le_mul hP hQ hb0 (hb0.trans hP)
  have hd := div_le_div_of_nonneg_right hm (by positivity : 0≤2*(rowCutoff y J : ℝ))
  have he : ((halfWidth y-1)*(rowCutoff y J : ℝ)/6)*
      ((halfWidth y-1)*(rowCutoff y J : ℝ)/6)/(2*(rowCutoff y J : ℝ))=
      linearCost y*(rowCutoff y J : ℝ) := by
    unfold linearCost
    field_simp
    ring
  rw [he] at hd
  exact hd.trans (by linarith)

/-- The native even cutoff is positive, including every small head. -/
theorem rowCutoff_pos (y : ℝ) (J : ℕ) : 0<rowCutoff y J := by
  have hH : 0<rowQuarter y J := Nat.one_le_ceil_iff.mpr (by
    unfold bandWidth smallPhaseScale
    positivity)
  unfold rowCutoff
  omega

/-- A true cofinal SIGNED obstruction at every sublinear power scale;
neither a norm allowance nor a hypothetical source inference is used. -/
theorem scaled_signed_boundary_tendsto_atTop {y beta : ℝ} (hy : 1≤|y|) (hb : beta<1) :
    Tendsto (fun J => (rowCutoff y J : ℝ)^(-beta)*
      (-(signedBoundary (rowCutoff y J) y (bandMask y J)).re)) atTop atTop := by
  have hy0 : y≠0 := by intro he; subst y; norm_num at hy
  have hX : Tendsto (fun J => (rowCutoff y J : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (rowCutoff_tendsto hy0)
  have ht := ((tendsto_rpow_atTop (by linarith : (0 : ℝ)<1-beta)).comp hX).const_mul_atTop
    (linearCost_pos hy0)
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_signed_boundary_lower hy] with J hJ
  have hx0 : (0 : ℝ)<(rowCutoff y J : ℝ) := by exact_mod_cast rowCutoff_pos y J
  have hh := mul_le_mul_of_nonneg_left hJ
    (Real.rpow_nonneg hx0.le (-beta))
  convert hh using 1
  dsimp only [Function.comp_def]
  rw [show 1-beta=(-beta)+1 by ring,Real.rpow_add hx0,Real.rpow_one]
  ring

theorem not_eventually_signed_subsource {y beta : ℝ} (hy : 1≤|y|) (hb : beta<1) (C : ℝ) :
    ¬∀ᶠ J in atTop,-(signedBoundary (rowCutoff y J) y (bandMask y J)).re≤
      C*(rowCutoff y J : ℝ)^beta := by
  intro hbound
  have ht := (scaled_signed_boundary_tendsto_atTop hy hb).eventually (eventually_gt_atTop C)
  obtain ⟨J,hJ,hlim⟩ := (hbound.and ht).exists
  have hx0 : (0 : ℝ)<(rowCutoff y J : ℝ) := by exact_mod_cast rowCutoff_pos y J
  have hh := mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hx0.le (-beta))
  have he : (rowCutoff y J : ℝ)^(-beta)*(C*(rowCutoff y J : ℝ)^beta)=C := by
    rw [mul_left_comm,←Real.rpow_add hx0,neg_add_cancel,Real.rpow_zero,mul_one]
  rw [he] at hh
  exact not_lt_of_ge hh hlim

/-- Uniform small SIGNED completion errors over all bounded correlated
masks are false for actual integer primes, even at one fixed height. -/
theorem not_eventually_uniform_signed_boundary_payment {y beta : ℝ}
    (hy : 1≤|y|) (hb : beta<1) (C : ℝ) :
    ¬∀ᶠ X : ℕ in atTop,∀ W : ℕ → ℕ → ℂ,(∀ d e,‖W d e‖≤1) →
      -(signedBoundary X y W).re≤C*(X : ℝ)^beta := by
  intro h
  have hy0 : y≠0 := by intro he; subst y; norm_num at hy
  have he := (rowCutoff_tendsto hy0).eventually h
  apply not_eventually_signed_subsource hy hb C
  filter_upwards [he] with J hJ
  exact hJ (bandMask y J) (bandMask_norm_le y J)

/-- The obstruction applies at the ACTUAL candidate zero height and
real part; its analytic multiplicity is not altered or inferred. -/
theorem no_uniform_signed_payment_at_campaign_zero (rho : NontrivialZetaZero)
    (hy : 54≤|rho.1.im|) (C : ℝ) :
    ¬∀ᶠ X : ℕ in atTop,∀ W : ℕ → ℕ → ℂ,(∀ d e,‖W d e‖≤1) →
      -(signedBoundary X rho.1.im W).re≤C*(X : ℝ)^rho.1.re :=
  not_eventually_uniform_signed_boundary_payment (by linarith)
    (NontrivialZetaZero.re_lt_one rho) C

end
end RiemannGaussian.ArithmeticOperatorSignedCrtAudit

#lint+ in RiemannGaussian.ArithmeticOperatorSignedCrtAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty signed CRT audit."
  logInfo m!"Signed-CRT audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-signed-crt"
  IO.FS.writeFile ".lake/arithmetic-operator-signed-crt/axioms.json"
    (Json.mkObj [("scope",toJson "actual phase-compatible signed CRT completion boundary is linear; uniform bounded-mask subsource payment refuted, prescribed RH packet still unestimated"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
