/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit
import RiemannGaussian.ArithmeticOperatorCompositeRamanujanFreedom
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Complete primitive-residue Fourier projection audit

Primitive complex roots encode the literal reduced fractions modulo one.
The complete native Fourier row is proved equal to the divisor-form
Ramanujan row, not assumed to have that identification. At frequency one
the cutoff is exactly the original actual Möbius sum. Every complex
denominator weight, native quotient and proper prime-power coefficient
is retained. The inverse-zeta response detects every actual zero and has
no density pole. Fixed complete Fourier projection is therefore not an
independent arithmetic estimate. Ordered adjacent-gap and incomplete
multi-point observables are outside this collapse theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorFareyFourierAudit
noncomputable section
open Complex Filter Polynomial
open ArithmeticOperatorRamanujanAudit ArithmeticOperatorCompositeRamanujanFreedom
open scoped BigOperators Topology

/-- Complete primitive residues on the unit circle, with the unit
denominator (the fraction zero modulo one) retained. -/
def fourierRow (q k : ℕ) : ℂ := ∑ z ∈ primitiveRoots q ℂ, z^k

/-- The literal ordinary-integer cutoff; the weight can contain the
height phase, a factorial kernel and correlated denominator masks. -/
def packet (X k : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 X, w q*fourierRow q k

/-- The root encoding really is the reduced-residue exponential sum. -/
theorem fourierRow_eq_reduced {q : ℕ} (hq : 0<q) (k : ℕ) :
    fourierRow q k = ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      Complex.exp (2*Real.pi*I*((a : ℂ)/(q : ℂ)))^k := by
  classical
  let z := Complex.exp (2*Real.pi*I/(q : ℂ))
  have hz : IsPrimitiveRoot z q := Complex.isPrimitiveRoot_exp q hq.ne'
  let : NeZero q := ⟨hq.ne'⟩
  symm
  refine Finset.sum_bij (fun a _ => z^a) ?_ ?_ ?_ ?_
  · intro a ha
    exact (mem_primitiveRoots hq).mpr (hz.pow_of_coprime a (Finset.mem_filter.mp ha).2)
  · intro a ha b hb he
    exact hz.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) he
  · intro v hv
    obtain ⟨a,ha,hac,he⟩ := hz.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).mp hv)
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,hac⟩,he⟩
  · intro a _
    change _=(Complex.exp _^a)^k
    apply congrArg (fun v : ℂ => v^k)
    rw [←Complex.exp_nat_mul]
    congr 1
    ring

/-- Complete grid orthogonality, including frequencies divisible by the
denominator and the denominator one. -/
theorem grid_fourier {q : ℕ} (hq : 0<q) (k : ℕ) :
    (∑ z ∈ nthRootsFinset q (1 : ℂ), z^k)=if q ∣ k then (q : ℂ) else 0 := by
  classical
  let z := Complex.exp (2*Real.pi*I/(q : ℂ))
  have hz : IsPrimitiveRoot z q := Complex.isPrimitiveRoot_exp q hq.ne'
  have he : nthRootsFinset q (1 : ℂ)=(Finset.range q).image (fun a => z^a) := by
    rw [nthRootsFinset,hz.nthRoots_eq (one_pow q)]
    simp only [mul_one,Multiset.toFinset_map]
    congr 1
    ext a
    simp
  rw [he,Finset.sum_image (fun a ha b hb hab =>
    hz.pow_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab)]
  simp_rw [←pow_mul, mul_comm _ k, pow_mul]
  by_cases hd : q ∣ k
  · rw [ite_eq_left hd,hz.pow_eq_one_iff_dvd k |>.mpr hd]
    simp
  · rw [ite_eq_right hd]
    have hn : z^k-1≠0 := sub_ne_zero.mpr (fun h => hd ((hz.pow_eq_one_iff_dvd k).mp h))
    have hp : (z^k)^q=1 := by rw [←pow_mul,mul_comm k q,pow_mul,hz.pow_eq_one,one_pow]
    exact (mul_eq_zero.mp (by simpa [hp] using geom_sum_mul (z^k) q)).resolve_right hn

/-- Exact primitive-order partition of a complete additive grid. -/
theorem sum_divisors_fourierRow {q : ℕ} (hq : 0<q) (k : ℕ) :
    (∑ d ∈ q.divisors,fourierRow d k)=if q ∣ k then (q : ℂ) else 0 := by
  classical
  rw [←grid_fourier hq k,IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
    Finset.sum_biUnion (fun a _ b _ hab => IsPrimitiveRoot.disjoint hab)]
  rfl

/-- The native primitive Fourier row is the actual divisor Ramanujan
coefficient. No character identification or primitive-root assertion is
left as a premise. -/
theorem fourierRow_eq_ramanujan {q : ℕ} (hq : 0<q) (k : ℕ) :
    fourierRow q k=(ramanujanDivisor q k : ℂ) := by
  let g : ℕ → ℂ := fun d => if d ∣ k then (d : ℂ) else 0
  have hp := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => fourierRow d k) (g := g)).mp
      (fun d hd => sum_divisors_fourierRow hd k) q hq
  have hr := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (ramanujanDivisor d k : ℂ)) (g := g)).mp (by
      intro d hd
      rw [←Int.cast_sum,sum_divisors_ramanujan hd]
      simp [g]) q hq
  exact hp.symm.trans hr

/-- Frequency zero is the exact native primitive count. -/
theorem fourierRow_zero (q : ℕ) : fourierRow q 0=(q.totient : ℂ) := by
  simp [fourierRow,Complex.card_primitiveRoots]

/-- The first nonzero additive frequency is exactly actual Möbius,
including nonsquarefree denominators and all endpoints. -/
theorem fourierRow_one (q : ℕ) : fourierRow q 1=(ArithmeticFunction.moebius q : ℂ) := by
  by_cases hq : q=0
  · simp [hq,fourierRow]
  · rw [fourierRow_eq_ramanujan (Nat.pos_of_ne_zero hq),
      ramanujanDivisor_of_coprime (Nat.coprime_one_right q)]

/-- Complete Fourier aggregation has recovered the unpaid original
Möbius test, with its entire correlated weight unchanged. -/
theorem packet_one (X : ℕ) (w : ℕ → ℂ) :
    packet X 1 w=∑ q ∈ Finset.Icc 1 X,w q*(ArithmeticFunction.moebius q : ℂ) := by
  simp only [packet,fourierRow_one]

/-- Free inverse weights for the collapse audit only. These are NOT
asserted to count actual reduced fractions or obey actual Gamma data. -/
def freeRow (v : ℕ → ℂ) (q k : ℕ) : ℂ :=
  ∑ da ∈ q.divisorsAntidiagonal, v da.1*(if da.2 ∣ k then (da.2 : ℂ) else 0)

theorem fourierRow_eq_freeRow (q k : ℕ) :
    fourierRow q k=freeRow (fun n => (ArithmeticFunction.moebius n : ℂ)) q k := by
  by_cases hq : q=0
  · simp [hq,fourierRow,freeRow]
  · exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun d => fourierRow d k)
      (g := fun d => if d ∣ k then (d : ℂ) else 0)).mp
      (fun d hd => sum_divisors_fourierRow hd k) q (Nat.pos_of_ne_zero hq)).symm

/-- All divisor fibers join for every free complex array and every
correlated denominator weight. The cutoff and quotient are still literal. -/
theorem free_cutoff_eq_quotient (X k : ℕ) (v w : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 X,w q*freeRow v q k)=
      ∑ d ∈ Finset.Icc 1 X,∑ a ∈ Finset.Icc 1 (X/d),
        (if d ∣ k then (d : ℂ) else 0)*v a*w (d*a) := by
  have he (q : ℕ) : w q*freeRow v q k=
      ∑ da ∈ q.divisorsAntidiagonal,
        (if da.1 ∣ k then (da.1 : ℂ) else 0)*v da.2*w (da.1*da.2) := by
    rw [freeRow,Finset.mul_sum,
      Nat.sum_divisorsAntidiagonal' (f := fun a d => w q*(v a*
        (if d ∣ k then (d : ℂ) else 0))),
      Nat.sum_divisorsAntidiagonal (f := fun d a =>
        (if d ∣ k then (d : ℂ) else 0)*v a*w (d*a))]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    ring
  simp_rw [he]
  exact sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix X
    (fun d a => (if d ∣ k then (d : ℂ) else 0)*v a*w (d*a))

/-- The inverse coefficient is recovered unchanged even in the free
algebra. Such free coefficients are not primitive-point counts. -/
theorem freeRow_one {q : ℕ} (hq : 0<q) (v : ℕ → ℂ) : freeRow v q 1=v q := by
  classical
  unfold freeRow
  rw [Finset.sum_eq_single (q,1)]
  · simp
  · intro da hda hneq
    by_cases hd : da.2 ∣ 1
    · have h1 : da.2=1 := Nat.dvd_one.mp hd
      have hq' := (Nat.mem_divisorsAntidiagonal.mp hda).1
      rw [h1,mul_one] at hq'
      exact False.elim (hneq (Prod.ext hq' h1))
    · simp [hd]
  · intro hh
    exact False.elim (hh (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp,hq.ne'⟩))

theorem free_packet_one (X : ℕ) (v w : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 X,w q*freeRow v q 1)=∑ q ∈ Finset.Icc 1 X,w q*v q := by
  exact Finset.sum_congr rfl (fun q hq => by rw [freeRow_one (Finset.mem_Icc.mp hq).1])

/-- Exact native all-frequency collapse; a new estimate of this right
side is still needed. No prime inequality enters this reindexing. -/
theorem packet_eq_quotient (X k : ℕ) (w : ℕ → ℂ) :
    packet X k w=
      ∑ d ∈ Finset.Icc 1 X,∑ a ∈ Finset.Icc 1 (X/d),
        (if d ∣ k then (d : ℂ) else 0)*(ArithmeticFunction.moebius a : ℂ)*w (d*a) := by
  simp_rw [packet,fourierRow_eq_freeRow]
  exact free_cutoff_eq_quotient X k _ w

/-- Combining any finite frequency code before estimation does not
introduce another arithmetic constraint on the inverse weights. -/
theorem finite_code_collapse (X : ℕ) (K : Finset ℕ) (c v w : ℕ → ℂ) :
    (∑ k ∈ K,c k*∑ q ∈ Finset.Icc 1 X,w q*freeRow v q k)=
      ∑ a ∈ Finset.Icc 1 X,v a*
        (∑ d ∈ Finset.Icc 1 (X/a),
          w (a*d)*(∑ k ∈ K,c k*(if d ∣ k then (d : ℂ) else 0))) := by
  simp_rw [free_cutoff_eq_quotient,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := K)]
  have he : (∑ d ∈ Finset.Icc 1 X,∑ a ∈ Finset.Icc 1 (X/d),
      ∑ k ∈ K,c k*((if d ∣ k then (d : ℂ) else 0)*v a*w (d*a)))=
      ∑ q ∈ Finset.Icc 1 X,∑ da ∈ q.divisorsAntidiagonal,
        ∑ k ∈ K,c k*((if da.1 ∣ k then (da.1 : ℂ) else 0)*v da.2*w (da.1*da.2)) :=
    (sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix X _).symm
  rw [he]
  have hs (q : ℕ) : (∑ da ∈ q.divisorsAntidiagonal,
      ∑ k ∈ K,c k*((if da.1 ∣ k then (da.1 : ℂ) else 0)*v da.2*w (da.1*da.2)))=
      ∑ da ∈ q.divisorsAntidiagonal,
        v da.1*(w (da.1*da.2)*(∑ k ∈ K,c k*(if da.2 ∣ k then (da.2 : ℂ) else 0))) := by
    rw [Nat.sum_divisorsAntidiagonal (f := fun d a =>
      ∑ k ∈ K,c k*((if d ∣ k then (d : ℂ) else 0)*v a*w (d*a))),
      Nat.sum_divisorsAntidiagonal' (f := fun a d =>
        v a*(w (a*d)*(∑ k ∈ K,c k*(if d ∣ k then (d : ℂ) else 0))))]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm d (q/d)]
    ring
  simp_rw [hs]
  rw [sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix X
    (fun a d => v a*(w (a*d)*(∑ k ∈ K,c k*(if d ∣ k then (d : ℂ) else 0))))]
  simp only [←Finset.mul_sum]

/-- Continuation of the first Fourier frequency; the actual density
pole becomes a zero, while all genuine zeta-zero poles remain. -/
def response (s : ℂ) : ℂ := 1/riemannZeta s

/-- The defining prime arithmetic is used here, on the genuine Euler
domain only. No continued Dirichlet series is asserted in the strip. -/
theorem first_frequency_euler {s : ℂ} (hs : 1<s.re) :
    LSeries (fun q => fourierRow q 1) s=response s := by
  simp only [fourierRow_one,response]
  apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr
  rw [mul_comm,←LSeries_one_eq_riemannZeta hs]
  exact LSeries_one_mul_Lseries_moebius hs

/-- The original logarithmic height phase is retained, not averaged
away. This is still only a genuine Euler-domain identity. -/
theorem first_frequency_twisted_euler (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun q => fourierRow q 1*SuzukiCarryCorrelation.primePhase y q) s=
      response (s+I*y) := by
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase,first_frequency_euler]
  simpa only [add_re,mul_re,I_re,I_im,ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,
    add_zero] using hs

/-- Exact multiplicity-sensitive source at every actual nontrivial
zero. This is NOT an inferred cutoff asymptotic. -/
theorem actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun s : ℂ => (s-rho.1)^(analyticZetaZeroMultiplicity rho)*response s)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨g,hg,hg0,he⟩ := (analyticAt_riemannZeta_nontrivialZero rho).analyticOrderAt_ne_top.mp
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  have ha : AnalyticAt ℂ (fun s : ℂ => 1/g s) rho.1 := analyticAt_const.div hg hg0
  refine ⟨1/g rho.1,one_div_ne_zero hg0,?_⟩
  have heq : (fun s : ℂ => (s-rho.1)^(analyticZetaZeroMultiplicity rho)*response s)
      =ᶠ[𝓝[≠] rho.1] fun s => 1/g s := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      hg.continuousAt.eventually_ne hg0 |>.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with s hs hgs (hsn : s≠rho.1)
    rw [response,hs]
    simp only [smul_eq_mul]
    change (s-rho.1)^(analyticZetaZeroMultiplicity rho)*
      (1/((s-rho.1)^(analyticZetaZeroMultiplicity rho)*g s))=_
    field_simp [pow_ne_zero _ (sub_ne_zero.mpr hsn),hgs]
  exact (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- Intrinsic pole/density separation at the actual zeta pole. -/
theorem response_density_zero : Tendsto response (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
  have hn : Tendsto (fun s : ℂ => s-1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hc : Continuous (fun s : ℂ => s-1) := by fun_prop
    simpa only [sub_self] using hc.continuousAt (x := (1 : ℂ)) |>.tendsto.mono_left
      nhdsWithin_le_nhds
  have ht := hn.div riemannZeta_residue_one (by norm_num : (1 : ℂ)≠0)
  have he : (fun s : ℂ => (s-1)/((s-1)*riemannZeta s))=ᶠ[𝓝[≠] (1 : ℂ)] response := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : s≠1)
    simp [response,div_mul_eq_div_div,sub_ne_zero.mpr hs]
  have ht' : Tendsto (fun s : ℂ => (s-1)/((s-1)*riemannZeta s))
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    convert ht using 1
    simp
  exact ht'.congr' he

/-- Removability is stated as a genuine punctured analytic extension,
not continuity of the totalized inverse at a zero. -/
def RemovableAt (s : ℂ) : Prop :=
  ∃ g : ℂ → ℂ,AnalyticAt ℂ g s ∧ g=ᶠ[𝓝[≠] s] response

/-- This projected inverse response can be regularized in the strip
exactly when the original zeta value is nonzero. The desired arithmetic
regularization is therefore still a zero-free-strength input. -/
theorem response_removable_iff {s : ℂ} (hs0 : 0<s.re) (hs1 : s.re<1) :
    RemovableAt s ↔ riemannZeta s≠0 := by
  constructor
  · rintro ⟨g,hg,he⟩ hz
    let rho : NontrivialZetaZero := ⟨s,hz,by
      rintro ⟨n,hn⟩
      have h := congrArg Complex.re hn
      norm_num [Complex.mul_re] at h
      nlinarith [Nat.cast_nonneg (α := ℝ) n],by
      intro h
      rw [h] at hs1
      norm_num at hs1⟩
    obtain ⟨v,hv,ht⟩ := actual_zero_source rho
    have hzlim : Tendsto (fun z : ℂ => (z-s)^(analyticZetaZeroMultiplicity rho)*g z)
        (𝓝[≠] s) (𝓝 0) := by
      have hsub : Tendsto (fun z : ℂ => z-s) (𝓝[≠] s) (𝓝 0) := by
        have hc : Continuous (fun z : ℂ => z-s) := by fun_prop
        simpa only [sub_self] using hc.continuousAt (x := s) |>.tendsto.mono_left
          nhdsWithin_le_nhds
      have h := hsub.pow (analyticZetaZeroMultiplicity rho)
      have hh := h.mul (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      simpa [zero_pow (analyticZetaZeroMultiplicity_positive rho).ne'] using hh
    have hj : (fun z : ℂ => (z-s)^(analyticZetaZeroMultiplicity rho)*g z)=ᶠ[𝓝[≠] s]
        fun z => (z-s)^(analyticZetaZeroMultiplicity rho)*response z := by
      filter_upwards [he] with z hz
      rw [hz]
    exact hv (tendsto_nhds_unique ht (hzlim.congr' hj))
  · intro hs
    have hn : s≠1 := by intro h; rw [h] at hs1; norm_num at hs1
    exact ⟨response,analyticAt_const.div (analyticOn_riemannZeta s hn) hs,
      Filter.EventuallyEq.rfl⟩

/-- Even the weakest first-frequency literal bound is precisely the
corresponding original signed Möbius bound, not additional information
provided by Farey ordering or generic Fourier positivity. -/
theorem first_frequency_bound_iff (X : ℕ) (w : ℕ → ℂ) (B : ℝ) :
    ‖packet X 1 w‖≤B ↔
      ‖∑ q ∈ Finset.Icc 1 X,w q*(ArithmeticFunction.moebius q : ℂ)‖≤B := by
  rw [packet_one]

/-- No uniform free inverse-weight allowance follows from the complete
cutoff/Fourier join. Actual coprimality and actual Gamma data are additional
constraints, and are not claimed for these arbitrary free arrays. -/
theorem free_bound_iff (X : ℕ) (w : ℕ → ℂ) (B : ℝ) :
    (∀ v,‖∑ q ∈ Finset.Icc 1 X,w q*freeRow v q 1‖≤B) ↔
      0≤B ∧ ∀ q ∈ Finset.Icc 1 X,w q=0 := by
  simp_rw [free_packet_one]
  have he := ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff
    (Finset.Icc 1 X) w B
  simpa only [mul_comm] using he

end
end RiemannGaussian.ArithmeticOperatorFareyFourierAudit
