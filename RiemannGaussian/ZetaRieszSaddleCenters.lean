/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCutoffTransitionAudit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Two nearby evaluation centers on one unchanged prime mask

The two ordinates are changed before summing primes. The exact comparison
is a cosine of the factorial-order/logarithm mismatch, with the old phase
and every finite mask retained. Its selected-source model is evaluated
separately; no complete-leg limit is transferred through a prime mask.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSaddleCenters
open ZetaRieszFactorialCutoff ZetaRieszCutoffTransitionAudit

/-- An ordinate displacement, normalized separately at each factorial order. -/
def leg (theta delta : ℝ) (k : ℕ) (s : ℂ) (p : ℕ) : ℂ :=
  Complex.exp (Complex.I*(theta : ℂ)*(k : ℂ))*
    zetaPrimeLogKernel k (s+Complex.I*delta) p

/-- Both swapped analytic incidences use exactly the same primes and orders. -/
def pair (theta delta : ℝ) (i j : ℕ) (s : ℂ) (p q : ℕ) : ℂ :=
  (leg theta delta i s p*leg (-theta) (-delta) j s q+
    leg (-theta) (-delta) i s p*leg theta delta j s q)/2

/-- The order/logarithm correlation left by the two-center comparison. -/
def mismatch (theta delta : ℝ) (i j p q : ℕ) : ℝ :=
  theta*((i : ℝ)-j)-delta*(log p-log q)

theorem kernel_shift (k p : ℕ) (s d : ℂ) :
    zetaPrimeLogKernel k (s+d) p =
      Complex.exp (-d*(log p : ℂ))*zetaPrimeLogKernel k s p := by
  unfold zetaPrimeLogKernel zetaPrimeFeature
  rw [show -((s+d)*(log p : ℂ)) = -d*(log p : ℂ)+-(s*(log p : ℂ)) by ring,
    Complex.exp_add]
  ring

theorem leg_eq (theta delta : ℝ) (k p : ℕ) (s : ℂ) :
    leg theta delta k s p =
      Complex.exp (Complex.I*(theta*(k : ℝ)-delta*log p : ℝ))*
        zetaPrimeLogKernel k s p := by
  rw [leg,kernel_shift,←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact same-mask comparison, including repeated primes and order zero. -/
theorem pair_eq_cos_mul (theta delta : ℝ) (i j p q : ℕ) (s : ℂ) :
    pair theta delta i j s p q =
      (cos (mismatch theta delta i j p q) : ℂ)*
        (zetaPrimeLogKernel i s p*zetaPrimeLogKernel j s q) := by
  have hp : leg theta delta i s p*leg (-theta) (-delta) j s q =
      Complex.exp (Complex.I*(mismatch theta delta i j p q : ℂ))*
        (zetaPrimeLogKernel i s p*zetaPrimeLogKernel j s q) := by
    rw [leg_eq,leg_eq]
    rw [mul_mul_mul_comm,←Complex.exp_add]
    congr 2
    unfold mismatch
    push_cast
    ring
  have hn : leg (-theta) (-delta) i s p*leg theta delta j s q =
      Complex.exp (-(Complex.I*(mismatch theta delta i j p q : ℂ)))*
        (zetaPrimeLogKernel i s p*zetaPrimeLogKernel j s q) := by
    rw [leg_eq,leg_eq]
    rw [mul_mul_mul_comm,←Complex.exp_add]
    congr 2
    unfold mismatch
    push_cast
    ring
  rw [pair,hp,hn,←add_mul]
  have hc := Complex.two_cos (mismatch theta delta i j p q : ℂ)
  rw [←Complex.ofReal_cos] at hc
  rw [show Complex.I*(mismatch theta delta i j p q : ℂ)=
    (mismatch theta delta i j p q : ℂ)*Complex.I by ring,
    show -((mismatch theta delta i j p q : ℂ)*Complex.I)=
      -(mismatch theta delta i j p q : ℂ)*Complex.I by ring,←hc]
  ring

/-- An arbitrary literal mask is common to the original and shifted sums. -/
def original (E : Finset (ℕ×ℕ×ℕ×ℕ)) (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ e∈E,w e*zetaPrimeLogKernel e.2.1 s e.1*
    zetaPrimeLogKernel e.2.2.1 s e.2.2.2

/-- Two-center comparison with exactly the same arbitrary finite mask. -/
def comparison (E : Finset (ℕ×ℕ×ℕ×ℕ)) (w : ℕ×ℕ×ℕ×ℕ → ℂ)
    (s : ℂ) (theta delta : ℝ) : ℂ :=
  ∑ e∈E,w e*pair theta delta e.2.1 e.2.2.1 s e.1 e.2.2.2

/-- This cost remains signed and retains the original product phase. -/
def curvature (E : Finset (ℕ×ℕ×ℕ×ℕ)) (w : ℕ×ℕ×ℕ×ℕ → ℂ)
    (s : ℂ) (theta delta : ℝ) : ℂ :=
  ∑ e∈E,w e*(1-cos (mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2) : ℝ)*
    (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2)

/-- No price or completion is silently attached to the comparison. -/
theorem same_mask_ledger (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta : ℝ) :
    original E w s = comparison E w s theta delta+curvature E w s theta delta := by
  simp only [original,comparison,curvature,←Finset.sum_add_distrib,pair_eq_cos_mul]
  apply Finset.sum_congr rfl
  intro e _
  push_cast
  ring

/-- Each scalar curvature is nonnegative, but its old complex phase remains. -/
theorem curvature_scalar_nonneg (theta delta : ℝ) (i j p q : ℕ) :
    0≤1-cos (mismatch theta delta i j p q) := sub_nonneg.mpr (cos_le_one _)

/-- The real-center alternative, normalized at log saddle `k/u`. -/
def realLeg (u shift : ℝ) (k : ℕ) (s : ℂ) (p : ℕ) : ℂ :=
  Complex.exp ((shift*(k : ℝ)/u : ℝ) : ℂ)*
    zetaPrimeLogKernel k (s+(shift : ℂ)) p

/-- Both real-center incidences retain the same full complex prime phase. -/
def realPair (u shift : ℝ) (i j : ℕ) (s : ℂ) (p q : ℕ) : ℂ :=
  (realLeg u shift i s p*realLeg u (-shift) j s q+
    realLeg u (-shift) i s p*realLeg u shift j s q)/2

private theorem realLeg_eq (u shift : ℝ) (k p : ℕ) (s : ℂ) :
    realLeg u shift k s p=Complex.exp ((shift*((k : ℝ)/u-log p) : ℝ) : ℂ)*
      zetaPrimeLogKernel k s p := by
  rw [realLeg,kernel_shift,←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Real saddle matching amplifies the pointwise absolute amplitude.
This does not determine the sign of the retained complex phase. -/
theorem realPair_eq_cosh_mul (u shift : ℝ) (i j p q : ℕ) (s : ℂ) :
    realPair u shift i j s p q=
      (cosh (shift*(((i : ℝ)-j)/u-(log p-log q))) : ℂ)*
        (zetaPrimeLogKernel i s p*zetaPrimeLogKernel j s q) := by
  let a : ℝ := shift*(((i : ℝ)-j)/u-(log p-log q))
  have hp : realLeg u shift i s p*realLeg u (-shift) j s q=
      Complex.exp (a : ℂ)*(zetaPrimeLogKernel i s p*zetaPrimeLogKernel j s q) := by
    rw [realLeg_eq,realLeg_eq,mul_mul_mul_comm,←Complex.exp_add]
    congr 2
    dsimp [a]
    push_cast
    ring
  have hn : realLeg u (-shift) i s p*realLeg u shift j s q=
      Complex.exp (-(a : ℂ))*(zetaPrimeLogKernel i s p*zetaPrimeLogKernel j s q) := by
    rw [realLeg_eq,realLeg_eq,mul_mul_mul_comm,←Complex.exp_add]
    congr 2
    dsimp [a]
    push_cast
    ring
  rw [realPair,hp,hn,←add_mul,←Complex.two_cosh,←Complex.ofReal_cosh]
  change (2*(cosh a : ℂ))*(zetaPrimeLogKernel i s p*zetaPrimeLogKernel j s q)/2=_
  ring

theorem real_amplitude_factor_ge_one (u shift : ℝ) (i j p q : ℕ) :
    1≤cosh (shift*(((i : ℝ)-j)/u-(log p-log q))) := Real.one_le_cosh _

/-- Exact angular normalization at the selected pole; its linearization is
the usual factorial-saddle normalization `delta/u`. -/
def angle (u delta : ℝ) : ℝ := Complex.arg ((u : ℂ)+Complex.I*delta)

theorem angle_eq_arctan {u : ℝ} (hu : 0<u) (delta : ℝ) :
    angle u delta=arctan (delta/u) := by
  have hr : 0<((u : ℂ)+Complex.I*delta).re := by simpa using hu
  have hlo := (Complex.neg_pi_div_two_lt_arg_iff (z := (u : ℂ)+Complex.I*delta)).mpr
    (Or.inl hr)
  have hhi := (Complex.arg_lt_pi_div_two_iff (z := (u : ℂ)+Complex.I*delta)).mpr
    (Or.inl hr)
  have ht := Real.arctan_tan hlo hhi
  rw [Complex.tan_arg] at ht
  simpa [angle] using ht.symm

/-- The selected pole's radial attenuation after phase matching. -/
def radiusRatio (u delta : ℝ) : ℝ := u/‖(u : ℂ)+Complex.I*delta‖

/-- One exact pole contribution, kept separate from genuine prime sums. -/
def selectedLeg (m : ℕ) (u delta : ℝ) (k : ℕ) : ℂ :=
  Complex.exp ((angle u delta : ℂ)*Complex.I*(k+1 : ℕ))*
    (-(m : ℂ)*((u : ℂ)/((u : ℂ)+Complex.I*delta))^(k+1))

/-- Genuine selected-pole algebra, not a limit for a hard-masked prime sum. -/
theorem selectedLeg_eq (m : ℕ) {u : ℝ} (hu : 0<u) (delta : ℝ) (k : ℕ) :
    selectedLeg m u delta k=-(m : ℂ)*(radiusRatio u delta : ℂ)^(k+1) := by
  let z : ℂ := (u : ℂ)+Complex.I*delta
  have hz : z≠0 := by
    intro he
    have hr := congrArg Complex.re he
    dsimp [z] at hr
    simp at hr
    linarith
  have hn : (‖z‖ : ℂ)≠0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hp : Complex.exp ((angle u delta : ℂ)*Complex.I)*(u : ℂ)/z=
      (radiusRatio u delta : ℂ) := by
    have hh := Complex.norm_mul_exp_arg_mul_I z
    change (‖z‖ : ℂ)*Complex.exp ((angle u delta : ℂ)*Complex.I)=z at hh
    unfold radiusRatio
    push_cast
    change _=(u : ℂ)/(‖z‖ : ℂ)
    apply (div_eq_div_iff hz hn).mpr
    linear_combination (u : ℂ)*hh
  unfold selectedLeg
  rw [show (angle u delta : ℂ)*Complex.I*((k+1 : ℕ) : ℂ)=
    ((k+1 : ℕ) : ℂ)*((angle u delta : ℂ)*Complex.I) by ring,
    Complex.exp_nat_mul]
  change Complex.exp ((angle u delta : ℂ)*Complex.I)^(k+1)*
    (-(m : ℂ)*((u : ℂ)/z)^(k+1))=_
  calc
    _ = -(m : ℂ)*(Complex.exp ((angle u delta : ℂ)*Complex.I)*(u : ℂ)/z)^(k+1) := by
      simp only [div_eq_mul_inv,mul_pow]
      ring
    _ = _ := by rw [hp]

/-- The selected source array of the phase-matched two centers. -/
def selectedArray (m : ℕ) (r : ℝ) (k : ℕ) : ℂ := -(m : ℂ)*(r : ℂ)^(k+1)

/-- The logged ordinary-prime leg has the same order-dependent phase
normalization as the finite kernel above. No prime mask is completed. -/
def ordinaryLeg (u y delta : ℝ) (k : ℕ) : ℂ :=
  Complex.exp ((angle u delta : ℂ)*Complex.I*(k+1 : ℕ))*
    (u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*(y+delta))

/-- A polarized version of the existing evaluator, with every original
factorial index and the same moving length. -/
def mixedEvaluation (a b : ℕ→ℂ) (u : ℝ) (N K : ℕ) : ℂ :=
  (evaluation (fun k => a k+b k) u N K-
    evaluation a u N K-evaluation b u N K)/2

theorem mixedEvaluation_same (a : ℕ→ℂ) (u : ℝ) (N K : ℕ) :
    mixedEvaluation a a u N K=evaluation a u N K := by
  have hm : evaluation (fun k => a k+a k) u N K=4*evaluation a u N K := by
    unfold evaluation
    simp only [add_mul,mul_add,Finset.sum_add_distrib,add_div]
    ring
  rw [mixedEvaluation,hm]
  ring

/-- Exact comparison of the chosen new analytic data; the residual is
the original quadratic minus this value, not an earned floor payment. -/
def matchedEvaluation (u y delta : ℝ) (N K : ℕ) : ℂ :=
  mixedEvaluation (ordinaryLeg u y delta) (ordinaryLeg u y (-delta)) u N K

theorem evaluation_geometric (c r : ℂ) (u : ℝ) {N K : ℕ}
    (hN : 0<N) (hK : 2*K≤N) :
    evaluation (fun k => c*r^(k+1)) u N K=c^2*r^(N+1)*
      (1+((harmonic (N-K) : ℝ)-(harmonic K : ℝ) : ℂ)-
        r*((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)*
          ((harmonic (N+1) : ℝ)-(harmonic K : ℝ) : ℂ)) := by
  have ht : (∑ k∈Finset.range N,(c*r^(k+1))*(c*r^(N-1-k+1)))=
      (N : ℂ)*(c^2*r^(N+1)) := by
    calc
      _ = ∑ _k∈Finset.range N,c^2*r^(N+1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have he : (k+1)+(N-1-k+1)=N+1 := by
          have := Finset.mem_range.mp hk
          omega
        rw [←he,pow_add]
        ring
      _ = _ := by simp
  have hc : (∑ k∈ZetaRieszPairPrefixConvolution.centralOrders (N+1) K,
      (c*r^(k-1+1))*(c*r^(N-k+1))/((N+1-k : ℕ) : ℂ))=
      c^2*r^(N+1)*((harmonic (N-K) : ℝ)-(harmonic K : ℝ) : ℂ) := by
    have hr := congrArg (fun x : ℝ => (x : ℂ)) (central_reciprocal hK)
    push_cast at hr
    push_cast
    rw [←hr,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hb := (Finset.mem_filter.mp hk).2
    have he : (k-1+1)+(N-k+1)=N+1 := by omega
    rw [←he,pow_add]
    ring
  have hp : (∑ k∈Finset.Icc 1 (N+1-K),
      (c*r^(k-1+1))*(c*r^(N+1-k+1))/((N+2-k : ℕ) : ℂ))=
      c^2*r^(N+2)*((harmonic (N+1) : ℝ)-(harmonic K : ℝ) : ℂ) := by
    have hr := congrArg (fun x : ℝ => (x : ℂ)) (prefix_reciprocal (by omega : K≤N+1))
    push_cast at hr
    push_cast
    rw [←hr,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hb := Finset.mem_Icc.mp hk
    have he : (k-1+1)+(N+1-k+1)=N+2 := by omega
    rw [←he,pow_add]
    ring
  unfold evaluation
  dsimp only
  rw [ht,hc,hp]
  have hn : (N : ℂ)≠0 := by exact_mod_cast hN.ne'
  rw [pow_succ r (N+1)]
  field_simp [hn]

/-- The tested displacement tends to zero at the factorial saddle width. -/
def offset (eta : ℝ) (N : ℕ) : ℝ := eta/sqrt ((N : ℝ)+1)

/-- Exact damping of a normalized selected leg at either new center. -/
def damping (u eta : ℝ) (N : ℕ) : ℝ :=
  (sqrt (1+(eta/u)^2/((N : ℝ)+1)))⁻¹

theorem damping_pos (u eta : ℝ) (N : ℕ) : 0<damping u eta N := by
  unfold damping
  apply inv_pos.mpr
  apply sqrt_pos.mpr
  positivity

/-- The two formulas for the selected leg radius agree exactly. -/
theorem radiusRatio_offset {u : ℝ} (hu : 0<u) (eta : ℝ) (N : ℕ) :
    radiusRatio u (offset eta N)=damping u eta N := by
  have hn : 0<(N : ℝ)+1 := by positivity
  have hu2 : 0<u^2 := sq_pos_of_pos hu
  have hs : sqrt ((N : ℝ)+1)^2=(N : ℝ)+1 := sq_sqrt hn.le
  have hz : ‖(u : ℂ)+Complex.I*offset eta N‖^2=
      u^2+eta^2/((N : ℝ)+1) := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,zero_add,one_mul]
    dsimp [offset]
    have hd : (eta/sqrt ((N : ℝ)+1))^2=eta^2/((N : ℝ)+1) := by rw [div_pow,hs]
    nlinarith only [hd]
  have hz0 : 0<‖(u : ℂ)+Complex.I*offset eta N‖ := by
    have hp : 0<u^2+eta^2/((N : ℝ)+1) := by positivity
    nlinarith [norm_nonneg ((u : ℂ)+Complex.I*offset eta N)]
  have hd : damping u eta N^2=(1+(eta/u)^2/((N : ℝ)+1))⁻¹ := by
    unfold damping
    rw [inv_pow,sq_sqrt (by positivity)]
  have hr : radiusRatio u (offset eta N)^2=damping u eta N^2 := by
    rw [radiusRatio,div_pow,hz,hd]
    field_simp
  have hr0 : 0<radiusRatio u (offset eta N) := div_pos hu hz0
  nlinarith [damping_pos u eta N]

theorem damping_tendsto (u eta : ℝ) :
    Tendsto (damping u eta) atTop (𝓝 1) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hh := (((hn.const_div_atTop ((eta/u)^2)).const_add 1).sqrt).inv₀
    (by norm_num : sqrt (1+(0 : ℝ))≠0)
  change Tendsto (fun N : ℕ => (sqrt (1+(eta/u)^2/((N : ℝ)+1)))⁻¹) _ _
  simpa using hh

theorem offset_tendsto (eta : ℝ) : Tendsto (offset eta) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  change Tendsto (fun N : ℕ => eta/sqrt ((N : ℝ)+1)) _ _
  simpa only [Function.comp_def] using
    (Real.tendsto_sqrt_atTop.comp hn).const_div_atTop eta

/-- Literal prime-density saddle normalization differs from the selected
pole normalization; that small difference accumulates with the total order. -/
def physicalMismatch (u eta : ℝ) (N : ℕ) : ℝ :=
  2*offset eta N-arctan (offset eta N/u)

theorem physicalMismatch_ratio_tendsto {u eta : ℝ} (hu : 1/2<u) (heta : 0<eta) :
    Tendsto (fun N : ℕ => physicalMismatch u eta N/offset eta N) atTop
      (𝓝 (2-1/u)) := by
  have hup : 0<u := by linarith
  have hd (N : ℕ) : 0<offset eta N := div_pos heta (sqrt_pos.mpr (by positivity))
  have hv : Tendsto (fun N => offset eta N/u) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (offset_tendsto eta).div_const u,?_⟩
    exact Eventually.of_forall (fun N => by simpa using (div_pos (hd N) hup).ne')
  have hs : Tendsto (fun x : ℝ => arctan x/x) (𝓝[≠] 0) (𝓝 1) := by
    simpa [div_eq_mul_inv,mul_comm] using
      (Real.hasDerivAt_arctan 0).tendsto_slope_zero
  have hh := (tendsto_const_nhds (x := (2 : ℝ))).sub ((hs.comp hv).div_const u)
  apply hh.congr
  intro N
  dsimp [physicalMismatch]
  field_simp [(hd N).ne',hup.ne']

/-- Small individual center shifts do NOT imply a small accumulated phase.
This is a phase-geometry theorem, not a native prime-sum decay statement. -/
theorem physicalMismatch_accumulated_atTop {u eta : ℝ} (hu : 1/2<u) (heta : 0<eta) :
    Tendsto (fun N : ℕ => ((N : ℝ)+1)*physicalMismatch u eta N) atTop atTop := by
  have hup : 0<u := by linarith
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hm : Tendsto (fun N : ℕ => ((N : ℝ)+1)*offset eta N) atTop atTop := by
    apply ((Real.tendsto_sqrt_atTop.comp hn).const_mul_atTop heta).congr
    intro N
    dsimp [offset]
    have hs : sqrt ((N : ℝ)+1)^2=(N : ℝ)+1 := sq_sqrt (by positivity)
    field_simp
    nlinarith only [hs]
  have hl : 0<2-1/u := by
    have hh : 1/u<2 := (div_lt_iff₀ hup).mpr (by linarith)
    linarith
  have hh := (physicalMismatch_ratio_tendsto hu heta).pos_mul_atTop hl hm
  apply hh.congr
  intro N
  have hd : offset eta N≠0 := (div_pos heta (sqrt_pos.mpr (by positivity))).ne'
  field_simp [hd]

/-- Unlike the zero-width comparison, the saddle-width limit has a fixed
Gaussian damping factor. This statement concerns the exact selected model. -/
theorem damping_pow_tendsto (u eta : ℝ) :
    Tendsto (fun N : ℕ => damping u eta N^(N+1)) atTop
      (𝓝 (exp (-((eta/u)^2)/2))) := by
  have hp := (Real.tendsto_one_add_div_pow_exp ((eta/u)^2)).comp
    (tendsto_add_atTop_nat 1)
  have hs := hp.sqrt.inv₀ (ne_of_gt (sqrt_pos.mpr (exp_pos _)))
  have he : (sqrt (exp ((eta/u)^2)))⁻¹=exp (-((eta/u)^2)/2) := by
    rw [←exp_half,←exp_neg]
    congr 1
    ring
  rw [he] at hs
  apply hs.congr
  intro N
  change (sqrt ((1+(eta/u)^2/((N+1 : ℕ) : ℝ))^(N+1)))⁻¹=_
  have hsq : sqrt ((1+(eta/u)^2/((N+1 : ℕ) : ℝ))^(N+1))=
      sqrt (1+(eta/u)^2/((N+1 : ℕ) : ℝ))^(N+1) := by
    apply (sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [←pow_mul, Nat.mul_comm (N+1) 2, pow_mul, sq_sqrt (by positivity)]
  rw [hsq]
  simp [damping,inv_pow]

private theorem prefix_factor_tendsto {u : ℝ} (hu : 0<u) (hU : u≤3/5) :
    Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℝ)/(u*SquarefreeVaughanLogSource.length u N)*
      ((harmonic (N+1) : ℝ)-(harmonic (cutoff0 N) : ℝ))) atTop
      (𝓝 (log (32/13)/(-2*u*log u))) := by
  have hk : Tendsto cutoff0 atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (3*b)] with N hN
    dsimp [cutoff0]
    omega
  have hr := cutoff0_ratio.inv₀ (by norm_num : (13/32 : ℝ)≠0)
  have hr' : Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℝ)/(cutoff0 N : ℝ)) atTop
      (𝓝 (32/13)) := by simpa only [inv_div,Nat.cast_add,Nat.cast_one] using hr
  have hh := HarmonicIntervalLimit.tendsto_harmonic_difference
    (fun N => N+1) cutoff0 (tendsto_add_atTop_nat 1) hk (by norm_num) hr'
  convert (ZetaRieszLengthAsymptotic.tendsto_head_length_factor hu hU).mul hh using 1
  · funext N
    simp
  · ring

/-- Exact constant/source model of the two new analytic centers. This is
not an asymptotic theorem for the hard-masked ordinary prime arrays. -/
def selectedModel (m : ℕ) (u eta : ℝ) (N : ℕ) : ℂ :=
  evaluation (selectedArray m (damping u eta N)) u N (cutoff0 N)

theorem selectedModel_eq (m : ℕ) (u eta : ℝ) {N : ℕ} (hN : 8≤N) :
    selectedModel m u eta N=(damping u eta N : ℂ)^(N+1)*
      evaluation (fun _ => -(m : ℂ)) u N (cutoff0 N)+
      (1-damping u eta N : ℝ)*(m : ℂ)^2*(damping u eta N : ℂ)^(N+1)*
        (((N+1 : ℕ) : ℝ)/(u*SquarefreeVaughanLogSource.length u N)*
          ((harmonic (N+1) : ℝ)-(harmonic (cutoff0 N) : ℝ)) : ℝ) := by
  have hK0 : 2*cutoff0 N≤N := by
    have := cutoff_bounds hN
    omega
  unfold selectedModel selectedArray
  rw [evaluation_geometric _ _ _ (by omega) hK0,
    evaluation_const _ _ (by omega) hK0]
  push_cast
  ring

/-- The source is attenuated by new ordinate data, not a cutoff change.
The exact same-mask difference must still be estimated independently. -/
theorem selectedModel_tendsto (m : ℕ) {u : ℝ} (hu : 0<u) (hU : u≤3/5) (eta : ℝ) :
    Tendsto (selectedModel m u eta) atTop
      (𝓝 (((m : ℝ)^2*exp (-((eta/u)^2)/2)*source u (13/32) : ℝ) : ℂ)) := by
  have hp := Complex.continuous_ofReal.continuousAt.tendsto.comp (damping_pow_tendsto u eta)
  have hc := evaluation_const_tendsto (-(m : ℂ)) cutoff0 hu hU (by norm_num)
    (by norm_num) ((eventually_ge_atTop 8).mono fun N hN => by
      have := (cutoff_bounds hN).2.2.1
      have := (cutoff_bounds hN).2.2.2
      omega) cutoff0_ratio
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp (damping_tendsto u eta)
  have hf := Complex.continuous_ofReal.continuousAt.tendsto.comp (prefix_factor_tendsto hu hU)
  have he := ((((tendsto_const_nhds (x := (1 : ℂ))).sub hr).mul_const
    ((m : ℂ)^2)).mul hp).mul hf
  simp only [Complex.ofReal_one,sub_self,zero_mul] at he
  have hh := (hp.mul hc).add he
  have hlim : (exp (-((eta/u)^2)/2) : ℂ)*
      ((-(m : ℂ))^2*(source u (13/32) : ℂ))+0=
      (((m : ℝ)^2*exp (-((eta/u)^2)/2)*source u (13/32) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 8] with N hN
  simpa only [Function.comp_def,Complex.ofReal_sub,Complex.ofReal_one,
    Complex.ofReal_pow] using (selectedModel_eq m u eta hN).symm

/-- The model difference is source-sized whenever the offset is nonzero. -/
theorem selected_difference_tendsto (m : ℕ) {u : ℝ} (hu : 0<u) (hU : u≤3/5) (eta : ℝ) :
    Tendsto (fun N : ℕ => evaluation (fun _ => -(m : ℂ)) u N (cutoff0 N)-
      selectedModel m u eta N) atTop
      (𝓝 (((m : ℝ)^2*(1-exp (-((eta/u)^2)/2))*source u (13/32) : ℝ) : ℂ)) := by
  have hc := evaluation_const_tendsto (-(m : ℂ)) cutoff0 hu hU (by norm_num)
    (by norm_num) ((eventually_ge_atTop 8).mono fun N hN => by
      have := (cutoff_bounds hN).2.2.1
      have := (cutoff_bounds hN).2.2.2
      omega) cutoff0_ratio
  convert hc.sub (selectedModel_tendsto m hu hU eta) using 1
  push_cast
  ring

/-- Both pieces add to the old source exactly; no comparison credit is free. -/
theorem source_ledger (m : ℕ) (u eta : ℝ) :
    (m : ℝ)^2*exp (-((eta/u)^2)/2)*source u (13/32)+
      (m : ℝ)^2*(1-exp (-((eta/u)^2)/2))*source u (13/32)=
      (m : ℝ)^2*source u (13/32) := by ring

theorem original_source_eq (u : ℝ) :
    source u (13/32)=1-ZetaRieszMaskSupport.retainedCost u := by
  norm_num [source,ZetaRieszMaskSupport.retainedCost]
  ring

/-- Only the scalar selected model is bounded here. All actual carrier
and moving-center comparison errors remain explicit obligations. -/
theorem original_source_upper {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    source u (13/32)<(39967/500000 : ℝ) := by
  have hd := damping_bounds hu hU
  have hp : 0 < -2*u*log u := by linarith only [hd.1]
  have ha : log (19/13 : ℝ)<37949/100000 := by
    apply (log_lt_iff_lt_exp (by norm_num)).mpr
    have he := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤37949/100000) 10
    norm_num [Finset.sum_range_succ] at he
    linarith only [he]
  have hb : (450393/500000 : ℝ)<log (32/13) := by
    have hh := sum_range_le_log_div (by norm_num : (0 : ℝ)≤19/45)
      (by norm_num : (19/45 : ℝ)<1) 8
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_left ha.le hp.le
  have hn := mul_le_mul_of_nonneg_right hd.2
    (show (0 : ℝ)≤1+37949/100000-39967/500000 by norm_num)
  have hs : source u (13/32)=1+log (19/13 : ℝ)-log (32/13)/(-2*u*log u) := by
    norm_num [source]
  rw [hs]
  have hh : 1+log (19/13 : ℝ)-39967/500000<log (32/13)/(-2*u*log u) := by
    apply (lt_div_iff₀ hp).mpr
    nlinarith only [hm,hn,hb]
  linarith only [hh]

/-- A rational certificate for the tested 0.03 saddle-width damping. -/
theorem tested_attenuation_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    exp (-(((3/100 : ℝ)/u)^2)/2)≤(1000000/1001799 : ℝ) := by
  have hup : 0<u := by linarith
  have husq : 0<u^2 := sq_pos_of_pos hup
  have hupper : u≤(10001/20000 : ℝ) := hU
  have hsq : u^2≤(10001/20000 : ℝ)^2 := by nlinarith
  have heq : (((3/100 : ℝ)/u)^2)/2=(9/20000)/u^2 := by ring
  have ha : (1799/1000000 : ℝ)≤(((3/100 : ℝ)/u)^2)/2 := by
    rw [heq]
    apply (le_div_iff₀ husq).mpr
    nlinarith only [hsq]
  have he := Real.add_one_le_exp ((((3/100 : ℝ)/u)^2)/2)
  have hlow : (1001799/1000000 : ℝ)≤exp ((((3/100 : ℝ)/u)^2)/2) := by linarith
  rw [show -(((3/100 : ℝ)/u)^2)/2=-((((3/100 : ℝ)/u)^2)/2) by ring,exp_neg]
  simpa only [inv_div] using
    (inv_le_inv₀ (exp_pos _) (by norm_num : (0 : ℝ)<1001799/1000000)).mpr hlow

/-- Uniformly across the whole original strip the new source model is
below the target. This does NOT bound the original literal carrier. -/
theorem tested_source_lt_target {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    exp (-(((3/100 : ℝ)/u)^2)/2)*source u (13/32)<(399/5000 : ℝ) := by
  have hs := original_source_upper hu hU
  have hb := tested_attenuation_bound hu hU
  calc
    _ < exp (-(((3/100 : ℝ)/u)^2)/2)*(39967/500000) :=
      mul_lt_mul_of_pos_left hs (exp_pos _)
    _ ≤ (1000000/1001799)*(39967/500000) :=
      mul_le_mul_of_nonneg_right hb (by norm_num)
    _ < _ := by norm_num

/-- The source difference is not a vanishing error. This lower bound
is for the selected model, not an independent bound on actual primes. -/
theorem tested_difference_source_gt {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    (1/7000 : ℝ)<(1-exp (-(((3/100 : ℝ)/u)^2)/2))*source u (13/32) := by
  have hs := ZetaRieszPairFloorAllMultiplicity.target_lt_multiple_source hu hU
    (m := 1) (by omega)
  rw [←original_source_eq] at hs
  norm_num only [Nat.cast_one,one_pow,one_mul] at hs
  have hb := tested_attenuation_bound hu hU
  calc
    (1/7000 : ℝ)<(1799/1001799)*(399/5000) := by norm_num
    _ < (1799/1001799)*source u (13/32) :=
      mul_lt_mul_of_pos_left hs (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hb])
      (by linarith only [hs])

/-- Automatic `o(1)` payment is ruled out in the selected source model.
This does not refute a new independent arithmetic inequality. -/
theorem not_tendsto_selected_difference_zero {m : ℕ} (hm : 0 < m)
    {u : ℝ} (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ¬Tendsto (fun N : ℕ => evaluation (fun _ => -(m : ℂ)) u N (cutoff0 N)-
      selectedModel m u (3/100) N) atTop (𝓝 0) := by
  have hup : 0<u := by linarith only [hu]
  have huq : u≤3/5 := hU.trans (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have ht := selected_difference_tendsto m hup huq (3/100)
  have hp := tested_difference_source_gt hu hU
  have hmR : 0<(m : ℝ) := by exact_mod_cast hm
  have hpos : 0<(m : ℝ)^2*(1-exp (-(((3/100 : ℝ)/u)^2)/2))*source u (13/32) := by
    rw [mul_assoc]
    exact mul_pos (sq_pos_of_pos hmR) (by linarith only [hp])
  intro hz
  have he := tendsto_nhds_unique ht hz
  have hr := congrArg Complex.re he
  norm_num only [Complex.ofReal_re,Complex.zero_re] at hr
  linarith only [hpos,hr]

/-- The genuine completed comparison cost; it is signed and unpaid. -/
def completedComparisonCost (u y eta : ℝ) (N : ℕ) : ℂ :=
  evaluation (ZetaRieszPairPrimePowerPayment.ordinaryArray u y) u N (cutoff0 N)-
    matchedEvaluation u y (offset eta N) N (cutoff0 N)

/-- The existing literal carrier is unchanged. Only its previously paid
whole-mask/diagonal error is removed; the new analytic comparison cost stays. -/
theorem norm_original_sub_joinedComparison_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (eta : ℝ) {N : ℕ} (hN : 65536≤N) :
    ‖ZetaRieszPairPrefixPayment.prefixPairDefect u y N-
      (matchedEvaluation u y (offset eta N) N (cutoff0 N)+
        completedComparisonCost u y eta N)‖≤
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget u N := by
  have he : matchedEvaluation u y (offset eta N) N (cutoff0 N)+
      completedComparisonCost u y eta N=
      ZetaRieszSelbergSourceAudit.harmonicEvaluation
        (ZetaRieszPairPrimePowerPayment.ordinaryArray u y) u N := by
    rw [completedComparisonCost]
    change _=evaluation (ZetaRieszPairPrimePowerPayment.ordinaryArray u y) u N (cutoff0 N)
    ring
  rw [he]
  exact ZetaRieszJoinedPhaseRadius.norm_prefix_sub_ordinary_le hu hU hy hN

end RiemannGaussian.ZetaRieszSaddleCenters
