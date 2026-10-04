/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairFloorAllMultiplicity
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Actual-prime phase recurrence and the height/order quantifiers

At arbitrarily large heights, every fixed factorial-order evaluation of
actual complete ordinary-prime moments returns close to its value at a
prescribed starting height. The same statement holds for the existing
finite symmetric pair evaluator, with its signed coefficient and full
factorial prefix unchanged. It follows from recurrence in the countable
unit torus and absolute convergence, without an exposed-zero hypothesis.

This is a no-go for a uniform relative phase contraction at fixed order,
NOT a counterexample to the required fixed-height, cofinal-order floor.
No literal height-dependent support is completed here, no cofinal order
sequence is controlled, and no independent 399/5000 bound is supplied.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairPhaseRecurrence
open ZetaRieszSelbergSourceAudit ZetaRieszPairPrimePowerPayment
open ZetaRieszPairWholeCompletion ZetaRieszRemainingPrefix

/-- A single unbounded integer height sequence returns every member of a countable frequency family to phase one. The prime frequencies are not sampled. -/
theorem exists_countable_phase_recurrence (freq : ℕ → ℝ) :
    ∃ H : ℕ → ℕ, Tendsto H atTop atTop ∧
      ∀ i : ℕ, Tendsto (fun n => Circle.exp (-(H n : ℝ)*freq i)) atTop (𝓝 1) := by
  let x : ℕ → (ℕ → Circle) := fun n i => Circle.exp (-(n : ℝ)^2*freq i)
  obtain ⟨b, f, hf, hb⟩ := CompactSpace.tendsto_subseq x
  let H : ℕ → ℕ := fun n => f (n+1)^2-f n^2
  have hfstep (n : ℕ) : f n+1 ≤ f (n+1) := hf (by omega)
  have hfle (n : ℕ) : f n ≤ f (n+1) := by have := hfstep n; omega
  have hfg (n : ℕ) : n ≤ H n := by
    have hfn := hf.id_le n
    have he : H n+f n^2=f (n+1)^2 := Nat.sub_add_cancel (Nat.pow_le_pow_left (hfle n) 2)
    have hs := hfstep n
    change n ≤ f n at hfn
    nlinarith only [he,hs,hfn]
  refine ⟨H, tendsto_atTop_mono hfg tendsto_id, ?_⟩
  intro i
  have h0 : Tendsto (fun n => x (f n) i) atTop (𝓝 (b i)) :=
    (continuous_apply i).tendsto b |>.comp hb
  have h1 : Tendsto (fun n => x (f (n+1)) i) atTop (𝓝 (b i)) :=
    h0.comp (tendsto_add_atTop_nat 1)
  have he (n : ℕ) : Circle.exp (-(H n : ℝ)*freq i)=x (f (n+1)) i/x (f n) i := by
    rw [show (H n : ℝ)=(f (n+1) : ℝ)^2-(f n : ℝ)^2 by
      dsimp [H]
      rw [Nat.cast_sub (Nat.pow_le_pow_left (hfle n) 2)]
      norm_cast]
    dsimp [x]
    rw [←Circle.exp_sub]
    congr 1
    ring
  simpa only [he,div_self'] using h1.div' h0

/-- The genuine integer logarithms all recur along the same height sequence. This is pointwise in the integer label, not uniform in growing labels. -/
theorem exists_log_phase_recurrence :
    ∃ H : ℕ → ℕ, Tendsto H atTop atTop ∧
      ∀ m : ℕ, Tendsto (fun n => Complex.exp (((-(H n : ℝ)*Real.log m : ℝ) : ℂ)*Complex.I))
        atTop (𝓝 1) := by
  obtain ⟨H,hH,hp⟩ := exists_countable_phase_recurrence (fun m => Real.log m)
  refine ⟨H,hH,fun m => ?_⟩
  have hv := (continuous_subtype_val.tendsto (1 : Circle)).comp (hp m)
  change Tendsto (fun n => (Circle.exp (-(H n : ℝ)*Real.log m) : ℂ))
    atTop (𝓝 ((1 : Circle) : ℂ)) at hv
  simpa only [Circle.coe_exp,Circle.coe_one] using hv

/-- The complete factorial kernel has its exact phase split. No derivative order, prime or common label phase is discarded. -/
theorem kernel_phase_shift (k m : ℕ) (sigma y h : ℝ) :
    zetaPrimeLogKernel k ((sigma : ℂ)+Complex.I*(y+h)) m=
      zetaPrimeLogKernel k ((sigma : ℂ)+Complex.I*y) m*
        Complex.exp (((-h*Real.log m : ℝ) : ℂ)*Complex.I) := by
  unfold zetaPrimeLogKernel zetaPrimeFeature
  have he : -(((sigma : ℂ)+Complex.I*((y : ℂ)+(h : ℂ)))*(Real.log m : ℂ))=
      -(((sigma : ℂ)+Complex.I*(y : ℂ))*(Real.log m : ℂ))+
        ((-h*Real.log m : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [he,Complex.exp_add]
  ring

/-- Every fixed literal factorial atom returns to its starting value along the common recurrence sequence. -/
theorem kernel_recurrence (H : ℕ → ℕ)
    (hp : ∀ m : ℕ, Tendsto (fun n => Complex.exp (((-(H n : ℝ)*Real.log m : ℝ) : ℂ)*Complex.I))
      atTop (𝓝 1)) (k m : ℕ) (sigma y : ℝ) :
    Tendsto (fun n => zetaPrimeLogKernel k ((sigma : ℂ)+Complex.I*(y+(H n : ℝ))) m)
      atTop (𝓝 (zetaPrimeLogKernel k ((sigma : ℂ)+Complex.I*y) m)) := by
  simp_rw [kernel_phase_shift]
  simpa only [mul_one] using (hp m).const_mul (zetaPrimeLogKernel k ((sigma : ℂ)+Complex.I*y) m)

/-- Absolute convergence passes recurrence to the ENTIRE ordinary-prime logarithmic moment at each fixed order. This is not a moving-order limit. -/
theorem ordinary_log_recurrence (H : ℕ → ℕ)
    (hp : ∀ m : ℕ, Tendsto (fun n => Complex.exp (((-(H n : ℝ)*Real.log m : ℝ) : ℂ)*Complex.I))
      atTop (𝓝 1)) (k : ℕ) (y : ℝ) :
    Tendsto (fun n => zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*(y+(H n : ℝ))))
      atTop (𝓝 (zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y))) := by
  let f : ℕ → ℕ → ℂ := fun n m => if m.Prime then
    (ArithmeticFunction.vonMangoldt m : ℂ)*zetaPrimeLogKernel k
      (3/2+Complex.I*(y+(H n : ℝ))) m else 0
  let g : ℕ → ℂ := fun m => if m.Prime then
    (ArithmeticFunction.vonMangoldt m : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*y) m else 0
  have hs : Summable (fun m => ‖g m‖) :=
    (summable_zetaOrdinaryPrimeLogMoment k (by norm_num)).norm
  have hl (m : ℕ) : Tendsto (fun n => f n m) atTop (𝓝 (g m)) := by
    by_cases hm : m.Prime
    · simpa only [f,g,if_pos hm,Complex.ofReal_div,Complex.ofReal_ofNat] using (kernel_recurrence H hp k m (3/2) y).const_mul
        (ArithmeticFunction.vonMangoldt m : ℂ)
    · simpa only [f,g,if_neg hm] using (tendsto_const_nhds (x := (0 : ℂ)))
  have hb : ∀ᶠ n in atTop, ∀ m, ‖f n m‖ ≤ ‖g m‖ := by
    apply Eventually.of_forall
    intro n m
    by_cases hm : m.Prime
    · simp only [f,g,if_pos hm,norm_mul,norm_zetaPrimeLogKernel]
      norm_num
    · simp only [f,g,if_neg hm,norm_zero,le_refl]
  exact tendsto_tsum_of_dominated_convergence hs hl hb

/-- The already-defined finite exhaustive pair evaluator recurs with all signed coefficients, integer factorial cutoffs and the moving length unchanged. -/
theorem finitePrefix_recurrence (H : ℕ → ℕ)
    (hp : ∀ m : ℕ, Tendsto (fun n => Complex.exp (((-(H n : ℝ)*Real.log m : ℝ) : ℂ)*Complex.I))
      atTop (𝓝 1)) (u y : ℝ) (N P : ℕ) :
    Tendsto (fun n => finitePrefixPairDefect u (y+(H n : ℝ)) N P) atTop
      (𝓝 (finitePrefixPairDefect u y N P)) := by
  unfold finitePrefixPairDefect
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro m hm
  simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_ofNat] using
    (kernel_recurrence H hp N m (3/2) y).const_mul
      ((ZetaRieszPairPrefixPayment.prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N)
        (Real.log (ZetaRieszPrimeEndpoint.largestPrime m))
        (Real.log (ZetaRieszOwnedCells.ownerCofactor m)) : ℂ)-ZetaRieszLowCountSelbergAudit.selbergCoefficient m)

/-- All three collected channels of the existing whole signed evaluator recur jointly, including every low order. No channel is norm-paid separately. -/
theorem harmonicEvaluation_recurrence (H : ℕ → ℕ)
    (hp : ∀ m : ℕ, Tendsto (fun n => Complex.exp (((-(H n : ℝ)*Real.log m : ℝ) : ℂ)*Complex.I))
      atTop (𝓝 1)) (u y : ℝ) (N : ℕ) :
    Tendsto (fun n => harmonicEvaluation (ordinaryArray u (y+(H n : ℝ))) u N) atTop
      (𝓝 (harmonicEvaluation (ordinaryArray u y) u N)) := by
  have ha (k : ℕ) : Tendsto (fun n => ordinaryArray u (y+(H n : ℝ)) k) atTop
      (𝓝 (ordinaryArray u y k)) := by
    simpa only [ordinaryArray,Complex.ofReal_add] using
      (ordinary_log_recurrence H hp k y).const_mul ((u : ℂ)^(k+1))
  unfold harmonicEvaluation
  have ht := tendsto_finsetSum (Finset.range N) (fun k _ => (ha k).mul (ha (N-1-k)))
  have hc := tendsto_finsetSum (ZetaRieszPairPrefixConvolution.centralOrders (N+1) (13*N/32))
    (fun k _ => ((ha (k-1)).mul (ha (N-k))).div_const ((N+1-k : ℕ) : ℂ))
  have hp' := tendsto_finsetSum (Finset.Icc 1 (N+1-13*N/32))
    (fun k _ => ((ha (k-1)).mul (ha (N+1-k))).div_const ((N+2-k : ℕ) : ℂ))
  exact ((ht.div_const (N : ℂ)).add hc).sub
    (hp'.const_mul (((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)))

/-- Every finite symmetric pair response can return arbitrarily close to its prescribed value above any height threshold. No literal period mask is transferred. -/
theorem exists_arbitrarily_high_finitePrefix_approx (u y : ℝ) (N P : ℕ)
    {epsilon : ℝ} (he : 0 < epsilon) (Y : ℝ) :
    ∃ h : ℝ, Y ≤ h ∧
      ‖finitePrefixPairDefect u h N P-finitePrefixPairDefect u y N P‖ < epsilon := by
  obtain ⟨H,hH,hp⟩ := exists_log_phase_recurrence
  have hh : Tendsto (fun n => y+(H n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop y ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hH)
  have hevent := Metric.tendsto_nhds.mp (finitePrefix_recurrence H hp u y N P) epsilon he
  obtain ⟨n,hn,hclose⟩ := ((hh.eventually_ge_atTop Y).and hevent).exists
  refine ⟨y+(H n : ℝ),hn,?_⟩
  simpa only [dist_eq_norm] using hclose

/-- The COMPLETE ordinary-prime joined quadratic returns arbitrarily close at fixed order, including its exact integer endpoints and source normalization. -/
theorem exists_arbitrarily_high_joined_approx (u y : ℝ) (N : ℕ)
    {epsilon : ℝ} (he : 0 < epsilon) (Y : ℝ) :
    ∃ h : ℝ, Y ≤ h ∧
      ‖harmonicEvaluation (ordinaryArray u h) u N-
        harmonicEvaluation (ordinaryArray u y) u N‖ < epsilon := by
  obtain ⟨H,hH,hp⟩ := exists_log_phase_recurrence
  have hh : Tendsto (fun n => y+(H n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop y ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hH)
  have hevent := Metric.tendsto_nhds.mp (harmonicEvaluation_recurrence H hp u y N) epsilon he
  obtain ⟨n,hn,hclose⟩ := ((hh.eventually_ge_atTop Y).and hevent).exists
  refine ⟨y+(H n : ℝ),hn,?_⟩
  simpa only [dist_eq_norm] using hclose

/-- A genuine signed inequality: at arbitrarily large heights the existing whole evaluator is at least its starting real value minus any positive tolerance. -/
theorem arbitrarily_high_joined_signed_lower (u y : ℝ) (N : ℕ)
    {epsilon : ℝ} (he : 0 < epsilon) (Y : ℝ) :
    ∃ h : ℝ, Y ≤ h ∧
      (harmonicEvaluation (ordinaryArray u y) u N).re-epsilon <
        (harmonicEvaluation (ordinaryArray u h) u N).re := by
  obtain ⟨h,hh,hclose⟩ := exists_arbitrarily_high_joined_approx u y N he Y
  refine ⟨h,hh,?_⟩
  have ha := (Complex.abs_re_le_norm _).trans_lt hclose
  rw [Complex.sub_re] at ha
  linarith [(abs_lt.mp ha).1]

/-- If the starting real value is positive, no strict multiplicative contraction can hold uniformly above a height threshold at this FIXED order. -/
theorem not_uniform_joined_relative_contraction (u y : ℝ) (N : ℕ)
    (hpos : 0 < (harmonicEvaluation (ordinaryArray u y) u N).re)
    {c : ℝ} (hc : c < 1) (Y : ℝ) :
    ∃ h : ℝ, Y ≤ h ∧ c*(harmonicEvaluation (ordinaryArray u y) u N).re <
      (harmonicEvaluation (ordinaryArray u h) u N).re := by
  have he : 0 < (1-c)*(harmonicEvaluation (ordinaryArray u y) u N).re :=
    mul_pos (sub_pos.mpr hc) hpos
  obtain ⟨h,hh,hlo⟩ := arbitrarily_high_joined_signed_lower u y N he Y
  exact ⟨h,hh,by nlinarith only [hlo]⟩

end RiemannGaussian.ZetaRieszPairPhaseRecurrence
