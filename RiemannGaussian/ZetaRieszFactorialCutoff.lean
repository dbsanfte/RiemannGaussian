/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairFloorAllMultiplicity

/-!
# Fixed-order perturbation of the completed factorial cutoff

The order, height and completed ordinary/von Mangoldt arrays do not change.
Only the exact factorial prefix endpoint changes. No literal prime mask is
completed here. The selected quadratic source is retained, not norm-paid.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszFactorialCutoff
open ZetaRieszPairPrefixConvolution ZetaRieszSelbergSourceAudit
open ZetaRieszPairPrimePowerPayment ZetaRieszLengthAsymptotic

/-- The already-completed harmonic evaluator with an arbitrary factorial
prefix endpoint. All original array orders, including zero, are retained. -/
def evaluation (a : ℕ → ℂ) (u : ℝ) (N K : ℕ) : ℂ :=
  (∑ k ∈ Finset.range N, a k * a (N-1-k)) / (N : ℂ) +
    (∑ k ∈ centralOrders (N+1) K,
      a (k-1) * a (N-k) / ((N+1-k : ℕ) : ℂ)) -
    ((N+1 : ℕ) : ℂ) / ((u : ℂ) * SquarefreeVaughanLogSource.length u N) *
      (∑ k ∈ Finset.Icc 1 (N+1-K),
        a (k-1) * a (N+1-k) / ((N+2-k : ℕ) : ℂ))

/-- At the original endpoint this is definitionally the checked evaluator. -/
theorem evaluation_original (a : ℕ → ℂ) (u : ℝ) (N : ℕ) :
    evaluation a u N (13*N/32) = harmonicEvaluation a u N := rfl

/-- Raising the cutoff removes two central endpoints and exactly one
successor-prefix endpoint. The complex phase is never replaced. -/
theorem evaluation_sub_succ (a : ℕ → ℂ) (u : ℝ) {N K : ℕ}
    (hK : 2*(K+1) ≤ N) :
    evaluation a u N K - evaluation a u N (K+1) =
      ((N+1 : ℕ) : ℂ) / ((K+1 : ℕ) : ℂ) * a K *
        (a (N-K-1) / ((N-K : ℕ) : ℂ) -
          a (N-K) / ((u : ℂ) * SquarefreeVaughanLogSource.length u N)) := by
  have hc : centralOrders (N+1) K =
      insert (K+1) (insert (N-K) (centralOrders (N+1) (K+1))) := by
    ext k
    simp only [centralOrders, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  have hn : N-K ∉ centralOrders (N+1) (K+1) := by
    simp only [centralOrders, Finset.mem_filter, Finset.mem_range]
    omega
  have hk : K+1 ∉ insert (N-K) (centralOrders (N+1) (K+1)) := by
    simp only [Finset.mem_insert, centralOrders, Finset.mem_filter, Finset.mem_range]
    omega
  have hp : Finset.Icc 1 (N+1-K) =
      insert (N+1-K) (Finset.Icc 1 (N+1-(K+1))) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hpn : N+1-K ∉ Finset.Icc 1 (N+1-(K+1)) := by
    simp only [Finset.mem_Icc]
    omega
  have hi : N+1-(K+1)=N-K ∧ N+2-(K+1)=N+1-K ∧
      N+1-(N-K)=K+1 ∧ N+2-(N+1-K)=K+1 ∧
      N-(N+1-K)=K-1 ∧ N+1-(N+1-K)=K := by omega
  unfold evaluation
  rw [hc, Finset.sum_insert hk, Finset.sum_insert hn, hp, Finset.sum_insert hpn]
  simp only [Nat.add_sub_cancel, hi.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.2,
    show N+1-K-1=N-K by omega,
    show N-(N-K)=K by omega, show N-(K+1)=N-K-1 by omega]
  have hden1 : ((K+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero K)
  have hden2 : ((N-K : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show N-K≠0 by omega)
  have hsum : ((N+1 : ℕ) : ℂ) = ((N-K : ℕ) : ℂ) + ((K+1 : ℕ) : ℂ) := by
    exact_mod_cast (show N+1=N-K+(K+1) by omega)
  rw [hsum]
  field_simp [hden1, hden2]
  ring

/-- The thin transition is exactly a consecutive sum of centered moments,
at the same order and height. No replacement-mask commutator appears. -/
theorem evaluation_sub_eq_sum (a : ℕ → ℂ) (u : ℝ) {N K₀ K₁ : ℕ}
    (h01 : K₀ ≤ K₁) (h1 : 2*K₁ ≤ N) :
    evaluation a u N K₀ - evaluation a u N K₁ =
      ∑ k ∈ Finset.Ico K₀ K₁,
        ((N+1 : ℕ) : ℂ) / ((k+1 : ℕ) : ℂ) * a k *
          (a (N-k-1) / ((N-k : ℕ) : ℂ) -
            a (N-k) / ((u : ℂ) * SquarefreeVaughanLogSource.length u N)) := by
  have hs := Finset.sum_Ico_sub (f := fun k => -evaluation a u N k) h01
  simp only [neg_sub_neg] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro k hk
  exact evaluation_sub_succ a u (by have hh := Finset.mem_Ico.mp hk; omega)

/-- The exact constant-array source for a limiting factorial fraction. -/
def source (u theta : ℝ) : ℝ :=
  1 + log ((1-theta)/theta) - log (1/theta)/(-2*u*log u)

private theorem reciprocal_interval (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.Icc (a+1) b, (1 : ℝ)/k) =
      (harmonic b : ℝ) - (harmonic a : ℝ) := by
  have hsub : Finset.Icc 1 a ⊆ Finset.Icc 1 b := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  have hs : Finset.Icc 1 b \ Finset.Icc 1 a = Finset.Icc (a+1) b := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hh := Finset.sum_sdiff (f := fun k : ℕ => (1 : ℝ)/k) hsub
  rw [hs] at hh
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simpa only [one_div] using (eq_sub_iff_add_eq.mpr hh)

/-- Both central endpoints remain genuine integer harmonic endpoints. -/
theorem central_reciprocal {N K : ℕ} (hK : 2*K ≤ N) :
    (∑ k ∈ centralOrders (N+1) K, (1 : ℝ)/((N+1-k : ℕ) : ℝ)) =
      (harmonic (N-K) : ℝ) - (harmonic K : ℝ) := by
  have he : centralOrders (N+1) K = Finset.Icc (K+1) (N-K) := by
    ext k
    simp only [centralOrders, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [he]
  have href : (∑ k ∈ Finset.Icc (K+1) (N-K),
      (1 : ℝ)/((N+1-k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc (K+1) (N-K), (1 : ℝ)/k := by
    apply Finset.sum_bij (fun k _ => N+1-k)
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha b hb h
      rw [Finset.mem_Icc] at ha hb
      omega
    · intro k hk
      refine ⟨N+1-k, ?_, ?_⟩
      · rw [Finset.mem_Icc] at hk ⊢
        omega
      · rw [Finset.mem_Icc] at hk
        omega
    · intro k _; rfl
  rw [href, reciprocal_interval _ _ (by omega)]

/-- The successor prefix likewise keeps the exact cutoff and `N+1`. -/
theorem prefix_reciprocal {N K : ℕ} (hK : K ≤ N+1) :
    (∑ k ∈ Finset.Icc 1 (N+1-K), (1 : ℝ)/((N+2-k : ℕ) : ℝ)) =
      (harmonic (N+1) : ℝ) - (harmonic K : ℝ) := by
  have href : (∑ k ∈ Finset.Icc 1 (N+1-K),
      (1 : ℝ)/((N+2-k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc (K+1) (N+1), (1 : ℝ)/k := by
    apply Finset.sum_bij (fun k _ => N+2-k)
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha b hb h
      rw [Finset.mem_Icc] at ha hb
      omega
    · intro k hk
      refine ⟨N+2-k, ?_, ?_⟩
      · rw [Finset.mem_Icc] at hk ⊢
        omega
      · rw [Finset.mem_Icc] at hk
        omega
    · intro k _; rfl
  rw [href, reciprocal_interval _ _ hK]

/-- Exact finite constant-array evaluation, before any limit or rounding. -/
theorem evaluation_const (c : ℂ) (u : ℝ) {N K : ℕ}
    (hN : 0 < N) (hK : 2*K ≤ N) :
    evaluation (fun _ => c) u N K = c^2 *
      ((1 + ((harmonic (N-K) : ℝ) - (harmonic K : ℝ)) -
        ((N+1 : ℕ) : ℝ)/(u*SquarefreeVaughanLogSource.length u N)*
          ((harmonic (N+1) : ℝ) - (harmonic K : ℝ)) : ℝ) : ℂ) := by
  have hs (S : Finset ℕ) (d : ℕ → ℕ) :
      (∑ k ∈ S, c*c/(d k : ℂ)) = c^2 * ∑ k ∈ S, (1 : ℂ)/(d k : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hc := congrArg (fun x : ℝ => (x : ℂ)) (central_reciprocal hK)
  have hp := congrArg (fun x : ℝ => (x : ℂ)) (prefix_reciprocal (by omega : K ≤ N+1))
  push_cast at hc hp
  unfold evaluation
  dsimp only
  rw [hs, hs, hc, hp]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp [hNc]

private theorem nat_atTop_of_ratio (K : ℕ → ℕ) {theta : ℝ} (ht : 0 < theta)
    (hr : Tendsto (fun N : ℕ => (K N : ℝ)/(N+1)) atTop (𝓝 theta)) :
    Tendsto K atTop atTop := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hh := hr.pos_mul_atTop ht hn
  have hc : Tendsto (fun N : ℕ => (K N : ℝ)) atTop atTop := by
    convert hh using 1
    funext N
    exact (div_mul_cancel₀ _ (by positivity : (N : ℝ)+1 ≠ 0)).symm
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [hc.eventually_ge_atTop (b : ℝ)] with N hN
  exact_mod_cast hN

/-- For every moving lower-half cutoff, its constant source is the exact
logarithmic formula. The floor and damping in the physical length remain. -/
theorem evaluation_const_tendsto (c : ℂ) (K : ℕ → ℕ) {u theta : ℝ}
    (hu : 0 < u) (huq : u ≤ 3/5) (ht : 0 < theta) (ht1 : theta < 1/2)
    (hK : ∀ᶠ N : ℕ in atTop, 2*K N ≤ N)
    (hr : Tendsto (fun N : ℕ => (K N : ℝ)/(N+1)) atTop (𝓝 theta)) :
    Tendsto (fun N : ℕ => evaluation (fun _ => c) u N (K N))
      atTop (𝓝 (c^2 * (source u theta : ℂ))) := by
  have hKt := nat_atTop_of_ratio K ht hr
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hbr : Tendsto (fun N : ℕ => ((N-K N : ℕ) : ℝ)/(N+1))
      atTop (𝓝 (1-theta)) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hn.const_div_atTop 1)).sub hr
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [hK] with N hN
    rw [Nat.cast_sub (by omega : K N ≤ N)]
    field_simp
    ring
  have hBt := nat_atTop_of_ratio (fun N => N-K N) (by linarith : 0 < 1-theta) hbr
  have hcb : Tendsto (fun N : ℕ => ((N-K N : ℕ) : ℝ)/(K N : ℝ))
      atTop (𝓝 ((1-theta)/theta)) := by
    have hh := hbr.div hr ht.ne'
    apply hh.congr
    intro N
    exact div_div_div_cancel_right₀ (by positivity : (N : ℝ)+1 ≠ 0) _ _
  have hpb : Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℝ)/(K N : ℝ))
      atTop (𝓝 (1/theta)) := by
    simpa only [one_div, inv_div, Nat.cast_add, Nat.cast_one] using hr.inv₀ ht.ne'
  have htone : 0 < 1-theta := by linarith only [ht1]
  have hc := HarmonicIntervalLimit.tendsto_harmonic_difference
    (fun N => N-K N) K hBt hKt (div_pos htone ht).ne' hcb
  have hp := HarmonicIntervalLimit.tendsto_harmonic_difference
    (fun N => N+1) K (tendsto_add_atTop_nat 1) hKt (by positivity : 1/theta ≠ 0) hpb
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add hc).sub
    ((tendsto_head_length_factor hu huq).mul hp)
  have hhh := (Complex.continuous_ofReal.continuousAt.tendsto.comp hh).const_mul (c^2)
  have htarget : Tendsto (fun N : ℕ => evaluation (fun _ => c) u N (K N))
      atTop (𝓝 (c^2 * ((1 + log ((1-theta)/theta) -
        (1/(-2*u*log u))*log (1/theta) : ℝ) : ℂ))) := hhh.congr' (by
    filter_upwards [hK, eventually_ge_atTop 1] with N hKN hN
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (evaluation_const c u (by omega) hKN).symm)
  convert htarget using 1
  congr 2
  unfold source
  ring

private theorem product_difference {a b c d : ℂ} {C : ℝ}
    (hb : ‖b‖≤C) (hc : ‖c‖≤C) :
    ‖a*b-c*d‖≤C*(‖a-c‖+‖b-d‖) := by
  have he : a*b-c*d=(a-c)*b+c*(b-d) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have h1 := mul_le_mul_of_nonneg_left hb (norm_nonneg (a-c))
  have h2 := mul_le_mul_of_nonneg_right hc (norm_nonneg (b-d))
  nlinarith only [h1,h2]

private theorem marginal_sums (e : ℕ → ℝ) (he : ∀ j,0≤e j)
    (N t : ℕ) (ht : t≤N+1) (S : Finset ℕ) (hS : ∀ k∈S,0<k ∧ k≤t) :
    (∑ k∈S,e (k-1))≤∑ j∈Finset.range (N+2),e j ∧
    (∑ k∈S,e (t-k))≤∑ j∈Finset.range (N+2),e j := by
  have hl : S.image (fun k => k-1)⊆Finset.range (N+2) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have := hS k hk
    exact Finset.mem_range.mpr (by omega)
  have hr : S.image (fun k => t-k)⊆Finset.range (N+2) := by
    intro j hj
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (by omega)
  have hil : Set.InjOn (fun k : ℕ => k-1) S := by
    intro a ha b hb h
    have := hS a ha
    have := hS b hb
    dsimp only at h
    omega
  have hir : Set.InjOn (fun k : ℕ => t-k) S := by
    intro a ha b hb h
    have := hS a ha
    have := hS b hb
    dsimp only at h
    omega
  constructor
  · rw [←Finset.sum_image hil]
    exact Finset.sum_le_sum_of_subset_of_nonneg hl (fun j _ _ => he j)
  · rw [←Finset.sum_image hir]
    exact Finset.sum_le_sum_of_subset_of_nonneg hr (fun j _ _ => he j)

private theorem harmonic_difference (a b : ℕ → ℂ) {C : ℝ} (hC : 0≤C)
    (ha : ∀ k,‖a k‖≤C) (hb : ∀ k,‖b k‖≤C)
    {N : ℕ} (hN : 0<N) (t : ℕ) (ht : t≤N+1) (S : Finset ℕ)
    (hS : ∀ k∈S,0<k ∧ k≤t ∧ N≤4*(t+1-k)) :
    ‖(∑ k∈S,a (k-1)*a (t-k)/((t+1-k : ℕ) : ℂ))-
      ∑ k∈S,b (k-1)*b (t-k)/((t+1-k : ℕ) : ℂ)‖≤
      (8*C/(N : ℝ))*∑ j∈Finset.range (N+2),‖a j-b j‖ := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hp k (hk : k∈S) :
      ‖(a (k-1)*a (t-k)-b (k-1)*b (t-k))/((t+1-k : ℕ) : ℂ)‖≤
        (4*C/(N : ℝ))*(‖a (k-1)-b (k-1)‖+‖a (t-k)-b (t-k)‖) := by
    have hs := hS k hk
    have hden : (0 : ℝ)<((t+1-k : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0<t+1-k)
    have hcomp : (N : ℝ)≤4*((t+1-k : ℕ) : ℝ) := by exact_mod_cast hs.2.2
    have hi : (1 : ℝ)/((t+1-k : ℕ) : ℝ)≤4/(N : ℝ) :=
      (div_le_div_iff₀ hden hNr).mpr (by linarith only [hcomp])
    rw [norm_div,Complex.norm_natCast,div_eq_mul_inv]
    exact (mul_le_mul (product_difference (ha (t-k)) (hb (k-1)))
      (by simpa only [one_div] using hi) (by positivity) (by positivity)).trans_eq (by ring)
  have hm := marginal_sums (fun j => ‖a j-b j‖) (fun j => norm_nonneg _) N t ht S
    (fun k hk => ⟨(hS k hk).1,(hS k hk).2.1⟩)
  rw [←Finset.sum_sub_distrib]
  simp only [←sub_div]
  calc
    _ ≤ ∑ k∈S,(4*C/(N : ℝ))*(‖a (k-1)-b (k-1)‖+‖a (t-k)-b (t-k)‖) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (4*C/(N : ℝ))*((∑ k∈S,‖a (k-1)-b (k-1)‖)+∑ k∈S,‖a (t-k)-b (t-k)‖) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (add_le_add hm.1 hm.2)
      (by positivity : 0≤4*C/(N : ℝ))).trans_eq (by ring)

private theorem trace_difference (a b : ℕ → ℂ) {C : ℝ} (hC : 0≤C)
    (ha : ∀ k,‖a k‖≤C) (hb : ∀ k,‖b k‖≤C) {N : ℕ} (hN : 0<N) :
    ‖(∑ k∈Finset.range N,a k*a (N-1-k))/(N : ℂ)-
      (∑ k∈Finset.range N,b k*b (N-1-k))/(N : ℂ)‖≤
      (2*C/(N : ℝ))*∑ k∈Finset.range (N+2),‖a k-b k‖ := by
  have hP k : ‖a k*a (N-1-k)-b k*b (N-1-k)‖≤
      C*(‖a k-b k‖+‖a (N-1-k)-b (N-1-k)‖) :=
    product_difference (ha (N-1-k)) (hb k)
  have hr : (∑ k∈Finset.range N,‖a (N-1-k)-b (N-1-k)‖)=
      ∑ k∈Finset.range N,‖a k-b k‖ := by
    simpa only using Finset.sum_range_reflect (fun k => ‖a k-b k‖) N
  have he : (∑ k∈Finset.range N,‖a k-b k‖)≤
      ∑ k∈Finset.range (N+2),‖a k-b k‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun k _ _ => norm_nonneg _)
  rw [←sub_div,←Finset.sum_sub_distrib,norm_div,Complex.norm_natCast]
  calc
    _ ≤ (∑ k∈Finset.range N,C*(‖a k-b k‖+‖a (N-1-k)-b (N-1-k)‖))/(N : ℝ) :=
      div_le_div_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => hP k)))
        (Nat.cast_nonneg _)
    _ = (2*C/(N : ℝ))*∑ k∈Finset.range N,‖a k-b k‖ := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,hr]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

private theorem length_factor_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) :
    ‖((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)‖≤3/2 := by
  have hu0 : 0<u := by linarith only [hu]
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN hu0 hU
  have hprod := mul_nonneg (show 0≤u-1/2 by linarith only [hu]) hL.le
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  rw [norm_div,norm_mul,Complex.norm_natCast,Complex.norm_real,
    Real.norm_of_nonneg hu0.le,Complex.norm_real,Real.norm_of_nonneg hL.le]
  apply (div_le_iff₀ (mul_pos hu0 hL)).mpr
  push_cast
  nlinarith only [hlo,hprod,hNr]

/-- The existing joint array-difference price remains valid for every
cutoff in the middle quarter, including both proposed exact endpoints.
This is a completed-array estimate, not a literal-mask completion. -/
theorem norm_evaluation_sub_le (a b : ℕ → ℂ) {C u : ℝ} (hC : 0≤C)
    (ha : ∀ k,‖a k‖≤C) (hb : ∀ k,‖b k‖≤C) (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) {K : ℕ} (hlo : N≤4*K) (hhi : 2*K≤N) :
    ‖evaluation a u N K-evaluation b u N K‖≤
      (22*C/(N : ℝ))*∑ k∈Finset.range (N+2),‖a k-b k‖ := by
  have hN0 : 0<N := by omega
  let E : ℝ := ∑ k∈Finset.range (N+2),‖a k-b k‖
  have hE : 0≤E := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have ht := trace_difference a b hC ha hb hN0
  have hc := harmonic_difference a b hC ha hb hN0 N (by omega)
    (centralOrders (N+1) (K)) (by
      intro k hk
      simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
      omega)
  have hp := harmonic_difference a b hC ha hb hN0 (N+1) (by omega)
    (Finset.Icc 1 (N+1-K)) (by
      intro k hk
      rw [Finset.mem_Icc] at hk
      omega)
  let F : ℂ := ((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)
  let T (v : ℕ → ℂ) : ℂ := (∑ k∈Finset.range N,v k*v (N-1-k))/(N : ℂ)
  let B (v : ℕ → ℂ) : ℂ := ∑ k∈centralOrders (N+1) (K),
    v (k-1)*v (N-k)/((N+1-k : ℕ) : ℂ)
  let P (v : ℕ → ℂ) : ℂ := ∑ k∈Finset.Icc 1 (N+1-K),
    v (k-1)*v (N+1-k)/((N+2-k : ℕ) : ℂ)
  have he : evaluation a u N K-evaluation b u N K=
      (T a-T b)+(B a-B b)-F*(P a-P b) := by
    unfold evaluation
    dsimp only [T,B,P,F]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hf : ‖F*(P a-P b)‖≤(3/2 : ℝ)*((8*C/(N : ℝ))*E) := by
    rw [norm_mul]
    exact mul_le_mul (length_factor_le hu hU hN) hp (norm_nonneg _) (by norm_num)
  exact (add_le_add ((norm_add_le _ _).trans (add_le_add ht hc)) hf).trans_eq (by dsimp only [E]; ring)

open ZetaRieszJoinedSourceError

/-- The selected-source comparison holds on the whole proposed cutoff
band, retaining every genuine ordinary-prime source-error order. -/
theorem norm_evaluation_sub_selected_le (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    {N : ℕ} (hN : 65536≤N) {K : ℕ} (hlo : N≤4*K) (hhi : 2*K≤N) :
    ‖evaluation (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N K-
      evaluation (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ))
        (3/2-rho.1.re) N K‖≤
      22*((analyticZetaZeroMultiplicity rho : ℝ)+sourceErrorMass rho)*
        sourceErrorMass rho/(N : ℝ) := by
  let m := analyticZetaZeroMultiplicity rho
  let D := sourceErrorMass rho
  have hD : 0≤D := sourceErrorMass_nonneg rho
  have hC : 0≤(m : ℝ)+D := add_nonneg (Nat.cast_nonneg _) hD
  have ho k : ‖ordinaryArray (3/2-rho.1.re) rho.1.im k‖≤(m : ℝ)+D := by
    have he := sum_source_error_le rho hrho hexposed hU {k}
    simp only [Finset.sum_singleton] at he
    have hi : ordinaryArray (3/2-rho.1.re) rho.1.im k=
        (ordinaryArray (3/2-rho.1.re) rho.1.im k+(m : ℂ))-(m : ℂ) := by ring
    rw [hi]
    apply ((norm_sub_le _ _).trans (add_le_add he le_rfl)).trans_eq
    rw [Complex.norm_natCast]
    ring
  have hm : ∀ _ : ℕ,‖(-(m : ℂ))‖≤(m : ℝ)+D := by
    intro _
    rw [norm_neg,Complex.norm_natCast]
    linarith only [hD]
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  exact (norm_evaluation_sub_le _ _ hC ho hm hu hU hN hlo hhi).trans
    ((mul_le_mul_of_nonneg_left (by
      simpa only [sub_neg_eq_add] using sum_source_error_le rho hrho hexposed hU
        (Finset.range (N+2))) (by positivity)).trans_eq (by dsimp only [m,D]; ring))

/-- Proper prime powers are paid on the same completed cutoff family,
without completing a new physical-mask sum. -/
theorem norm_ordinary_sub_mangoldt_evaluation_le {C u : ℝ} (hC : 0 ≤ C)
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (ho : ∀ k, ‖ordinaryArray u y k‖ ≤ C)
    (hm : ∀ k, ‖mangoldtArray u y k‖ ≤ C) {N K : ℕ}
    (hN : 65536 ≤ N) (hlo : N ≤ 4*K) (hhi : 2*K ≤ N) :
    ‖evaluation (ordinaryArray u y) u N K - evaluation (mangoldtArray u y) u N K‖ ≤
      22*C*powerMass/(N : ℝ) := by
  have hp := sum_norm_array_difference_le (show 0 ≤ u by linarith only [hu]) hU y (N+2)
  exact (norm_evaluation_sub_le _ _ hC ho hm hu hU hN hlo hhi).trans
    ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring))

/-- The genuine completed ordinary-prime source has the independently
derived cutoff formula, multiplied by the square of the analytic multiplicity. -/
theorem tendsto_ordinary_source (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (K : ℕ → ℕ) {theta : ℝ} (ht : 0 < theta) (ht1 : theta < 1/2)
    (hK : ∀ᶠ N : ℕ in atTop, N ≤ 4*K N ∧ 2*K N ≤ N)
    (hr : Tendsto (fun N : ℕ => (K N : ℝ)/(N+1)) atTop (𝓝 theta)) :
    Tendsto (fun N : ℕ => evaluation
      (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N (K N))
      atTop (𝓝 (((analyticZetaZeroMultiplicity rho : ℂ)^2)*
        (source (3/2-rho.1.re) theta : ℂ))) := by
  have hu : 0 < 3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have huq : 3/2-rho.1.re ≤ (3/5 : ℝ) :=
    hU.trans (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have hs := evaluation_const_tendsto (-(analyticZetaZeroMultiplicity rho : ℂ))
    K hu huq ht ht1 (hK.mono fun _ h => h.2) hr
  simp only [neg_sq] at hs
  have he : Tendsto (fun N : ℕ => evaluation
      (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N (K N) -
      evaluation (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ))
        (3/2-rho.1.re) N (K N)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (by
      filter_upwards [hK, eventually_ge_atTop 65536] with N hKN hN
      exact norm_evaluation_sub_selected_le rho hrho hexposed hU hN hKN.1 hKN.2)
    exact tendsto_source_error_price rho
  simpa only [sub_add_cancel, zero_add] using he.add hs

/-- The same exact source survives in the full von Mangoldt array. -/
theorem tendsto_mangoldt_source (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (K : ℕ → ℕ) {theta : ℝ} (ht : 0 < theta) (ht1 : theta < 1/2)
    (hK : ∀ᶠ N : ℕ in atTop, N ≤ 4*K N ∧ 2*K N ≤ N)
    (hr : Tendsto (fun N : ℕ => (K N : ℝ)/(N+1)) atTop (𝓝 theta)) :
    Tendsto (fun N : ℕ => evaluation
      (mangoldtArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N (K N))
      atTop (𝓝 (((analyticZetaZeroMultiplicity rho : ℂ)^2)*
        (source (3/2-rho.1.re) theta : ℂ))) := by
  obtain ⟨C,hC,ho,hm,_⟩ := exists_exposed_quadratic_power_payment rho hrho hexposed hU
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have he : Tendsto (fun N : ℕ => evaluation
      (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N (K N) -
      evaluation (mangoldtArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N (K N))
        atTop (𝓝 0) := by
    apply squeeze_zero_norm' (by
      filter_upwards [hK, eventually_ge_atTop 65536] with N hKN hN
      exact norm_ordinary_sub_mangoldt_evaluation_le (by linarith only [hC])
        hu hU rho.1.im ho hm hN hKN.1 hKN.2)
    simpa only [mul_zero, div_eq_mul_inv, one_div, one_mul] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (22*C*powerMass)
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_ordinary_source rho hrho hexposed hU K ht ht1 hK hr).sub he

/-- The proposed recurrence defect is retained as a complex centered
moment, not replaced by a difference of its two absolute values. -/
def centeredDefect (a : ℕ → ℂ) (u : ℝ) (N j : ℕ) : ℂ :=
  a j / ((j+1 : ℕ) : ℂ) -
    a (j+1) / ((u : ℂ)*SquarefreeVaughanLogSource.length u N)

/-- Summing the factorial allocations first does not center this moment
at the exposed source's saddle. Its selected limit is generally nonzero. -/
theorem tendsto_centered_defect (a : ℕ → ℂ) (c : ℂ)
    (ha : Tendsto a atTop (𝓝 c)) (K : ℕ → ℕ) {u theta : ℝ}
    (hu : 0 < u) (huq : u ≤ 3/5) (ht1 : theta < 1/2)
    (hK : ∀ᶠ N : ℕ in atTop, K N ≤ N)
    (hr : Tendsto (fun N : ℕ => (K N : ℝ)/(N+1)) atTop (𝓝 theta)) :
    Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℂ) *
      centeredDefect a u N (N-K N-1)) atTop
        (𝓝 (c*((1-theta : ℝ)⁻¹ - (1/(-2*u*log u) : ℝ) : ℂ))) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hb : Tendsto (fun N : ℕ => ((N-K N : ℕ) : ℝ)/(N+1))
      atTop (𝓝 (1-theta)) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hn.const_div_atTop 1)).sub hr
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [hK] with N hN
    rw [Nat.cast_sub hN]
    field_simp
    ring
  have hpos : 0 < 1-theta := by linarith only [ht1]
  have hBn := nat_atTop_of_ratio (fun N => N-K N) hpos hb
  have hJ := (tendsto_sub_atTop_nat 1).comp hBn
  have hbC := Complex.continuous_ofReal.continuousAt.tendsto.comp hb
  have hfC := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_head_length_factor hu huq)
  have hh := ((ha.comp hJ).div hbC (by exact_mod_cast hpos.ne')).sub
    ((ha.comp hBn).mul hfC)
  have htarget : Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℂ) *
      centeredDefect a u N (N-K N-1)) atTop
        (𝓝 (c/(1-theta : ℝ) - c*(1/(-2*u*log u) : ℝ))) := hh.congr' (by
    filter_upwards [hBn.eventually_ge_atTop 1] with N hN
    have hi : N-K N-1+1=N-K N := by omega
    dsimp only [Function.comp_def, centeredDefect]
    rw [hi]
    push_cast
    simp only [Pi.div_apply, div_div_eq_mul_div]
    ring)
  convert htarget using 1
  push_cast
  ring

end RiemannGaussian.ZetaRieszFactorialCutoff
