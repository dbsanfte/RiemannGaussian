/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMovingPrimeIntervals
import RiemannGaussian.ZetaRieszPrimeFourier

/-!
# Exact composite moment cancellation improves the signed prime budget

Every squarefree composite cofactor annihilates both constant and logarithmic
divisor profiles. Remove their contribution before measuring the common prime
profile's energy. The optimum is an explicit quadratic projection, retaining
all signed prime cross terms. No arithmetic carrier or finite mask is changed.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCenteredPrimeEnergy
open Real ZetaRieszMovingPrimeIntervals ZetaRieszOwnerMaximal
open ZetaRieszPrimeTailEnergy ZetaRieszRetainedFactorial
open ZetaRieszWeightedPrimeTail ZetaRieszJointAllocation

/-- The common logarithmic increment annihilated by composite divisor sums. -/
def logStep (k : ℕ) : ℝ := log (k+1 : ℕ)-log k

/-- Population-truncated difference energy before the free moment projection. -/
def rawEnergy (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*(f k-f (k+1))^2

/-- Squared length of the exact logarithmic null direction. -/
def logEnergy (X : ℕ) : ℝ := ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*logStep k^2

/-- Signed correlation with the logarithmic null direction. -/
def logCross (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*(f k-f (k+1))*logStep k

/-- The energy after subtracting an arbitrary exact null component. -/
def shiftedEnergy (X : ℕ) (f : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*(f k-f (k+1)-a*logStep k)^2

/-- Optimal centering is performed on the full signed block profile. -/
def centeredEnergy (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  shiftedEnergy X f (logCross X f/logEnergy X)

private theorem logEnergy_nonneg (X : ℕ) : 0 ≤ logEnergy X :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _))

/-- The centered profile is still a nonnegative squared energy. -/
theorem centeredEnergy_nonneg (X : ℕ) (f : ℕ → ℝ) : 0 ≤ centeredEnergy X f := by
  unfold centeredEnergy shiftedEnergy
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _))

private theorem shiftedEnergy_expand (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    shiftedEnergy X f a = rawEnergy X f-2*a*logCross X f+a^2*logEnergy X := by
  simp only [shiftedEnergy,rawEnergy,logCross,logEnergy,Finset.mul_sum,
    ← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem logCross_sq_le (X : ℕ) (f : ℕ → ℝ) :
    logCross X f^2 ≤ rawEnergy X f*logEnergy X := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.Ico 1 X)
    (fun k _ => mul_nonneg (Nat.cast_nonneg k) (sq_nonneg (f k-f (k+1))))
    (fun k _ => mul_nonneg (Nat.cast_nonneg k) (sq_nonneg (logStep k)))
  intro k _
  ring_nf
  rfl

/-- The exact saved cost is the squared signed correlation divided by the
logarithmic energy. This is an equality, not a fitted numerical allowance. -/
theorem centeredEnergy_eq (X : ℕ) (f : ℕ → ℝ) :
    centeredEnergy X f = rawEnergy X f-(logCross X f)^2/logEnergy X := by
  rw [centeredEnergy,shiftedEnergy_expand]
  by_cases h : logEnergy X=0
  · simp only [h,div_zero,mul_zero,zero_mul,sub_zero,zero_pow (by decide : 2 ≠ 0),add_zero]
  · field_simp
    ring

/-- Removing the null moment never increases a signed profile's cost. -/
theorem centeredEnergy_le_raw (X : ℕ) (f : ℕ → ℝ) :
    centeredEnergy X f ≤ rawEnergy X f := by
  rw [centeredEnergy_eq]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (logEnergy_nonneg X))

/-- The chosen projection minimizes energy among every affine-log correction. -/
theorem centeredEnergy_le_shifted (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    centeredEnergy X f ≤ shiftedEnergy X f a := by
  rw [centeredEnergy_eq,shiftedEnergy_expand]
  by_cases h : logEnergy X=0
  · have hc : logCross X f=0 := by
      have hs := logCross_sq_le X f
      rw [h,mul_zero] at hs
      nlinarith [sq_nonneg (logCross X f)]
    simp [h,hc]
  · have hp : 0 < logEnergy X := lt_of_le_of_ne (logEnergy_nonneg X) (Ne.symm h)
    apply (mul_le_mul_iff_of_pos_right hp).mp
    have he : (rawEnergy X f-(logCross X f)^2/logEnergy X)*logEnergy X =
        rawEnergy X f*logEnergy X-(logCross X f)^2 := by field_simp
    rw [he]
    nlinarith [sq_nonneg (a*logEnergy X-logCross X f)]

/-- The affine-log correction, clipped only beyond all population divisors. -/
def centeredProfile (X : ℕ) (f : ℕ → ℝ) (a : ℝ) (d : ℕ) : ℝ :=
  if d ≤ X then f d+a*log d-(f X+a*log X) else 0

/-- Actual squarefree composite divisors annihilate the whole affine-log
correction exactly, before any norm, count sum or prime projection. -/
theorem divisor_centering {n X : ℕ} (hn : Squarefree n) (hp : ¬n.Prime)
    (h1 : n ≠ 1) (hX : n ≤ X) (f : ℕ → ℝ) (a : ℝ) :
    (∑ d ∈ n.divisors, (μ d : ℝ)*centeredProfile X f a d) =
      ∑ d ∈ n.divisors, (μ d : ℝ)*f d := by
  have hm : (∑ d ∈ n.divisors, (μ d : ℝ))=0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero h1
  have hl : (∑ d ∈ n.divisors, (μ d : ℝ)*log d)=0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_log_eq_zero hn hp
  have he d (hd : d ∈ n.divisors) : centeredProfile X f a d =
      f d+a*log d-(f X+a*log X) := by
    apply if_pos
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) (Nat.dvd_of_mem_divisors hd)).trans hX
  simp_rw [Finset.sum_congr rfl (fun d hd => congrArg (fun x : ℝ => (μ d : ℝ)*x) (he d hd))]
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hx : (∑ d ∈ n.divisors, (μ d : ℝ)*(a*log d)) = a*(∑ d ∈ n.divisors, (μ d : ℝ)*log d) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [hx,hl,mul_zero,← Finset.sum_mul,hm,zero_mul,add_zero,sub_zero]

/-- Exact conversion of the finite arithmetic prefix to actual divisors. -/
theorem prefix_eq_divisors {n X : ℕ} (hn : 0 < n) (hX : n ≤ X) (g : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, g d*(if d ∣ n then (μ d : ℝ) else 0)) =
      ∑ d ∈ n.divisors, (μ d : ℝ)*g d := by
  have he : (Finset.Icc 1 X).filter (fun d => d ∣ n)=n.divisors := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,hd⟩
      exact ⟨hd,hn.ne'⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,(Nat.le_of_dvd hn hd).trans hX⟩,hd⟩
  simp_rw [mul_ite,mul_zero]
  rw [← Finset.sum_filter,he]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private theorem centeredProfile_energy (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*
      (centeredProfile X f a k-centeredProfile X f a (k+1))^2) = shiftedEnergy X f a := by
  have he : ∀ k ∈ Finset.Ico 1 X,
      centeredProfile X f a k-centeredProfile X f a (k+1) = f k-f (k+1)-a*logStep k := by
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    simp only [centeredProfile,if_pos (by omega : k ≤ X),if_pos (by omega : k+1 ≤ X),logStep]
    ring
  have hx : centeredProfile X f a X=0 := by simp [centeredProfile]
  have hx' : centeredProfile X f a (X+1)=0 := by simp [centeredProfile]
  unfold shiftedEnergy
  rw [← Finset.sum_congr rfl (fun (k : ℕ) hk => congrArg (fun z : ℝ => (k : ℝ)*z^2) (he k hk))]
  symm
  apply Finset.sum_subset (by intro k hk; have := Finset.mem_Ico.mp hk; exact Finset.mem_Icc.mpr ⟨this.1,this.2.le⟩)
  intro k hk hk'
  have hkX : k=X := by simp only [Finset.mem_Icc,Finset.mem_Ico] at hk hk'; omega
  rw [hkX,hx,hx']
  simp

/-- One unconditional arithmetic constant controls every composite profile
after optimal centering. No endpoint at exp(L) or generic density error is paid. -/
theorem exists_centered_divisor_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S : Finset ℕ) (f : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n ∧ ¬n.Prime) →
      (∑ n ∈ S, (∑ d ∈ n.divisors, (μ d : ℝ)*f d)^2) ≤ E*X*centeredEnergy X f := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_divisor_profile_mean
  refine ⟨E,hE,fun X S f hS hSF => ?_⟩
  let a := logCross X f/logEnergy X
  have hb := hmean X X S (centeredProfile X f a) hS (fun n hn => (hSF n hn).1)
    (by simp [centeredProfile])
  have he n (hn : n ∈ S) :
      (∑ d ∈ Finset.Icc 1 X, centeredProfile X f a d*(if d ∣ n then (μ d : ℝ) else 0)) =
        ∑ d ∈ n.divisors, (μ d : ℝ)*f d := by
    have hx := Finset.mem_Ioc.mp (hS hn)
    rw [prefix_eq_divisors (by omega : 0 < n) hx.2]
    exact divisor_centering (hSF n hn).1 (hSF n hn).2 (by omega) hx.2 f a
  rw [Finset.sum_congr rfl (fun n hn => congrArg (fun x : ℝ => x^2) (he n hn)),
    centeredProfile_energy] at hb
  exact hb

/-- Exact block response over all actual cofactor divisors. The cofactor
bound, rather than the moving physical cutoff, determines the finite support. -/
theorem component_response_divisors (P : ℕ → Finset ℕ) (I : Finset ℕ)
    (c : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    componentResponse P I c L n =
      ∑ d ∈ n.divisors, (μ d : ℝ)*blockProfile P I c L d := by
  simp only [componentResponse,VaughanLogAverage.riesz,← Finset.sum_sub_distrib,
    Finset.mul_sum,blockProfile,profile]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Both phase components are centered as complete signed prime blocks. -/
def centeredBlockEnergy (P : ℕ → Finset ℕ) (I : Finset ℕ) (G : ℝ → ℝ)
    (y L : ℝ) (X : ℕ) : ℝ :=
  centeredEnergy X (blockProfile P I (fun p => G (log p)*cos (y*log p)/(p : ℝ)) L)+
    centeredEnergy X (blockProfile P I (fun p => G (log p)*sin (y*log p)/(p : ℝ)) L)

private theorem centeredBlockEnergy_nonneg (P : ℕ → Finset ℕ) (I : Finset ℕ)
    (G : ℝ → ℝ) (y L : ℝ) (X : ℕ) : 0 ≤ centeredBlockEnergy P I G y L X :=
  add_nonneg (centeredEnergy_nonneg _ _) (centeredEnergy_nonneg _ _)

/-- The centered block inequality keeps arbitrary correlated cofactor phases
and all composite counts. The null moments are discharged arithmetically. -/
theorem exists_centered_block_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (P : ℕ → Finset ℕ) (I S : Finset ℕ)
      (G : ℝ → ℝ) (v : ℕ → ℝ) (y L : ℝ) (X : ℕ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n ∧ ¬n.Prime) →
      (∑ n ∈ S, (blockResponse P I G y L (v n) n)^2) ≤ E*X*centeredBlockEnergy P I G y L X := by
  obtain ⟨E,hE,hmean⟩ := exists_centered_divisor_mean
  refine ⟨E,hE,fun P I S G v y L X hS hSF => ?_⟩
  have hc (c : ℕ → ℝ) : (∑ n ∈ S, (componentResponse P I c L n)^2) ≤
      E*X*centeredEnergy X (blockProfile P I c L) := by
    simp_rw [component_response_divisors]
    exact hmean X S _ hS hSF
  let c := fun p : ℕ => G (log p)*cos (y*log p)/(p : ℝ)
  let s := fun p : ℕ => G (log p)*sin (y*log p)/(p : ℝ)
  have hrot n : (blockResponse P I G y L (v n) n)^2 ≤
      (componentResponse P I c L n)^2+(componentResponse P I s L n)^2 := by
    rw [block_phase]
    change (cos (y*v n)*componentResponse P I c L n-
      sin (y*v n)*componentResponse P I s L n)^2 ≤ _
    have he : (cos (y*v n)*componentResponse P I c L n-
          sin (y*v n)*componentResponse P I s L n)^2+
        (sin (y*v n)*componentResponse P I c L n+
          cos (y*v n)*componentResponse P I s L n)^2 =
        (sin (y*v n)^2+cos (y*v n)^2)*
          ((componentResponse P I c L n)^2+(componentResponse P I s L n)^2) := by ring
    rw [sin_sq_add_cos_sq,one_mul] at he
    nlinarith only [he,sq_nonneg (sin (y*v n)*componentResponse P I c L n+
      cos (y*v n)*componentResponse P I s L n)]
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ S) => hrot n)
  rw [Finset.sum_add_distrib] at hs
  have hc' := hc c
  have hs' := hc s
  change _ ≤ E*X*(centeredEnergy X (blockProfile P I c L)+
    centeredEnergy X (blockProfile P I s L))
  linarith

/-- All binary blocks retain their internal signed prime correlations. -/
def centeredMovingEnergy (P : ℕ → Finset ℕ) (G : ℝ → ℝ) (y L : ℝ) (X b : ℕ) : ℝ :=
  dyadicCost (fun a m => centeredBlockEnergy P (Finset.Ico a (a+m)) G y L X) b 0

private theorem centeredMovingEnergy_nonneg (P : ℕ → Finset ℕ) (G : ℝ → ℝ)
    (y L : ℝ) (X b : ℕ) : 0 ≤ centeredMovingEnergy P G y L X b :=
  dyadicCost_nonneg _ (fun _ _ => centeredBlockEnergy_nonneg _ _ _ _ _ _) _ _

/-- Cofactors may choose different prime intervals. Their moving radial,
ownership and other interval endpoints cost binary depth, not cofactor variation. -/
theorem exists_centered_moving_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (G : ℝ → ℝ) (v : ℕ → ℝ) (y L : ℝ) (X b : ℕ) (lo hi : ℕ → ℕ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n ∧ ¬n.Prime) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∑ n ∈ S, (blockResponse P (Finset.Ico (lo n) (hi n)) G y L (v n) n)^2) ≤
        4*((b+1 : ℕ) : ℝ)*E*X*centeredMovingEnergy P G y L X b := by
  obtain ⟨E,hE,hmean⟩ := exists_centered_block_mean
  refine ⟨E,hE,fun P S G v y L X b lo hi hS hSF hends => ?_⟩
  let f := fun n i => ∑ p ∈ P i, (G (log p)*cos (y*(log p+v n))/(p : ℝ))*
    (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-log p) n)
  have hp n (hn : n ∈ S) := interval_sq_le_dyadicCost (f n) b (lo n) (hi n)
    (hends n hn).1 (hends n hn).2
  have hs := Finset.sum_le_sum hp
  rw [← Finset.mul_sum,dyadicCost_sum] at hs
  have hm := dyadicCost_mono
    (fun a m => ∑ n ∈ S, (∑ i ∈ Finset.Ico a (a+m), f n i)^2)
    (fun a m => E*X*centeredBlockEnergy P (Finset.Ico a (a+m)) G y L X)
    (2^b) b 0 (by omega)
    (fun a m _ => hmean P (Finset.Ico a (a+m)) S G v y L X hS hSF)
  rw [dyadicCost_mul] at hm
  exact hs.trans (by
    have ht := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 4*((b+1 : ℕ) : ℝ))
    simpa only [centeredMovingEnergy,mul_assoc] using ht)

/-- Exact cofactor weights have two signed bounds. No binomial cap replaces
their quadratic energy, and no prime phase is bounded term by term. -/
theorem exists_centered_moving_weighted_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (G : ℝ → ℝ) (v w : ℕ → ℝ) (y L : ℝ) (X b : ℕ) (lo hi : ℕ → ℕ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n ∧ ¬n.Prime) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      let J := ∑ n ∈ S, w n*blockResponse P (Finset.Ico (lo n) (hi n)) G y L (v n) n;
      let K := sqrt ((∑ n ∈ S, (w n)^2)*
        (4*((b+1 : ℕ) : ℝ)*E*X*centeredMovingEnergy P G y L X b));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_centered_moving_mean
  refine ⟨E,hE,fun P S G v w y L X b lo hi hS hSF hends => ?_⟩
  dsimp only
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => blockResponse P (Finset.Ico (lo n) (hi n)) G y L (v n) n)).trans
      (mul_le_mul_of_nonneg_left (hmean P S G v y L X b lo hi hS hSF hends)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_abs,sq_sqrt (mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (by positivity) (centeredMovingEnergy_nonneg P G y L X b)))]
  exact hs

/-- A literal retained carrier's computable budget, using exact coefficients. -/
def retainedCenteredCost (E : ℝ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
    (B : ℕ → ℕ → ℝ) (N X b : ℕ) (y L : ℝ) : ℝ :=
  (1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2),
    sqrt ((∑ n ∈ S, (exp (-log n/2)*B n j/(n : ℝ))^2)*
      (4*((b+1 : ℕ) : ℝ)*E*X*centeredMovingEnergy P (factorialAmplitude j) y L X b)))

/-- The ORIGINAL residual-coefficient carrier has both signed bounds with
cofactor-dependent prime intervals and exact factorial coefficients. Eligibility
and coprimality are required only for the selected primes, not completed rows. -/
theorem exists_literal_centered_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Finset ℕ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (N X b : ℕ) (y L : ℝ) (lo hi : ℕ → ℕ),
      0 < L → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), ∀ p ∈ P i,
        p.Prime ∧ p ∈ A ∧ ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℝ,
        (∀ n ∈ S, ∀ j ≤ N+1,
          0 ≤ B n j ∧ B n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j)) ∧
        (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), ∀ p ∈ P i,
          (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
            ∑ j ∈ Finset.range (N+2), B n j*log p^j) ∧
        let J := (∑ n ∈ S, ∑ i ∈ Finset.Ico (lo n) (hi n), ∑ p ∈ P i,
          residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
        let K := retainedCenteredCost E P S B N X b y L;
        -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_centered_moving_weighted_bounds
  refine ⟨E,hE,fun A P S N X b y L lo hi hL hS hSF hends hprime => ?_⟩
  have hex n (hn : n ∈ S) := exists_retained_coefficients A N (hSF n hn).1 (hSF n hn).2
  choose B hcoef hid using hex
  let B' := fun n j => if hn : n ∈ S then B n hn j else 0
  have hcoef' n (hn : n ∈ S) j (hj : j ≤ N+1) :
      0 ≤ B' n j ∧ B' n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j) := by
    simpa only [B',dif_pos hn] using hcoef n hn j hj
  have hid' n (hn : n ∈ S) i (hi : i ∈ Finset.Ico (lo n) (hi n)) p (hp : p ∈ P i) :
      (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
        ∑ j ∈ Finset.range (N+2), B' n j*log p^j := by
    have hp' := hprime n hn i hi p hp
    simpa only [B',dif_pos hn] using hid n hn p hp'.1 hp'.2.1 hp'.2.2
  refine ⟨B',hcoef',hid',?_⟩
  let w := fun j (n : ℕ) => exp (-log n/2)*B' n j/(n : ℝ)
  have hi' n (hn : n ∈ S) :
      (∑ i ∈ Finset.Ico (lo n) (hi n), ∑ p ∈ P i,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), w j n*
        blockResponse P (Finset.Ico (lo n) (hi n)) (factorialAmplitude j) y L (log n) n) := by
    simp only [Complex.re_sum]
    have he i (hi : i ∈ Finset.Ico (lo n) (hi n)) p (hp : p ∈ P i) :=
      atom_expansion A N L y (hSF n hn).1 (hSF n hn).2
        (hprime n hn i hi p hp).1 (hprime n hn i hi p hp).2.2 (B' n) (hid' n hn i hi p hp)
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (he i hi))]
    simp only [← Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := P _) (t := Finset.range (N+2))]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [w,blockResponse,componentResponse,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    ring
  have htotal :
      (∑ n ∈ S, ∑ i ∈ Finset.Ico (lo n) (hi n), ∑ p ∈ P i,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S, w j n*
        blockResponse P (Finset.Ico (lo n) (hi n)) (factorialAmplitude j) y L (log n) n) := by
    rw [Complex.re_sum,Finset.sum_congr rfl hi',← Finset.mul_sum,Finset.sum_comm]
  have hj j : |∑ n ∈ S, w j n*
      blockResponse P (Finset.Ico (lo n) (hi n)) (factorialAmplitude j) y L (log n) n| ≤
      sqrt ((∑ n ∈ S, (w j n)^2)*
        (4*((b+1 : ℕ) : ℝ)*E*X*centeredMovingEnergy P (factorialAmplitude j) y L X b)) :=
    abs_le.mpr (hbound P S (factorialAmplitude j) (fun n => log n) (w j) y L X b lo hi
      hS (fun n hn => ⟨(hSF n hn).1, by
        intro hp
        have hc := (hSF n hn).2
        simp [hp.primeFactors] at hc⟩) hends)
  have hs := (Finset.abs_sum_le_sum_abs _ (Finset.range (N+2))).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (N+2)) => hj j))
  apply abs_le.mp
  rw [htotal,abs_mul,abs_div,abs_neg,abs_one,
    abs_of_pos (show 0 < L*(N.factorial : ℝ) by positivity)]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

private theorem rawEnergy_le_tail (f : ℕ → ℝ) (X R : ℕ)
    (hf : ∀ d : ℕ, R < d → f d=0) :
    rawEnergy X f ≤ ∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2 := by
  let I := (Finset.Ico 1 X).filter (fun k => k ≤ R)
  have he : rawEnergy X f = ∑ k ∈ I, (k : ℝ)*(f k-f (k+1))^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hk'
    have hRk : R < k := lt_of_not_ge (fun h => hk' (Finset.mem_filter.mpr ⟨hk,h⟩))
    rw [hf k hRk,hf (k+1) (by omega)]
    simp
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (fun k hk => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1).1,(Finset.mem_filter.mp hk).2⟩)
  intro k _ _
  exact mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _)

private theorem blockProfile_tail (P : ℕ → Finset ℕ) (I : Finset ℕ)
    (c : ℕ → ℝ) (L : ℝ) (R : ℕ) (hR : exp L < R+1) (d : ℕ) (hd : R < d) :
    blockProfile P I c L d=0 := by
  have hd1 : 1 ≤ d := by omega
  have he : ((d-1 : ℕ) : ℝ)+1=(d : ℝ) := by exact_mod_cast Nat.sub_add_cancel hd1
  have hcut : exp L < ((d-1 : ℕ) : ℝ)+1 := by
    rw [he]
    exact hR.trans_le (by exact_mod_cast (by omega : R+1 ≤ d))
  apply Finset.sum_eq_zero
  intro i _
  simpa only [Nat.sub_add_cancel hd1] using
    profile_endpoint (P i) c (fun p => log p) L (d-1) hcut (fun p _ => log_natCast_nonneg p)

/-- Exact moment centering and the population cutoff never cost more than
the preceding uncentered prime energy, for every physical cutoff and height. -/
theorem centeredBlockEnergy_le (P : ℕ → Finset ℕ) (I : Finset ℕ) (G : ℝ → ℝ)
    (y L : ℝ) (X R : ℕ) (hR : exp L < R+1) :
    centeredBlockEnergy P I G y L X ≤ blockEnergy P I G y L R := by
  let f := blockProfile P I (fun p => G (log p)*cos (y*log p)/(p : ℝ)) L
  let g := blockProfile P I (fun p => G (log p)*sin (y*log p)/(p : ℝ)) L
  have hc := (centeredEnergy_le_raw X f).trans
    (rawEnergy_le_tail f X R (blockProfile_tail P I _ L R hR))
  have hs := (centeredEnergy_le_raw X g).trans
    (rawEnergy_le_tail g X R (blockProfile_tail P I _ L R hR))
  change centeredEnergy X f+centeredEnergy X g ≤ _
  have he : blockEnergy P I G y L R =
      (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2)+
      (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(g k-g (k+1))^2) := by
    simp only [blockEnergy,f,g,mul_add,Finset.sum_add_distrib]
  rw [he]
  exact add_le_add hc hs

/-- The improvement survives all binary levels and arbitrary moving endpoints. -/
theorem centeredMovingEnergy_le (P : ℕ → Finset ℕ) (G : ℝ → ℝ)
    (y L : ℝ) (X R b : ℕ) (hR : exp L < R+1) :
    centeredMovingEnergy P G y L X b ≤ movingEnergy P G y L R b := by
  exact dyadicCost_mono _ _ (2^b) b 0 (by omega)
    (fun a m _ => centeredBlockEnergy_le P (Finset.Ico a (a+m)) G y L X R hR)

/-- Both literal signed inequalities improve uniformly with the SAME mean
constant and EXACT allocation coefficients; the previous cost is never enlarged. -/
theorem retainedCenteredCost_le (E : ℝ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
    (B : ℕ → ℕ → ℝ) (N X R b : ℕ) (y L : ℝ)
    (hE : 0 ≤ E) (hL : 0 ≤ L) (hR : exp L < R+1) :
    retainedCenteredCost E P S B N X b y L ≤ retainedMovingCost E P S B N X R b y L := by
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1/(L*(N.factorial : ℝ)))
  apply Finset.sum_le_sum
  intro j _
  apply sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact mul_le_mul_of_nonneg_left (centeredMovingEnergy_le P (factorialAmplitude j) y L X R b hR)
    (by positivity)

/-- The moving bound applies to the actual union of disjoint prime cells;
neither eligibility nor coprimality is imposed outside the retained interval. -/
theorem exists_literal_centered_union_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Finset ℕ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (N X b : ℕ) (y L : ℝ) (lo hi : ℕ → ℕ),
      0 < L → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ i < 2^b, ∀ j < 2^b, i ≠ j → Disjoint (P i) (P j)) →
      (∀ n ∈ S, ∀ p ∈ (Finset.Ico (lo n) (hi n)).biUnion P,
        p.Prime ∧ p ∈ A ∧ ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℝ,
        (∀ n ∈ S, ∀ j ≤ N+1,
          0 ≤ B n j ∧ B n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j)) ∧
        (∀ n ∈ S, ∀ p ∈ (Finset.Ico (lo n) (hi n)).biUnion P,
          (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
            ∑ j ∈ Finset.range (N+2), B n j*log p^j) ∧
        let J := (∑ n ∈ S, ∑ p ∈ (Finset.Ico (lo n) (hi n)).biUnion P,
          residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
        let K := retainedCenteredCost E P S B N X b y L;
        -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_centered_bounds
  refine ⟨E,hE,fun A P S N X b y L lo hi hL hS hSF hends hdis hp => ?_⟩
  obtain ⟨B,hcoef,hid,hb⟩ := hbound A P S N X b y L lo hi hL hS hSF hends
    (fun n hn i hi p hp' => hp n hn p (Finset.mem_biUnion.mpr ⟨i,hi,hp'⟩))
  refine ⟨B,hcoef,?_,?_⟩
  · intro n hn p hp'
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hp'
    exact hid n hn i hi p hpi
  · have he n (hn : n ∈ S) := selected_union_sum P b (lo n) (hi n) (hends n hn).2 hdis
      (fun p => residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n))
    simpa only [Finset.sum_congr rfl he] using hb

/-- One arithmetic constant pays finite radial/count families of moving
literal prime intervals. The cost keeps each block's exact allocation energy;
there is no maximum-order or family-cardinality multiplier. -/
theorem exists_literal_centered_family_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (A S : ℕ → Finset ℕ)
      (P : ℕ → ℕ → Finset ℕ) (N X b : ℕ → ℕ) (y L : ℕ → ℝ)
      (lo hi : ℕ → ℕ → ℕ),
      (∀ i ∈ I, 0 < L i) →
      (∀ i ∈ I, S i ⊆ Finset.Ioc 1 (X i)) →
      (∀ i ∈ I, ∀ n ∈ S i, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ i ∈ I, ∀ n ∈ S i, lo i n ≤ hi i n ∧ hi i n ≤ 2^(b i)) →
      (∀ i ∈ I, ∀ n ∈ S i, ∀ t ∈ Finset.Ico (lo i n) (hi i n), ∀ p ∈ P i t,
        p.Prime ∧ p ∈ A i ∧ ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℕ → ℝ,
        (∀ i ∈ I, ∀ n ∈ S i, ∀ j ≤ N i+1,
          0 ≤ B i n j ∧ B i n j ≤ ((N i+1).choose j : ℝ)*log n^(N i+1-j)) ∧
        (∀ i ∈ I, ∀ n ∈ S i, ∀ t ∈ Finset.Ico (lo i n) (hi i n), ∀ p ∈ P i t,
          (1-boundedShare (A i) (N i) (p*n))*log (p*n : ℕ)^(N i+1) =
            ∑ j ∈ Finset.range (N i+2), B i n j*log p^j) ∧
        let J := ∑ i ∈ I, (∑ n ∈ S i, ∑ t ∈ Finset.Ico (lo i n) (hi i n), ∑ p ∈ P i t,
          residualCoefficient (A i) (L i) (N i) (p*n)*
            zetaPrimeLogKernel (N i) (3/2+Complex.I*y i) (p*n)).re;
        let K := ∑ i ∈ I, retainedCenteredCost E (P i) (S i) (B i) (N i) (X i) (b i) (y i) (L i);
        -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_centered_bounds
  refine ⟨E,hE,fun I A S P N X b y L lo hi hL hS hSF hends hp => ?_⟩
  have hex i (hI : i ∈ I) := hbound (A i) (P i) (S i) (N i) (X i) (b i) (y i) (L i)
    (lo i) (hi i) (hL i hI) (hS i hI) (hSF i hI) (hends i hI) (hp i hI)
  choose B hcoef hid hb using hex
  let B' := fun i n j => if hi : i ∈ I then B i hi n j else 0
  refine ⟨B',?_,?_,?_⟩
  · intro i hi n hn j hj
    simpa only [B',dif_pos hi] using hcoef i hi n hn j hj
  · intro i hi n hn t ht p hp'
    simpa only [B',dif_pos hi] using hid i hi n hn t ht p hp'
  · let J := fun i => (∑ n ∈ S i, ∑ t ∈ Finset.Ico (lo i n) (hi i n), ∑ p ∈ P i t,
        residualCoefficient (A i) (L i) (N i) (p*n)*
          zetaPrimeLogKernel (N i) (3/2+Complex.I*y i) (p*n)).re
    have hbi i (hI : i ∈ I) :
        -retainedCenteredCost E (P i) (S i) (B' i) (N i) (X i) (b i) (y i) (L i) ≤ J i ∧
        J i ≤ retainedCenteredCost E (P i) (S i) (B' i) (N i) (X i) (b i) (y i) (L i) := by
      simpa only [J,B',dif_pos hI] using hb i hI
    have hl := Finset.sum_le_sum (fun i (hI : i ∈ I) => (hbi i hI).1)
    have hu := Finset.sum_le_sum (fun i (hI : i ∈ I) => (hbi i hI).2)
    rw [Finset.sum_neg_distrib] at hl
    exact ⟨hl,hu⟩

/-- Unique largest-prime ownership transports the estimate to an actual
finite set of integer labels. No selected label or prime incidence is spent
twice. This does not assert that the selected labels exhaust the core. -/
theorem exists_literal_centered_owned_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Finset ℕ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (N X b : ℕ) (y L : ℝ) (lo hi : ℕ → ℕ),
      0 < L → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ i < 2^b, ∀ j < 2^b, i ≠ j → Disjoint (P i) (P j)) →
      let Q := fun n => (Finset.Ico (lo n) (hi n)).biUnion P;
      (∀ n ∈ S, ∀ p ∈ Q n,
        p.Prime ∧ p ∈ A ∧ ∀ r : ℕ, r.Prime → r ∣ n → r < p) →
      ∃ B : ℕ → ℕ → ℝ,
        (∀ n ∈ S, ∀ j ≤ N+1,
          0 ≤ B n j ∧ B n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j)) ∧
        (∀ n ∈ S, ∀ p ∈ Q n,
          (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
            ∑ j ∈ Finset.range (N+2), B n j*log p^j) ∧
        let labels := S.biUnion (fun n => (Q n).image (fun p => n*p));
        let J := (∑ n ∈ labels,
          residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re;
        let K := retainedCenteredCost E P S B N X b y L;
        -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_centered_union_bounds
  refine ⟨E,hE,fun A P S N X b y L lo hi hL hS hSF hends hdis hp => ?_⟩
  dsimp only at hp ⊢
  obtain ⟨B,hcoef,hid,hb⟩ := hbound A P S N X b y L lo hi hL hS hSF hends hdis
    (fun n hn p hp' => ⟨(hp n hn p hp').1,(hp n hn p hp').2.1,
      fun hpn => (lt_irrefl p) ((hp n hn p hp').2.2 p (hp n hn p hp').1 hpn)⟩)
  refine ⟨B,hcoef,hid,?_⟩
  have he := ZetaRieszCoupledWindow.sum_owned_products S
    (fun n => (Finset.Ico (lo n) (hi n)).biUnion P)
    (fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    (fun n hn => (hSF n hn).1.ne_zero)
    (fun n hn p hp' => ⟨(hp n hn p hp').1,(hp n hn p hp').2.2⟩)
  rw [he]
  simpa only [Nat.mul_comm] using hb

end RiemannGaussian.ZetaRieszCenteredPrimeEnergy
