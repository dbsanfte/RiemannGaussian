/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmallCofactorCancellation

/-!
# Signed transport between active cofactor-count crossings

Opposite Mobius ranks at nearby logarithmic bases pay their DISTANCE,
not two separate crossing amplitudes. Both hinges and the original common
complex phase/factorial/allocation are retained. Matched original orbits
are disjoint, and every unmatched incidence remains signed. The theorem
applies after both old zero deletions; it does not assert a global cover
or a source-scale bound on the resulting transport cost.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCrossCountTransport
open ZetaRieszSmallCofactorCancellation ZetaRieszShortDivisorOrbits
open ZetaRieszShortDivisorCancellation ZetaRieszHingePairCancellation
open ZetaRieszSignedConvolution ZetaRieszPrimeEndpoint ZetaRieszParityPacket
open ZetaRieszPrimeCountFrequency

/-- The TWO original translated hinges on one based divisor orbit. -/
def basedResponse (a p R : ℕ) (L : ℝ) (e : ℕ) : ℝ :=
  VaughanLogAverage.riesz (log (p*a : ℕ)-L-log e) R-
    VaughanLogAverage.riesz (log a-L-log e) R

private theorem quotient_log {a e : ℕ} (ha : Squarefree a) (he : e ∣ a) :
    log (a/e : ℕ)=log a-log e := by
  have he0 := Nat.pos_of_dvd_of_pos he (Nat.pos_of_ne_zero ha.ne_zero)
  have hb0 : 0<a/e := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero) he) he0
  have hl : log a=log e+log (a/e : ℕ) := by
    conv_lhs => rw [← Nat.mul_div_cancel' he]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast he0.ne') (by exact_mod_cast hb0.ne')]
  linarith

/-- The weight is evaluated at the ORIGINAL label, on every rank. -/
theorem weighted_based_sum_eq {a p R e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (he : e ∣ a/R) (L : ℝ) (w : ℂ) :
    (∑ db ∈ orbitDivisors a R e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      w*(μ (a/e) : ℂ)*(basedResponse a p R L e : ℂ) := by
  rw [weighted_orbit_eq_riesz_difference ha hp hRa he L w,
    base_log ha hp (base_dvd hRa he),quotient_log ha (base_dvd hRa he)]
  simp only [basedResponse,sub_right_comm]

private theorem cutoff_lipschitz {R : ℕ} (hs : Squarefree R)
    (hc : 2≤R.primeFactors.card) (x z : ℝ) :
    |VaughanLogAverage.riesz x R-VaughanLogAverage.riesz z R|≤
      (2 : ℝ)^R.primeFactors.card/4*|x-z| := by
  have h := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter x z hs hc
  rw [ZetaRieszTentSlope.absolute_divisor_mass_eq_card hs,
    ZetaRieszSmoothHead.card_divisors_of_squarefree hs,Nat.cast_pow,Nat.cast_ofNat] at h
  exact h.trans_eq (by ring)

/-- The joined two-hinge profile pays one logarithmic distance. No
comparison of Fourier norms or separate prime-leg limits enters. -/
theorem basedResponse_lipschitz {R : ℕ} (hs : Squarefree R)
    (hc : 2≤R.primeFactors.card) (a p e f : ℕ) (L : ℝ) :
    |basedResponse a p R L e-basedResponse a p R L f|≤
      (2 : ℝ)^R.primeFactors.card/2*|log e-log f| := by
  have h₁ := cutoff_lipschitz hs hc (log (p*a : ℕ)-L-log e)
    (log (p*a : ℕ)-L-log f)
  have h₂ := cutoff_lipschitz hs hc (log a-L-log e) (log a-L-log f)
  have he₁ : (log (p*a : ℕ)-L-log e)-(log (p*a : ℕ)-L-log f)=-(log e-log f) := by ring
  have he₂ : (log a-L-log e)-(log a-L-log f)=-(log e-log f) := by ring
  rw [he₁,abs_neg] at h₁
  rw [he₂,abs_neg] at h₂
  unfold basedResponse
  rw [show (VaughanLogAverage.riesz (log (p*a : ℕ)-L-log e) R-
      VaughanLogAverage.riesz (log a-L-log e) R)-
      (VaughanLogAverage.riesz (log (p*a : ℕ)-L-log f) R-
        VaughanLogAverage.riesz (log a-L-log f) R)=
      (VaughanLogAverage.riesz (log (p*a : ℕ)-L-log e) R-
        VaughanLogAverage.riesz (log (p*a : ℕ)-L-log f) R)-
      (VaughanLogAverage.riesz (log a-L-log e) R-
        VaughanLogAverage.riesz (log a-L-log f) R) by ring]
  exact (abs_sub _ _).trans (by linarith only [h₁,h₂])

/-- When the OTHER hinge is actually saturated on both bases, the
cross-count cost improves by another factor two. -/
theorem basedResponse_lipschitz_of_first_saturated {R : ℕ} (hs : Squarefree R)
    (hc : 2≤R.primeFactors.card) (a p e f : ℕ) (L : ℝ)
    (he : log R≤log (p*a : ℕ)-L-log e)
    (hf : log R≤log (p*a : ℕ)-L-log f) :
    |basedResponse a p R L e-basedResponse a p R L f|≤
      (2 : ℝ)^R.primeFactors.card/4*|log e-log f| := by
  have hR1 : R≠1 := by intro h; simp [h] at hc
  have hnp : ¬R.Prime := by intro h; rw [h.primeFactors] at hc; simp at hc
  unfold basedResponse
  rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hs hR1 hnp he,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hs hR1 hnp hf]
  have h := cutoff_lipschitz hs hc (log a-L-log e) (log a-L-log f)
  rw [show (log a-L-log e)-(log a-L-log f)=-(log e-log f) by ring,abs_neg] at h
  simpa only [zero_sub,neg_sub_neg,abs_sub_comm] using h

/-- The symmetric improvement when both second hinges are exactly zero.
This covers the other active crossing without deleting either hinge. -/
theorem basedResponse_lipschitz_of_second_nonpos {R : ℕ} (hs : Squarefree R)
    (hc : 2≤R.primeFactors.card) (a p e f : ℕ) (L : ℝ)
    (he : log a-L-log e≤0) (hf : log a-L-log f≤0) :
    |basedResponse a p R L e-basedResponse a p R L f|≤
      (2 : ℝ)^R.primeFactors.card/4*|log e-log f| := by
  unfold basedResponse
  rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos he,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos hf,sub_zero,sub_zero]
  have h := cutoff_lipschitz hs hc (log (p*a : ℕ)-L-log e)
    (log (p*a : ℕ)-L-log f)
  rw [show (log (p*a : ℕ)-L-log e)-(log (p*a : ℕ)-L-log f)=-(log e-log f) by ring,
    abs_neg] at h
  exact h

/-- Each matched pair may use EITHER inactive hinge. Different pairs and
count classes need not use the same side of the physical crossing. -/
theorem basedResponse_lipschitz_of_inactive_hinge {R : ℕ} (hs : Squarefree R)
    (hc : 2≤R.primeFactors.card) (a p e f : ℕ) (L : ℝ)
    (hinactive : (log R≤log (p*a : ℕ)-L-log e ∧ log R≤log (p*a : ℕ)-L-log f) ∨
      (log a-L-log e≤0 ∧ log a-L-log f≤0)) :
    |basedResponse a p R L e-basedResponse a p R L f|≤
      (2 : ℝ)^R.primeFactors.card/4*|log e-log f| := by
  rcases hinactive with h | h
  · exact basedResponse_lipschitz_of_first_saturated hs hc a p e f L h.1 h.2
  · exact basedResponse_lipschitz_of_second_nonpos hs hc a p e f L h.1 h.2

/-- Opposite cofactor-count parity is joined BEFORE any inequality.
There is no requirement that the ranks be adjacent. -/
theorem opposite_based_sum_eq {a p R e f : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (he : e ∣ a/R) (hf : f ∣ a/R)
    (hopp : μ (a/f)= -μ (a/e)) (L : ℝ) (w : ℂ) :
    (∑ db ∈ orbitDivisors a R e, w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))+
      (∑ db ∈ orbitDivisors a R f, w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      w*(μ (a/e) : ℂ)*((basedResponse a p R L e-basedResponse a p R L f : ℝ) : ℂ) := by
  rw [weighted_based_sum_eq ha hp hRa he,weighted_based_sum_eq ha hp hRa hf,hopp]
  push_cast
  ring

private theorem opposite_real_floor {m : ℤ} (hm : |(m : ℝ)|≤1)
    {x B : ℝ} (hx : |x|≤B) (w : ℂ) :
    -|w.re| * B≤(w*(m : ℂ)*(x : ℂ)).re := by
  simp only [Complex.mul_re,Complex.intCast_re,Complex.intCast_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have h := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_right hm (abs_nonneg x)).trans (by simpa using hx))
    (abs_nonneg w.re)
  have hl := neg_abs_le (w.re*(m : ℝ)*x)
  rw [abs_mul,abs_mul] at hl
  nlinarith only [h,hl]

/-- A direct independent floor for the full ORIGINAL opposite-rank pair,
with its original complex direction and both hinges retained. -/
theorem opposite_based_floor {a p R e f : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (hc : 2≤R.primeFactors.card)
    (he : e ∣ a/R) (hf : f ∣ a/R) (hopp : μ (a/f)= -μ (a/e))
    (L : ℝ) (w : ℂ) :
    -|w.re| * ((2 : ℝ)^R.primeFactors.card/2*|log e-log f|)≤
      ((∑ db ∈ orbitDivisors a R e, w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))+
        (∑ db ∈ orbitDivisors a R f, w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))).re := by
  rw [opposite_based_sum_eq ha hp hRa he hf hopp]
  exact opposite_real_floor (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a/e))
    (basedResponse_lipschitz (ha.squarefree_of_dvd hRa) hc a p e f L) w

/-- For the saturated opposite hinge, a canonical two-small-prime
crossing costs just `|log e-log f|`, rather than two tent heights. -/
theorem opposite_based_floor_of_first_saturated {a p R e f : ℕ}
    (ha : Squarefree a) (hp : p.Prime) (hRa : R ∣ a) (hc : 2≤R.primeFactors.card)
    (he : e ∣ a/R) (hf : f ∣ a/R) (hopp : μ (a/f)= -μ (a/e))
    (L : ℝ) (hse : log R≤log (p*a : ℕ)-L-log e)
    (hsf : log R≤log (p*a : ℕ)-L-log f) (w : ℂ) :
    -|w.re| * ((2 : ℝ)^R.primeFactors.card/4*|log e-log f|)≤
      ((∑ db ∈ orbitDivisors a R e, w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))+
        (∑ db ∈ orbitDivisors a R f, w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))).re := by
  rw [opposite_based_sum_eq ha hp hRa he hf hopp]
  exact opposite_real_floor (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a/e))
    (basedResponse_lipschitz_of_first_saturated (ha.squarefree_of_dvd hRa) hc a p e f L hse hsf) w

/-- A parity-reversing involution transports the ENTIRE signed spectrum,
across any number of count classes. The common observation is applied
only after cancellation; no parity class is priced separately. -/
theorem signed_involution_floor (E : Finset ℕ) (τ : ℕ→ℕ) (σ : ℕ→ℤ)
    (F cost : ℕ→ℝ) (w : ℂ)
    (hmem : ∀ e∈E, τ e∈E) (hinv : ∀ e∈E, τ (τ e)=e)
    (hopp : ∀ e∈E, σ (τ e)= -σ e) (hσ : ∀ e∈E, |(σ e : ℝ)|≤1)
    (hF : ∀ e∈E, |F e-F (τ e)|≤cost e) :
    -|w.re|/2*(∑ e∈E, cost e)≤(∑ e∈E, w*(σ e : ℂ)*(F e : ℂ)).re := by
  let g := fun e => (w*(σ e : ℂ)*(F e : ℂ)).re
  have hperm : (∑ e∈E, g (τ e))=∑ e∈E, g e := by
    apply Finset.sum_bij (fun e _ => τ e)
    · exact hmem
    · intro e he f hf hef
      exact (hinv e he).symm.trans ((congrArg τ hef).trans (hinv f hf))
    · intro f hf
      exact ⟨τ f,hmem f hf,hinv f hf⟩
    · intros; rfl
  have hpair (e : ℕ) (he : e∈E) : -|w.re| * cost e≤g e+g (τ e) := by
    have h := opposite_real_floor (hσ e he) (hF e he) w
    dsimp [g]
    rw [hopp e he]
    convert h using 1
    simp only [Complex.mul_re,Complex.intCast_re,
      Complex.intCast_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
      sub_zero,Int.cast_neg,Complex.neg_re,Complex.neg_im]
    ring
  have hs := Finset.sum_le_sum hpair
  rw [Finset.sum_add_distrib,hperm,← Finset.mul_sum] at hs
  rw [Complex.re_sum]
  change -|w.re|/2*(∑ e∈E, cost e)≤∑ e∈E, g e
  linarith only [hs]

/-- The same joined transport controls BOTH floor and ceiling; it is
independent of the orientation of the original complex observation. -/
theorem signed_involution_abs (E : Finset ℕ) (τ : ℕ→ℕ) (σ : ℕ→ℤ)
    (F cost : ℕ→ℝ) (w : ℂ)
    (hmem : ∀ e∈E, τ e∈E) (hinv : ∀ e∈E, τ (τ e)=e)
    (hopp : ∀ e∈E, σ (τ e)= -σ e) (hσ : ∀ e∈E, |(σ e : ℝ)|≤1)
    (hF : ∀ e∈E, |F e-F (τ e)|≤cost e) :
    |(∑ e∈E, w*(σ e : ℂ)*(F e : ℂ)).re|≤|w.re|/2*(∑ e∈E, cost e) := by
  have hp := signed_involution_floor E τ σ F cost w hmem hinv hopp hσ hF
  have hn := signed_involution_floor E τ σ F cost (-w) hmem hinv hopp hσ hF
  simp only [neg_mul,Finset.sum_neg_distrib,Complex.neg_re,abs_neg] at hn
  exact abs_le.mpr ⟨by linarith only [hp],by linarith only [hn]⟩

/-- This selected population is a union of WHOLE original divisor orbits.
The old zero deletions commute with the entire selected spectrum. -/
theorem retained_group_eq_sum {u : ℝ} {N K n R : ℕ}
    (hn : n∈coreBand u N K) (hs : Squarefree n)
    (hRa : R ∣ n/largestPrime n) (hQR : leastPairBlock (n/largestPrime n) ∣ R)
    (E : Finset ℕ) (hE : E⊆((n/largestPrime n)/R).divisors) (w : ℂ) :
    let a := n/largestPrime n
    let D := a.divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db∈D∩E.biUnion (orbitDivisors a R), f db)=
      ∑ e∈E, w*(μ (a/e) : ℂ)*
        (basedResponse a (largestPrime n) R (SquarefreeVaughanLogSource.length u N) e : ℂ) := by
  have hd := core_data hn hs
  have hcop : R.Coprime ((n/largestPrime n)/R) :=
    Nat.coprime_of_squarefree_mul ((Nat.mul_div_cancel' hRa).symm ▸ hd.2.1)
  dsimp only
  rw [Finset.inter_biUnion,Finset.sum_biUnion (by
    intro e he f hf hef
    exact (orbitDivisors_disjoint hcop (hE he) (hE hf) hef).mono
      Finset.inter_subset_right Finset.inter_subset_right)]
  apply Finset.sum_congr rfl
  intro e he
  rw [retained_small_orbit_eq_full hn hs hRa hQR (hE he) w]
  exact weighted_based_sum_eq hd.2.1 hd.1 hRa (Nat.dvd_of_mem_divisors (hE he)) _ w

/-- Independent signed floor on the CURRENT retained cofactor spectrum.
Any parity-reversing transport is allowed, including jumps across several
count classes. Every original unmatched incidence stays signed on the left. -/
theorem retained_matching_floor {u : ℝ} {N K n R : ℕ}
    (hn : n∈coreBand u N K) (hs : Squarefree n)
    (hRa : R ∣ n/largestPrime n) (hQR : leastPairBlock (n/largestPrime n) ∣ R)
    (hc : 2≤R.primeFactors.card) (E : Finset ℕ)
    (hE : E⊆((n/largestPrime n)/R).divisors) (τ : ℕ→ℕ)
    (hmem : ∀ e∈E, τ e∈E) (hinv : ∀ e∈E, τ (τ e)=e)
    (hopp : ∀ e∈E, μ ((n/largestPrime n)/τ e)= -μ ((n/largestPrime n)/e))
    (w : ℂ) :
    let a := n/largestPrime n
    let D := a.divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let O := E.biUnion (orbitDivisors a R)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db∈D\O, f db).re-
      |w.re| * ((2 : ℝ)^R.primeFactors.card/4*(∑ e∈E, |log e-log (τ e)|))≤
        (∑ db∈D, f db).re := by
  have hd := core_data hn hs
  have hb := signed_involution_floor E τ (fun e => μ ((n/largestPrime n)/e))
    (basedResponse (n/largestPrime n) (largestPrime n) R (SquarefreeVaughanLogSource.length u N))
    (fun e => (2 : ℝ)^R.primeFactors.card/2*|log e-log (τ e)|) w hmem hinv hopp
    (by intro e _; exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
    (by intro e _; exact basedResponse_lipschitz (hd.2.1.squarefree_of_dvd hRa) hc _ _ _ _ _)
  rw [← retained_group_eq_sum hn hs hRa hQR E hE w] at hb
  rw [← Finset.mul_sum] at hb
  dsimp only at hb ⊢
  have he := congrArg Complex.re (Finset.sum_inter_add_sum_sdiff
    ((n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n))
    (E.biUnion (orbitDivisors (n/largestPrime n) R))
    (fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)))
  rw [Complex.add_re] at he
  nlinarith only [hb,he]

/-- The same global spectrum principle with the OTHER hinge exactly
saturated. For a canonical pair, the complete matching cost is HALF the
sum of matched log distances (each pair is counted twice). -/
theorem retained_matching_floor_of_first_saturated {u : ℝ} {N K n R : ℕ}
    (hn : n∈coreBand u N K) (hs : Squarefree n)
    (hRa : R ∣ n/largestPrime n) (hQR : leastPairBlock (n/largestPrime n) ∣ R)
    (hc : 2≤R.primeFactors.card) (E : Finset ℕ)
    (hE : E⊆((n/largestPrime n)/R).divisors) (τ : ℕ→ℕ)
    (hmem : ∀ e∈E, τ e∈E) (hinv : ∀ e∈E, τ (τ e)=e)
    (hopp : ∀ e∈E, μ ((n/largestPrime n)/τ e)= -μ ((n/largestPrime n)/e))
    (hfull : ∀ e∈E, log R≤log (largestPrime n*(n/largestPrime n) : ℕ)-
      SquarefreeVaughanLogSource.length u N-log e) (w : ℂ) :
    let a := n/largestPrime n
    let D := a.divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let O := E.biUnion (orbitDivisors a R)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db∈D\O, f db).re-
      |w.re| * ((2 : ℝ)^R.primeFactors.card/8*(∑ e∈E, |log e-log (τ e)|))≤
        (∑ db∈D, f db).re := by
  have hd := core_data hn hs
  have hb := signed_involution_floor E τ (fun e => μ ((n/largestPrime n)/e))
    (basedResponse (n/largestPrime n) (largestPrime n) R (SquarefreeVaughanLogSource.length u N))
    (fun e => (2 : ℝ)^R.primeFactors.card/4*|log e-log (τ e)|) w hmem hinv hopp
    (by intro e _; exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
    (by
      intro e he
      exact basedResponse_lipschitz_of_first_saturated
        (hd.2.1.squarefree_of_dvd hRa) hc _ _ _ _ _ (hfull e he) (hfull (τ e) (hmem e he)))
  rw [← retained_group_eq_sum hn hs hRa hQR E hE w] at hb
  rw [← Finset.mul_sum] at hb
  dsimp only at hb ⊢
  have he := congrArg Complex.re (Finset.sum_inter_add_sum_sdiff
    ((n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n))
    (E.biUnion (orbitDivisors (n/largestPrime n) R))
    (fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)))
  rw [Complex.add_re] at he
  nlinarith only [hb,he]

/-- One signed matching may couple BOTH kinds of active crossing and
arbitrarily many count ranks. The exact other-hinge zeros are checked per
pair, so opposite crossings are never incorrectly completed or norm-paid. -/
theorem retained_matching_floor_of_inactive_hinge {u : ℝ} {N K n R : ℕ}
    (hn : n∈coreBand u N K) (hs : Squarefree n)
    (hRa : R ∣ n/largestPrime n) (hQR : leastPairBlock (n/largestPrime n) ∣ R)
    (hc : 2≤R.primeFactors.card) (E : Finset ℕ)
    (hE : E⊆((n/largestPrime n)/R).divisors) (τ : ℕ→ℕ)
    (hmem : ∀ e∈E, τ e∈E) (hinv : ∀ e∈E, τ (τ e)=e)
    (hopp : ∀ e∈E, μ ((n/largestPrime n)/τ e)= -μ ((n/largestPrime n)/e))
    (hinactive : ∀ e∈E,
      (log R≤log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N-log e ∧
       log R≤log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N-log (τ e)) ∨
      (log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N-log e≤0 ∧
       log (n/largestPrime n : ℕ)-SquarefreeVaughanLogSource.length u N-log (τ e)≤0)) (w : ℂ) :
    let a := n/largestPrime n
    let D := a.divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let O := E.biUnion (orbitDivisors a R)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db∈D\O, f db).re-
      |w.re| * ((2 : ℝ)^R.primeFactors.card/8*(∑ e∈E, |log e-log (τ e)|))≤
        (∑ db∈D, f db).re := by
  have hd := core_data hn hs
  have hb := signed_involution_floor E τ (fun e => μ ((n/largestPrime n)/e))
    (basedResponse (n/largestPrime n) (largestPrime n) R (SquarefreeVaughanLogSource.length u N))
    (fun e => (2 : ℝ)^R.primeFactors.card/4*|log e-log (τ e)|) w hmem hinv hopp
    (by intro e _; exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
    (by
      intro e he
      exact basedResponse_lipschitz_of_inactive_hinge
        (hd.2.1.squarefree_of_dvd hRa) hc _ _ _ _ _ (hinactive e he))
  rw [← retained_group_eq_sum hn hs hRa hQR E hE w] at hb
  rw [← Finset.mul_sum] at hb
  dsimp only at hb ⊢
  have he := congrArg Complex.re (Finset.sum_inter_add_sum_sdiff
    ((n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n))
    (E.biUnion (orbitDivisors (n/largestPrime n) R))
    (fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)))
  rw [Complex.add_re] at he
  nlinarith only [hb,he]

/-- Apply the same cancellation to ALL selected original labels/counts
and radial periods together. The coefficient is the exact real original
weight, never an absolute Fourier budget or a completed prime profile. -/
theorem global_retained_matching_floor (u y : ℝ) (N K : ℕ)
    (S : Finset ℕ) (hS : S⊆coreBand u N K) (hSF : ∀ n∈S, Squarefree n)
    (E : ℕ→Finset ℕ) (τ : ℕ→ℕ→ℕ)
    (hE : ∀ n∈S, E n⊆((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hmem : ∀ n∈S, ∀ e∈E n, τ n e∈E n)
    (hinv : ∀ n∈S, ∀ e∈E n, τ n (τ n e)=e)
    (hopp : ∀ n∈S, ∀ e∈E n,
      μ ((n/largestPrime n)/τ n e)= -μ ((n/largestPrime n)/e)) :
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let O := fun n => (E n).biUnion (orbitDivisors (n/largestPrime n)
      (leastPairBlock (n/largestPrime n)))
    let w := fun n => phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)
    let f := fun n (db : ℕ×ℕ) => w n*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ n∈S, ∑ db∈D n\O n, f n db).re-
      (∑ n∈S, |(w n).re| * (∑ e∈E n, |log e-log (τ n e)|))≤
        (∑ n∈S, ∑ db∈D n, f n db).re := by
  dsimp only
  have h (n : ℕ) (hn : n∈S) := retained_matching_floor (hS hn) (hSF n hn)
    (canonical_block_data (hS hn) (hSF n hn)).1 (dvd_refl _)
    (by rw [(canonical_block_data (hS hn) (hSF n hn)).2.1])
    (E n) (hE n hn) (τ n) (hmem n hn) (hinv n hn) (hopp n hn)
    (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n))
  have hh (n : ℕ) (hn : n∈S) := h n hn
  have hs := Finset.sum_le_sum (fun n hn => by
    have hh := hh n hn
    dsimp only at hh
    have hC : (2 : ℝ)^(leastPairBlock (n/largestPrime n)).primeFactors.card/4=1 := by
      rw [(canonical_block_data (hS hn) (hSF n hn)).2.1]
      norm_num
    rw [hC,one_mul] at hh
    exact hh)
  simpa only [Finset.sum_sub_distrib,Complex.re_sum] using hs

/-- Direct application to the CURRENT endgame scalar. Existing signed
whole-row payments are retained ONCE. The only new debit is the joint
log-transport cost, and the entire unmatched central spectrum is explicit. -/
theorem polynomialCentralRemaining_transport_floor (u y : ℝ) (j : ℕ)
    (E : ℕ→Finset ℕ) (τ : ℕ→ℕ→ℕ) :
    let N := dyadicMomentOrder j
    let K := dyadicPrimeCount j
    let S := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let O := fun n => (E n).biUnion (orbitDivisors (n/largestPrime n)
      (leastPairBlock (n/largestPrime n)))
    let w := fun n => phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)
    let f := fun n (db : ℕ×ℕ) => w n*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∀ n∈S, E n⊆((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)→
    (∀ n∈S, ∀ e∈E n, τ n e∈E n)→
    (∀ n∈S, ∀ e∈E n, τ n (τ n e)=e)→
    (∀ n∈S, ∀ e∈E n, μ ((n/largestPrime n)/τ n e)= -μ ((n/largestPrime n)/e))→
    (∑ n∈S, ∑ db∈D n\O n, f n db).re-
      (∑ n∈S, |(w n).re| * (∑ e∈E n, |log e-log (τ n e)|))-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+
        ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j≤
        ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j := by
  dsimp only
  intro hE hmem hinv hopp
  have h := global_retained_matching_floor u y (dyadicMomentOrder j) (dyadicPrimeCount j)
    _ (by intro n hn; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1)
    (by intro n hn; exact (Finset.mem_filter.mp hn).2) E τ hE hmem hinv hopp
  dsimp only at h
  rw [← ZetaRieszCrossingOrbitCancellation.centralConvolution_eq_affine_sdiff] at h
  rw [ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining_eq]
  linarith only [h]

/-- A common multiplicative factor does not change transport distance.
Thus one near-relation lifts to every disjoint background rank. -/
theorem log_distance_common_factor {e x z : ℕ} (he : 0<e) (hx : 0<x) (hz : 0<z) :
    |log (e*x : ℕ)-log (e*z : ℕ)|=|log x-log z| := by
  rw [Nat.cast_mul,Nat.cast_mul,
    log_mul (by exact_mod_cast he.ne') (by exact_mod_cast hx.ne'),
    log_mul (by exact_mod_cast he.ne') (by exact_mod_cast hz.ne')]
  congr 1
  ring

/-- Opposite multiplicative parity lifts automatically through arbitrary
additional cofactor counts, without a new phase or factorial comparison. -/
theorem opposite_cofactor_parity_common_factor {a e x z : ℕ} (ha : Squarefree a)
    (hex : e*x ∣ a) (hez : e*z ∣ a) (hx : e.Coprime x) (hz : e.Coprime z)
    (hopp : μ z= -μ x) : μ (a/(e*z))= -μ (a/(e*x)) := by
  have h₁ : μ (a/(e*z))=μ a*μ (e*z) := by
    exact_mod_cast RoughMoebiusHyperbola.moebius_cofactor ha hez
  have h₂ : μ (a/(e*x))=μ a*μ (e*x) := by
    exact_mod_cast RoughMoebiusHyperbola.moebius_cofactor ha hex
  rw [h₁,h₂,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hx,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hz,hopp]
  ring

/-- The SAME signed near-relation controls all its background cofactor
counts at once. Distinctness/coverage remains required when spending this
bound as a suballocation in `global_retained_matching_floor`. -/
theorem replicated_relation_floor {a p R x z : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (hc : 2≤R.primeFactors.card)
    (E : Finset ℕ) (he : ∀ e∈E, e*x ∣ a/R ∧ e*z ∣ a/R)
    (hcop : ∀ e∈E, e.Coprime x ∧ e.Coprime z) (hopp : μ z= -μ x)
    (hx : 0<x) (hz : 0<z) (L : ℝ) (w : ℂ) :
    -|w.re| * ((2 : ℝ)^R.primeFactors.card/2*|log x-log z|)*(E.card : ℝ)≤
      (∑ e∈E,
        ((∑ db∈orbitDivisors a R (e*x), w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))+
        (∑ db∈orbitDivisors a R (e*z), w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)))).re := by
  have h (e : ℕ) (hm : e∈E) := opposite_based_floor ha hp hRa hc
    (he e hm).1 (he e hm).2
    (opposite_cofactor_parity_common_factor ha (base_dvd hRa (he e hm).1)
      (base_dvd hRa (he e hm).2) (hcop e hm).1 (hcop e hm).2 hopp) L w
  have he0 (e : ℕ) (hm : e∈E) : 0<e := by
    have hp0 := Nat.pos_of_dvd_of_pos (base_dvd hRa (he e hm).1) (Nat.pos_of_ne_zero ha.ne_zero)
    by_contra hh
    have hz : e=0 := by omega
    simp [hz] at hp0
  have hs := Finset.sum_le_sum (fun e hm => by
    have hh := h e hm
    rw [log_distance_common_factor (he0 e hm) hx hz] at hh
    exact hh)
  rw [Complex.re_sum]
  convert! hs using 1
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

/-- A pure active parity layer admits NO parity-reversing matching.
This is the exact obstruction to upgrading local log transport into a
uniform global cancellation guarantee merely by increasing the count. -/
theorem single_parity_no_transport (E : Finset ℕ) (hE : E.Nonempty)
    (σ : ℕ→ℤ) {c : ℤ} (hc : c≠0) (hσ : ∀ e∈E, σ e=c) :
    ¬∃ τ : ℕ→ℕ, (∀ e∈E, τ e∈E) ∧ (∀ e∈E, σ (τ e)= -σ e) := by
  rintro ⟨τ,hmem,hopp⟩
  obtain ⟨e,he⟩ := hE
  have h := hopp e he
  rw [hσ e he,hσ (τ e) (hmem e he)] at h
  omega

/-- On a single reinforcing parity layer the separate price is EXACT,
even with the full original complex direction. More counts alone cannot
give a uniform saving on this geometry. -/
theorem single_parity_exact_price (E : Finset ℕ) (σ : ℕ→ℤ)
    (F : ℕ→ℝ) (w : ℂ) {c : ℤ} (hc : |(c : ℝ)|=1)
    (hσ : ∀ e∈E, σ e=c) (hF : ∀ e∈E, 0≤F e) :
    |(∑ e∈E, w*(σ e : ℂ)*(F e : ℂ)).re|=|w.re| * (∑ e∈E, F e) := by
  have hs : (∑ e∈E, w*(σ e : ℂ)*(F e : ℂ))=
      w*(c : ℂ)*((∑ e∈E, F e : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e he => by rw [hσ e he])
  rw [hs]
  simp only [Complex.mul_re,Complex.intCast_re,Complex.intCast_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [abs_mul,abs_mul,hc,mul_one,abs_of_nonneg (Finset.sum_nonneg hF)]

/-- Separated clustered prime logs can put EVERY active divisor in one
rank, even as the total cofactor count grows. Both interval edges are
literal; the empty divisor and all other ranks are checked as well. -/
theorem clustered_active_rank {B d : ℕ} (hB : Squarefree B)
    (hd : d∈B.divisors) {α ε D W : ℝ} (hε : 0≤ε) (hα : 0≤α-ε)
    (hprimes : ∀ q∈B.primeFactors, α-ε≤log q ∧ log q≤α+ε)
    (j : ℕ) (hlo : ((j-1 : ℕ) : ℝ)*(α+ε)+W≤D)
    (hhi : D≤((j+1 : ℕ) : ℝ)*(α-ε))
    (hactive : D-W<log d ∧ log d<D) : d.primeFactors.card=j := by
  have hs := hB.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hsub := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hB.ne_zero
  have hl : (d.primeFactors.card : ℝ)*(α-ε)≤log d := by
    have h := Finset.sum_le_sum (fun q hq => (hprimes q (hsub hq)).1)
    rw [Finset.sum_const,nsmul_eq_mul,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at h
    exact h
  have hh : log d≤(d.primeFactors.card : ℝ)*(α+ε) := by
    have h := Finset.sum_le_sum (fun q hq => (hprimes q (hsub hq)).2)
    rw [Finset.sum_const,nsmul_eq_mul,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at h
    exact h
  have hα' : 0≤α+ε := by linarith only [hα,hε]
  apply Nat.le_antisymm
  · by_contra hj
    have hnat : j+1≤d.primeFactors.card := by omega
    have hcast : ((j+1 : ℕ) : ℝ)≤d.primeFactors.card := by exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hcast hα
    linarith only [hl,hmul,hhi,hactive.2]
  · by_contra hj
    have hnat : d.primeFactors.card≤j-1 := by omega
    have hcast : (d.primeFactors.card : ℝ)≤(j-1 : ℕ) := by exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hcast hα'
    linarith only [hh,hmul,hlo,hactive.1]

/-- This is a genuine growing-count obstruction, rather than a failed
numerical pairing: a single active clustered rank has constant nonzero
Mobius parity, so no complete active-spectrum transport can exist. -/
theorem clustered_active_no_transport {B : ℕ} (hB : Squarefree B)
    (E : Finset ℕ) (hE : E.Nonempty) (hdiv : E⊆B.divisors)
    {α ε D W : ℝ} (hε : 0≤ε) (hα : 0≤α-ε)
    (hprimes : ∀ q∈B.primeFactors, α-ε≤log q ∧ log q≤α+ε)
    (j : ℕ) (hlo : ((j-1 : ℕ) : ℝ)*(α+ε)+W≤D)
    (hhi : D≤((j+1 : ℕ) : ℝ)*(α-ε))
    (hactive : ∀ d∈E, D-W<log d ∧ log d<D) :
    ¬∃ τ : ℕ→ℕ, (∀ d∈E, τ d∈E) ∧ (∀ d∈E, μ (τ d)= -μ d) := by
  apply single_parity_no_transport E hE (fun d => μ d) (c := (-1 : ℤ)^j)
    (pow_ne_zero j (by norm_num))
  intro d hd
  have h := ZetaRieszReflectedLinear.moebius_eq_primeCount
    (hB.squarefree_of_dvd (Nat.dvd_of_mem_divisors (hdiv hd)))
  have hc := clustered_active_rank hB (hdiv hd) hε hα hprimes j hlo hhi (hactive d hd)
  rw [hc] at h
  exact_mod_cast h

end RiemannGaussian.ZetaRieszCrossCountTransport
