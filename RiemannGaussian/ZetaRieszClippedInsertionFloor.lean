/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerPairFloor

/-!
# Joined clipped-prime insertion on the literal inner crossing

An inserted prime below the active hinge is retained: its response is a
clipped logarithm, not zero. Join every candidate before pricing the
coverage deficit and the complex transport difference. Every original
phase and allocation remains in that difference. Partner existence,
disjoint capacity and a native numerical floor are not asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszClippedInsertionFloor
open ZetaRieszInnerHingeTransport ZetaRieszSignedConvolution
open ZetaRieszJointAllocation ZetaRieszFixedCountPeriod

/-- The complete inserted divisor response is clipped at the prime log.
Orders/counts are unrestricted; no inserted prime is dropped below the hinge. -/
theorem riesz_insert_clipped {r b : ℕ} (hr : r.Prime) (hrb : ¬r ∣ b)
    (hb : b ≠ 0) {D : ℝ} (hD : 0 ≤ D) (hhead : D ≤ log b.minFac) :
    VaughanLogAverage.riesz D (r*b)=min D (log r) := by
  rw [ZetaSquarefreeRieszWindows.riesz_prime_mul D hr hrb,
    ZetaRieszTypeII.riesz_eq_cutoff_below_minFac hb hD hhead]
  rcases le_total D (log r) with h | h
  · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr h),
      sub_zero,min_eq_left h]
  · rw [ZetaRieszTypeII.riesz_eq_cutoff_below_minFac hb
      (sub_nonneg.mpr h) (by linarith [log_natCast_nonneg r]),min_eq_right h]
    ring

/-- Saturating the two actual outer hinges leaves the clipped inserted
response. The upper bound uses the OLD base head, not the inserted prime. -/
theorem response_insert_clipped {p q r b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hb : Squarefree b)
    (hc : 2 ≤ b.primeFactors.card) (hrb : ¬r ∣ b) (hqr : ¬q ∣ r*b)
    {L : ℝ}
    (hsat : log (q*(r*b) : ℕ) ≤ L)
    (hfull : log (r*b : ℕ) ≤ log (p*(q*(r*b)) : ℕ)-L)
    (hD : 0 ≤ log (p*(r*b) : ℕ)-L)
    (hhead : log (p*(r*b) : ℕ)-L ≤ log b.minFac) :
    response L (log p+log (q*(r*b) : ℕ)) (q*(r*b)) =
      -min (log (p*(r*b) : ℕ)-L) (log r) := by
  have hsf : Squarefree (r*b) := Nat.squarefree_mul_iff.mpr
    ⟨hr.coprime_iff_not_dvd.mpr hrb,hr.squarefree,hb⟩
  have hcount : 2 ≤ (r*b).primeFactors.card := hc.trans
    (Finset.card_le_card (Nat.primeFactors_mono (dvd_mul_left b r) hsf.ne_zero))
  have hcomp : r*b ≠ 1 ∧ ¬(r*b).Prime := by
    constructor
    · intro he; simp [he] at hcount
    · intro he; simp [he.primeFactors] at hcount
  have hlogq : log (q*(r*b) : ℕ)=log q+log (r*b : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hq.ne_zero)
      (by exact_mod_cast hsf.ne_zero)]
  have hlogp : log (p*(r*b) : ℕ)=log p+log (r*b : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hsf.ne_zero)]
  have hlogn : log (p*(q*(r*b)) : ℕ)=log p+log (q*(r*b) : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast (mul_ne_zero hq.ne_zero hsf.ne_zero))]
  rw [response,ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr hsat),
    sub_zero,← hlogn,ZetaSquarefreeRieszWindows.riesz_prime_mul _ hq hqr,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hsf hcomp.1 hcomp.2 hfull,
    show log (p*(q*(r*b)) : ℕ)-L-log q=log (p*(r*b) : ℕ)-L by
      rw [hlogn,hlogq,hlogp]; ring,
    riesz_insert_clipped hr hrb hb.ne_zero hD hhead]
  ring

/-- The literal inserted atom has the favorable opposite parity with
its full allocation, complex phase and actual finite-prime mask retained. -/
theorem literal_insert_clipped {p q r b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hb : Squarefree b)
    (hc : 2 ≤ b.primeFactors.card) (hrb : ¬r ∣ b) (hqr : ¬q ∣ r*b)
    (hpqr : ¬p ∣ q*(r*b)) {L : ℝ}
    (hsat : log (q*(r*b) : ℕ) ≤ L)
    (hfull : log (r*b : ℕ) ≤ log (p*(q*(r*b)) : ℕ)-L)
    (hD : 0 ≤ log (p*(r*b) : ℕ)-L)
    (hhead : log (p*(r*b) : ℕ)-L ≤ log b.minFac)
    (A : Finset ℕ) (N : ℕ) (y : ℝ) :
    residualCoefficient A L N (p*(q*(r*b)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*b))) =
      -(μ b : ℂ)*(min (log (p*(r*b) : ℕ)-L) (log r) : ℝ)*
        phaseWeight A L N y (q*(r*b)) p := by
  have hsf : Squarefree (r*b) := Nat.squarefree_mul_iff.mpr
    ⟨hr.coprime_iff_not_dvd.mpr hrb,hr.squarefree,hb⟩
  have hsfq : Squarefree (q*(r*b)) := Nat.squarefree_mul_iff.mpr
    ⟨hq.coprime_iff_not_dvd.mpr hqr,hq.squarefree,hsf⟩
  have hcount : 2 ≤ (q*(r*b)).primeFactors.card := hc.trans
    (Finset.card_le_card (Nat.primeFactors_mono
      (show b ∣ q*(r*b) from dvd_mul_of_dvd_right (dvd_mul_left b r) q) hsfq.ne_zero))
  rw [residual_atom_eq_parity_response hsfq hcount hp hpqr,
    response_insert_clipped hp hq hr hb hc hrb hqr hsat hfull hD hhead,
    moebius_prime_mul_eq_not_dvd hq,if_neg hqr,
    moebius_prime_mul_eq_not_dvd hr,if_neg hrb]
  push_cast
  ring

/-- Join every candidate before pricing. Coverage shortfall and ONE
signed complex transport remain; neither is silently assumed small. -/
theorem joined_insertions_floor {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (F : ℂ) (G : ι → ℂ) {τ : ℝ} (hF : F.re ≤ 0) :
    -max (τ-∑ i∈S,c i) 0*‖F‖-
      ‖∑ i∈S,(c i : ℂ)*(F-G i)‖ ≤
        ((τ : ℂ)*F-∑ i∈S,(c i : ℂ)*G i).re := by
  let C := ∑ i∈S,c i
  have he : (τ : ℂ)*F-∑ i∈S,(c i : ℂ)*G i =
      ((τ-C : ℝ) : ℂ)*F+∑ i∈S,(c i : ℂ)*(F-G i) := by
    dsimp [C]
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,
      ← Complex.ofReal_sum]
    push_cast
    ring
  have hcap : (τ-C)*F.re ≥ max (τ-C) 0*F.re :=
    mul_le_mul_of_nonpos_right (le_max_left _ _) hF
  have hre : -‖F‖ ≤ F.re := (abs_le.mp (Complex.abs_re_le_norm F)).1
  have ht := mul_le_mul_of_nonneg_left hre (le_max_right (τ-C) 0)
  have hd := (abs_le.mp (Complex.abs_re_le_norm
    (∑ i∈S,(c i : ℂ)*(F-G i)))).1
  rw [he,Complex.add_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  dsimp only [C] at hcap ht ⊢
  linarith only [hcap,ht,hd]

/-- Once finite clipped coverage is proved, only the JOINED original
complex transport costs the floor. This is not a capacity hypothesis proof. -/
theorem joined_insertions_floor_of_coverage {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (F : ℂ) (G : ι → ℂ) {τ : ℝ} (hF : F.re ≤ 0)
    (hcover : τ ≤ ∑ i∈S,c i) :
    -‖∑ i∈S,(c i : ℂ)*(F-G i)‖ ≤
      ((τ : ℂ)*F-∑ i∈S,(c i : ℂ)*G i).re := by
  have h := joined_insertions_floor S c F G (τ := τ) hF
  simpa only [max_eq_right (sub_nonpos.mpr hcover),zero_mul,neg_zero,zero_sub] using h

/-- Favorable individual allocation changes do not break the JOINED
transport saving. Only their common lower-tail error is charged, and every
inserted unweighted phase must actually have the favorable real sign. -/
theorem joined_weighted_insertions_floor {ι : Type*} (S : Finset ι)
    (c w : ι → ℝ) (F : ℂ) (G : ι → ℂ) {τ a e : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (he : 0 ≤ e) (hF : F.re ≤ 0)
    (hc : ∀ i∈S,0 ≤ c i) (hG : ∀ i∈S,(G i).re ≤ 0)
    (hw : ∀ i∈S,a ≤ w i+e) :
    -max (τ-∑ i∈S,c i) 0*‖F‖-
        ‖∑ i∈S,(c i : ℂ)*(F-G i)‖-e*(∑ i∈S,c i*‖G i‖) ≤
      ((a : ℂ)*(τ : ℂ)*F-∑ i∈S,(c i : ℂ)*(w i : ℂ)*G i).re := by
  let P := max (τ-∑ i∈S,c i) 0*‖F‖+
    ‖∑ i∈S,(c i : ℂ)*(F-G i)‖
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hj := joined_insertions_floor S c F G (τ := τ) hF
  have hmain : -P ≤ a*((τ : ℂ)*F-∑ i∈S,(c i : ℂ)*G i).re := by
    have h := mul_le_mul_of_nonneg_left hj ha
    have hp := mul_le_mul_of_nonneg_right ha1 hP
    dsimp [P] at *
    nlinarith
  have hsum : -e*(∑ i∈S,c i*‖G i‖) ≤
      (∑ i∈S,(c i : ℂ)*((a-w i : ℝ) : ℂ)*G i).re := by
    simp only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i his
    have hr := (abs_le.mp (Complex.abs_re_le_norm (G i))).1
    have hs := mul_le_mul_of_nonpos_right
      (show a-w i ≤ e by linarith [hw i his]) (hG i his)
    have hn := mul_le_mul_of_nonneg_left hr he
    have hh := mul_le_mul_of_nonneg_left (hn.trans hs) (hc i his)
    nlinarith only [hh]
  have hid : (a : ℂ)*(τ : ℂ)*F-∑ i∈S,(c i : ℂ)*(w i : ℂ)*G i =
      (a : ℂ)*((τ : ℂ)*F-∑ i∈S,(c i : ℂ)*G i)+
        ∑ i∈S,(c i : ℂ)*((a-w i : ℝ) : ℂ)*G i := by
    simp only [Complex.ofReal_sub,mul_sub,sub_mul,Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    ring_nf
  rw [hid,Complex.add_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  dsimp only [P] at hmain
  linarith only [hmain,hsum]

/-- Reuse the proved owner lower tail for an entire insertion family.
There is ONE coupled transport norm; no absolute owner-variation cost.
The common exponential error is the already paid global lower-tail rate. -/
theorem joined_owner_insertions_floor {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (x' : ι → ℝ) (F : ℂ) (G : ι → ℂ)
    {N : ℕ} (hN : 32 ≤ N) {x τ : ℝ} (hx : (3/8 : ℝ) ≤ x)
    (hc : ∀ i∈S,0 ≤ c i) (hx' : ∀ i∈S,x ≤ x' i ∧ x' i ≤ 1)
    (hx1 : x ≤ 1) (hF : F.re ≤ 0) (hG : ∀ i∈S,(G i).re ≤ 0) :
    -max (τ-∑ i∈S,c i) 0*‖F‖-
        ‖∑ i∈S,(c i : ℂ)*(F-G i)‖-
        (2*exp (-(N : ℝ)/25))*(∑ i∈S,c i*‖G i‖) ≤
      ((ZetaRieszOwnerMaximal.ownerWeight N x : ℂ)*(τ : ℂ)*F-
        ∑ i∈S,(c i : ℂ)*(ZetaRieszOwnerMaximal.ownerWeight N (x' i) : ℂ)*G i).re := by
  apply joined_weighted_insertions_floor S c
    (fun i => ZetaRieszOwnerMaximal.ownerWeight N (x' i)) F G
    (ZetaRieszOwnerMaximal.ownerWeight_bounds N (by linarith) hx1).1
    (ZetaRieszOwnerMaximal.ownerWeight_bounds N (by linarith) hx1).2
    (by positivity) hF hc hG
  intro i his
  exact ZetaRieszOwnerPairFloor.ownerWeight_almost_monotone hN hx
    (hx' i his).1 (hx' i his).2

/-- A proved first log-gap moment cancels before norms. The same smooth
complex amplitude is used at every actual total log. The remaining cost
is quadratic in the common gap radius, independent of candidate count. -/
theorem centred_transport_norm {ι : Type*} (S : Finset ι) (c t : ι → ℝ)
    (f g h : ℝ → ℂ) {T ρ M : ℝ} (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hf : ∀ v∈Set.Icc (T-ρ) (T+ρ),HasDerivAt f (g v) v)
    (hg : ∀ v∈Set.Icc (T-ρ) (T+ρ),HasDerivAt g (h v) v)
    (hb : ∀ v∈Set.Icc (T-ρ) (T+ρ),‖h v‖ ≤ M)
    (hc : ∀ i∈S,0 ≤ c i) (ht : ∀ i∈S,|t i-T| ≤ ρ)
    (hcentre : (∑ i∈S,c i*(t i-T))=0) :
    ‖∑ i∈S,(c i : ℂ)*(f T-f (t i))‖ ≤
      M*ρ*(∑ i∈S,c i*|t i-T|) := by
  have hT : T∈Set.Icc (T-ρ) (T+ρ) := ⟨by linarith,by linarith⟩
  let R := fun v : ℝ => f v-f T-((v-T : ℝ) : ℂ)*g T
  have hd v (hv : v∈Set.Icc (T-ρ) (T+ρ)) :
      HasDerivAt R (g v-g T) v := by
    have hh := ((hf v hv).sub_const (f T)).sub
      (((hasDerivAt_id v).sub_const T).ofReal_comp.mul_const (g T))
    convert! hh using 1
    simp only [Complex.ofReal_one,one_mul]
  have hdB v (hv : v∈Set.Icc (T-ρ) (T+ρ)) : ‖g v-g T‖ ≤ M*ρ := by
    have hx : |v-T| ≤ ρ := abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v hv => (hg v hv).hasDerivWithinAt) hb
      (convex_Icc (T-ρ) (T+ρ)) hT hv
    simpa only [Real.norm_eq_abs] using
      hh.trans (mul_le_mul_of_nonneg_left hx hM)
  have hR i (hi : i∈S) : ‖R (t i)‖ ≤ M*ρ*|t i-T| := by
    have hti : t i∈Set.Icc (T-ρ) (T+ρ) := by
      have hh := abs_le.mp (ht i hi)
      constructor <;> linarith only [hh.1,hh.2]
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v hv => (hd v hv).hasDerivWithinAt) hdB
      (convex_Icc (T-ρ) (T+ρ)) hT hti
    simpa only [R,sub_self,Complex.ofReal_zero,zero_mul,sub_zero,
      Real.norm_eq_abs] using hh
  have hlin : (∑ i∈S,(c i : ℂ)*((t i-T : ℝ) : ℂ)*g T)=0 := by
    rw [← Finset.sum_mul]
    simp only [← Complex.ofReal_mul,← Complex.ofReal_sum,hcentre,
      Complex.ofReal_zero,zero_mul]
  have he : (∑ i∈S,(c i : ℂ)*(f T-f (t i))) =
      -(∑ i∈S,(c i : ℂ)*R (t i)) := by
    have each i : (c i : ℂ)*(f T-f (t i)) =
        -(c i : ℂ)*R (t i)-(c i : ℂ)*((t i-T : ℝ) : ℂ)*g T := by
      dsimp [R]
      ring
    simp_rw [each]
    rw [Finset.sum_sub_distrib,hlin,sub_zero]
    simp only [neg_mul,Finset.sum_neg_distrib]
  rw [he,norm_neg]
  calc
    _ ≤ ∑ i∈S,‖(c i : ℂ)*R (t i)‖ := norm_sum_le _ _
    _ ≤ ∑ i∈S,c i*(M*ρ*|t i-T|) := by
      apply Finset.sum_le_sum
      intro i his
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc i his)]
      exact mul_le_mul_of_nonneg_left (hR i his) (hc i his)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- The entire centered family costs the squared gap radius times its
total clipped mass. There is no separate cost per count or candidate. -/
theorem centred_transport_norm_quadratic {ι : Type*} (S : Finset ι)
    (c t : ι → ℝ) (f g h : ℝ → ℂ) {T ρ M : ℝ}
    (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hf : ∀ v∈Set.Icc (T-ρ) (T+ρ),HasDerivAt f (g v) v)
    (hg : ∀ v∈Set.Icc (T-ρ) (T+ρ),HasDerivAt g (h v) v)
    (hb : ∀ v∈Set.Icc (T-ρ) (T+ρ),‖h v‖ ≤ M)
    (hc : ∀ i∈S,0 ≤ c i) (ht : ∀ i∈S,|t i-T| ≤ ρ)
    (hcentre : (∑ i∈S,c i*(t i-T))=0) :
    ‖∑ i∈S,(c i : ℂ)*(f T-f (t i))‖ ≤ M*ρ^2*(∑ i∈S,c i) := by
  have hs : (∑ i∈S,c i*|t i-T|) ≤ ρ*(∑ i∈S,c i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i his
    exact (mul_le_mul_of_nonneg_left (ht i his) (hc i his)).trans_eq (mul_comm _ _)
  have hh := (centred_transport_norm S c t f g h hρ hM hf hg hb hc ht hcentre).trans
    (mul_le_mul_of_nonneg_left hs (mul_nonneg hM hρ))
  exact hh.trans_eq (by ring)

/-- Exact clipped coverage plus a proved centered total-log moment
replaces the joined transport by its quadratic price. All phase-sign,
derivative, owner-share and coverage obligations remain explicit. -/
theorem centred_owner_insertions_floor {ι : Type*} (S : Finset ι)
    (c t x' : ι → ℝ) (f g h : ℝ → ℂ) {N : ℕ} (hN : 32 ≤ N)
    {x τ T ρ M : ℝ} (hx : (3/8 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hf : ∀ v∈Set.Icc (T-ρ) (T+ρ),HasDerivAt f (g v) v)
    (hg : ∀ v∈Set.Icc (T-ρ) (T+ρ),HasDerivAt g (h v) v)
    (hb : ∀ v∈Set.Icc (T-ρ) (T+ρ),‖h v‖ ≤ M)
    (hc : ∀ i∈S,0 ≤ c i) (ht : ∀ i∈S,|t i-T| ≤ ρ)
    (hcentre : (∑ i∈S,c i*(t i-T))=0)
    (hcover : τ ≤ ∑ i∈S,c i)
    (hx' : ∀ i∈S,x ≤ x' i ∧ x' i ≤ 1)
    (hF : (f T).re ≤ 0) (hG : ∀ i∈S,(f (t i)).re ≤ 0) :
    -M*ρ*(∑ i∈S,c i*|t i-T|)-
        (2*exp (-(N : ℝ)/25))*(∑ i∈S,c i*‖f (t i)‖) ≤
      ((ZetaRieszOwnerMaximal.ownerWeight N x : ℂ)*(τ : ℂ)*f T-
        ∑ i∈S,(c i : ℂ)*(ZetaRieszOwnerMaximal.ownerWeight N (x' i) : ℂ)*f (t i)).re := by
  have hj := joined_owner_insertions_floor S c x' (f T) (fun i => f (t i))
    hN (τ := τ) hx hc hx' hx1 hF hG
  rw [max_eq_right (sub_nonpos.mpr hcover),neg_zero,zero_mul,zero_sub] at hj
  have hcst := centred_transport_norm S c t f g h hρ hM hf hg hb hc ht hcentre
  linarith only [hj,hcst]

/-- A finite family of ACTUAL inserted labels has this joined floor.
Membership, fractional capacity and source-scale transport still need
proof at a whole-population application; no mask is completed here. -/
theorem literal_insertions_floor {ι : Type*} (S : Finset ι)
    (β : ι → ℝ) (p' r : ι → ℕ) {p q b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hb : Squarefree b)
    (hc : 2 ≤ b.primeFactors.card) (hqb : ¬q ∣ b) (hpqb : ¬p ∣ q*b)
    {L : ℝ} (hi : InnerHinge L p q b)
    (hdata : ∀ i∈S,(p' i).Prime ∧ (r i).Prime ∧ ¬r i ∣ b ∧
      ¬q ∣ r i*b ∧ ¬p' i ∣ q*(r i*b) ∧
      log (q*(r i*b) : ℕ) ≤ L ∧
      log (r i*b : ℕ) ≤ log (p' i*(q*(r i*b)) : ℕ)-L ∧
      0 ≤ log (p' i*(r i*b) : ℕ)-L ∧
      log (p' i*(r i*b) : ℕ)-L ≤ log b.minFac)
    (A : Finset ℕ) (N : ℕ) (y : ℝ)
    (hnegative : ((μ b : ℂ)*phaseWeight A L N y (q*b) p).re ≤ 0) :
    let c := fun i => β i*min (log (p' i*(r i*b) : ℕ)-L) (log (r i))
    let F := (μ b : ℂ)*phaseWeight A L N y (q*b) p
    let G := fun i => (μ b : ℂ)*phaseWeight A L N y (q*(r i*b)) (p' i);
    -max ((log (p*b : ℕ)-L)-∑ i∈S,c i) 0*‖F‖-
      ‖∑ i∈S,(c i : ℂ)*(F-G i)‖ ≤
        (residualCoefficient A L N (p*(q*b))*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b))+
          ∑ i∈S,(β i : ℂ)*(residualCoefficient A L N (p' i*(q*(r i*b)))*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p' i*(q*(r i*b))))).re := by
  dsimp only
  have h := joined_insertions_floor S
    (fun i => β i*min (log (p' i*(r i*b) : ℕ)-L) (log (r i)))
    ((μ b : ℂ)*phaseWeight A L N y (q*b) p)
    (fun i => (μ b : ℂ)*phaseWeight A L N y (q*(r i*b)) (p' i))
    (τ := log (p*b : ℕ)-L) hnegative
  convert h using 1
  rw [literal_inner_atom hp hq hb hc hqb hpqb hi]
  have he : (∑ i∈S,(β i : ℂ)*(residualCoefficient A L N (p' i*(q*(r i*b)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p' i*(q*(r i*b))))) =
      -(∑ i∈S,((β i*min (log (p' i*(r i*b) : ℕ)-L) (log (r i)) : ℝ) : ℂ)*
        ((μ b : ℂ)*phaseWeight A L N y (q*(r i*b)) (p' i))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i his
    obtain ⟨hpi,hri,hrb,hqr,hpqr,hsat,hfull,hD,hhead⟩ := hdata i his
    rw [literal_insert_clipped hpi hq hri hb hc hrb hqr hpqr hsat hfull hD hhead]
    push_cast
    ring
  rw [he]
  congr 1
  push_cast
  ring

end RiemannGaussian.ZetaRieszClippedInsertionFloor
