/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLargeOrderCore

/-!
# Small-prime cancellation inside the central signed sum

Extract an actual cofactor prime before the arithmetic mean. Its Möbius
sign replaces the prime hinge by its exact difference under multiplication.
The resulting energy is bounded by twice the smaller prime logarithm,
independently of the Riesz length, order, height and all finite masks.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCentralPrimeDifference
open Real ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy
  ZetaRieszQuadraticPrimeEnergy ZetaRieszJointAllocation

/-- The two prime differences commute, before any absolute value. -/
def pulse (L : ℝ) (p r d : ℕ) : ℝ := hinge L r d-hinge (L-log p) r d

private theorem hinge_cap (L : ℝ) {p : ℕ} (_hp : 1 ≤ p) (d : ℕ) :
    hinge L p d = min (log p) (max 0 (L-log d)) := by
  have hp0 : 0 ≤ log p := log_natCast_nonneg p
  unfold hinge
  by_cases h : L-log d ≤ 0
  · rw [max_eq_left h,max_eq_left (by linarith),min_eq_right hp0]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ L-log d)]
    by_cases h' : log p ≤ L-log d
    · rw [max_eq_right (by linarith),min_eq_left h']
      ring
    · rw [max_eq_left (by linarith),min_eq_right (by linarith)]
      ring

/-- Exact prime insertion in the actual Riesz response, including both
cutoffs. No saturation, density or phase assumption enters. -/
theorem divisor_pulse {r n : ℕ} (hr : r.Prime) (hrn : ¬r ∣ n)
    (L : ℝ) (p : ℕ) :
    divisorResponse (hinge L p) (r*n) = divisorResponse (pulse L p r) n := by
  rw [divisor_prime_mul hr hrn]
  apply Finset.sum_congr rfl
  intro d hd
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  simp only [pulse,hinge,Nat.cast_mul,log_mul hr0 hd0]
  have h1 : L-log r-log d=L-(log r+log d) := by ring
  have h2 : L-log p-log r-log d=L-log p-(log r+log d) := by ring
  rw [h1,h2]
  ring

private theorem hinge_delta (L : ℝ) {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) :
    0 ≤ hinge L p k-hinge L p (k+1) ∧
      hinge L p k-hinge L p (k+1) ≤ log (k+1 : ℕ)-log k := by
  rw [hinge_cap L hp,hinge_cap L hp]
  have hl : log k ≤ log (k+1 : ℕ) := log_le_log (by exact_mod_cast hk)
    (by exact_mod_cast Nat.le_succ k)
  have hc : min (log p) (max 0 (L-log (k+1 : ℕ))) ≤
      min (log p) (max 0 (L-log k)) := min_le_min_left _ (max_le_max_left _ (by linarith))
  refine ⟨sub_nonneg.mpr hc,?_⟩
  by_cases h0 : L-log (k+1 : ℕ) ≤ 0
  · rw [max_eq_left h0,min_eq_right (log_natCast_nonneg p)]
    have hm := min_le_right (log p) (max 0 (L-log k))
    by_cases h1 : L-log k ≤ 0
    · rw [max_eq_left h1,min_eq_right (log_natCast_nonneg p)]
      linarith
    · rw [max_eq_right (by linarith)] at hm ⊢
      linarith
  · rw [max_eq_right (by linarith : 0 ≤ L-log (k+1 : ℕ)),
      max_eq_right (by linarith : 0 ≤ L-log k)]
    rcases le_total (log p) (L-log (k+1 : ℕ)) with h | h
    · rw [min_eq_left h,min_eq_left (by linarith)]
      linarith
    · rw [min_eq_right h]
      linarith [min_le_right (log p) (L-log k)]

/-- Every literal prime hinge has energy at most its prime logarithm. -/
theorem hinge_energy (L : ℝ) {p : ℕ} (hp : 1 ≤ p) (X : ℕ) :
    rawEnergy X (hinge L p) ≤ log p := by
  have hstep (k : ℕ) (hk : k ∈ Finset.Ico 1 X) :
      (k : ℝ)*(hinge L p k-hinge L p (k+1))^2 ≤
        hinge L p k-hinge L p (k+1) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    have hd := hinge_delta L hp (Finset.mem_Ico.mp hk).1
    have hl := log_le_sub_one_of_pos (show (0 : ℝ) < (k+1 : ℕ)/k by positivity)
    rw [log_div (by positivity) hk0.ne'] at hl
    have he : (k : ℝ)*((k+1 : ℕ)/k-1)=1 := by push_cast; field_simp; ring
    have hkl : (k : ℝ)*(log (k+1 : ℕ)-log k) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hl hk0.le).trans_eq he
    have hkd := (mul_le_mul_of_nonneg_left hd.2 hk0.le).trans hkl
    nlinarith [mul_le_mul_of_nonneg_right hkd hd.1]
  by_cases hX : 1 ≤ X
  · have htel : (∑ k ∈ Finset.Ico 1 X, (hinge L p k-hinge L p (k+1))) =
        hinge L p 1-hinge L p X := by
      calc
        _ = -(∑ k ∈ Finset.Ico 1 X, (hinge L p (k+1)-hinge L p k)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
        _ = _ := by rw [Finset.sum_Ico_sub _ hX]; ring
    have hbound := (Finset.sum_le_sum hstep).trans_eq htel
    have hnonneg : 0 ≤ hinge L p X := by
      rw [hinge_cap L hp]
      exact le_min (log_natCast_nonneg p) (le_max_left _ _)
    have htop : hinge L p 1 ≤ log p := by rw [hinge_cap L hp]; exact min_le_left _ _
    exact hbound.trans (by linarith)
  · have hz : X=0 := by omega
    simp only [hz,rawEnergy,Finset.Ico_eq_empty_of_le (by omega : 0 ≤ 1),Finset.sum_empty]
    exact log_natCast_nonneg p

/-- The two cutoff slopes have opposite signs. Their nonnegative overlap
is subtracted exactly, rather than charging two squared norms. -/
theorem pulse_energy_eq (X : ℕ) (L : ℝ) (p r : ℕ) :
    rawEnergy X (pulse L p r) = rawEnergy X (hinge L r)+
      rawEnergy X (hinge (L-log p) r)-2*
        ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*(hinge L r k-hinge L r (k+1))*
          (hinge (L-log p) r k-hinge (L-log p) r (k+1)) := by
  simp only [rawEnergy,pulse,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Uniform arithmetic saving: after the exact small-prime difference,
the cutoff energy costs at most 2 log r, with no large log p or L factor. -/
theorem pulse_energy_le (X : ℕ) (L : ℝ) (p : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    rawEnergy X (pulse L p r) ≤ 2*log r := by
  rw [pulse_energy_eq]
  have hcross : 0 ≤ ∑ k ∈ Finset.Ico 1 X,
      (k : ℝ)*(hinge L r k-hinge L r (k+1))*
        (hinge (L-log p) r k-hinge (L-log p) r (k+1)) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k)
      (hinge_delta L hr (Finset.mem_Ico.mp hk).1).1)
      (hinge_delta (L-log p) hr (Finset.mem_Ico.mp hk).1).1
  linarith [hinge_energy L hr X,hinge_energy (L-log p) hr X]


private theorem raw_nonneg (X : ℕ) (f : ℕ → ℝ) : 0 ≤ rawEnergy X f :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _))

private theorem exists_raw_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S : Finset ℕ) (f : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, divisorResponse f n^2) ≤ E*X*rawEnergy X f := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_divisor_profile_mean
  refine ⟨E,hE,fun X S f hS hSF => ?_⟩
  let g := fun d => if d ≤ X then f d-f X else 0
  have he n (hn : n ∈ S) :
      (∑ d ∈ Finset.Icc 1 X, g d*(if d ∣ n then (μ d : ℝ) else 0)) =
        divisorResponse f n := by
    have hx := Finset.mem_Ioc.mp (hS hn)
    have hdiv : (Finset.Icc 1 X).filter (fun d => d ∣ n)=n.divisors := by
      ext d
      simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
      constructor
      · rintro ⟨_,hd⟩; exact ⟨hd,by omega⟩
      · rintro ⟨hd,_⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),(Nat.le_of_dvd (by omega) hd).trans hx.2⟩,hd⟩
    simp only [mul_ite,mul_zero,← Finset.sum_filter,hdiv]
    have hg d (hd : d ∈ n.divisors) : g d=f d-f X :=
      if_pos ((Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hx.2)
    have hm : (∑ d ∈ n.divisors, (μ d : ℝ))=0 := by
      exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero (by omega : n ≠ 1)
    simp_rw [Finset.sum_congr rfl (fun d hd => congrArg (fun z : ℝ => z*(μ d : ℝ)) (hg d hd))]
    simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,hm,mul_zero,sub_zero,divisorResponse]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have heg : (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*(g k-g (k+1))^2)=rawEnergy X f := by
    have hzero : g X=0 := by simp [g]
    have hsucc : g (X+1)=0 := by simp [g]
    symm
    calc
      _ = ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*(g k-g (k+1))^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hx := Finset.mem_Ico.mp hk
        simp only [g,if_pos (by omega : k ≤ X),if_pos (by omega : k+1 ≤ X)]
        ring
      _ = _ := by
        apply Finset.sum_subset (fun k hk => Finset.mem_Icc.mpr
          ⟨(Finset.mem_Ico.mp hk).1,(Finset.mem_Ico.mp hk).2.le⟩)
        intro k hk hnot
        have hkX : k=X := by simp only [Finset.mem_Icc,Finset.mem_Ico] at hk hnot; omega
        simp [hkX,hzero,hsucc]
  have hb := hmean X X S g hS hSF (by simp [g])
  rw [Finset.sum_congr rfl (fun n hn => congrArg (fun z : ℝ => z^2) (he n hn)),heg] at hb
  exact hb

/-- Joint cost AFTER exact prime-difference cancellation. All prime and
count cross terms stay inside the common coordinate energies. -/
def differenceCost (E : ℝ) (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ I, sqrt ((∑ n ∈ S, (rotate P O a (W n))^2)*E*X*
    rawEnergy X (fun d => rotate P O a (fun p => F p d)))

private theorem raw_joint_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S I P : Finset ℕ)
      (O W F : ℕ → ℕ → ℝ), Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n) →
      |∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n| ≤
        differenceCost E X S I P O W F := by
  obtain ⟨E,hE,hmean⟩ := exists_raw_mean
  refine ⟨E,hE,fun X S I P O W F hO hS hSF => ?_⟩
  have hrot a n : divisorResponse (fun d => rotate P O a (fun p => F p d)) n =
      rotate P O a (fun p => divisorResponse (F p) n) := by
    simp only [divisorResponse,rotate,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have he : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      ∑ a ∈ I, ∑ n ∈ S, rotate P O a (W n)*
        divisorResponse (fun d => rotate P O a (fun p => F p d)) n := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    simp_rw [hrot]
    exact (coordinate_pairing I P O hO _ _).symm
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  let f := fun d => rotate P O a (fun p => F p d)
  have h := (Finset.sum_mul_sq_le_sq_mul_sq S (fun n => rotate P O a (W n))
    (divisorResponse f)).trans (mul_le_mul_of_nonneg_left (hmean X S f hS hSF)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_abs,sq_sqrt (mul_nonneg (by positivity) (raw_nonneg _ _))]
  simpa only [mul_assoc] using h

/-- BOTH signed bounds on the actual selected small-prime fibre. All
cofactor counts, allocation orders, phases and arbitrary row masks are
retained. The new arithmetic mean has no unproved cancellation premise. -/
theorem exists_prime_difference_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (r X N : ℕ) (A S I P : Finset ℕ)
      (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ),
      r.Prime → Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ ¬r ∣ n) → (∀ n ∈ S, Q n ⊆ P) →
      (∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ r*n) →
      let W := fun n p => if p ∈ Q n then scale*primeWeight A L y N (r*n) p else 0;
      let J := scale*(∑ n ∈ S, ∑ p ∈ Q n,
        residualCoefficient A L N (p*(r*n))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(r*n))).re;
      let C := differenceCost E X S I P O W (fun p => pulse L p r);
      -C ≤ J ∧ J ≤ C := by
  obtain ⟨E,hE,hbound⟩ := raw_joint_bounds
  refine ⟨E,hE,fun r X N A S I P Q O L y scale hr hO hS hSF hQ hp => ?_⟩
  let W := fun n p => if p ∈ Q n then scale*primeWeight A L y N (r*n) p else 0
  have hb := hbound X S I P O W (fun p => pulse L p r) hO hS (fun n hn => (hSF n hn).1)
  have he : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (pulse L p r) n) =
      scale*(∑ n ∈ S, ∑ p ∈ Q n,
        residualCoefficient A L N (p*(r*n))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(r*n))).re := by
    simp only [Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hs := Nat.squarefree_mul_iff.mpr
      ⟨hr.coprime_iff_not_dvd.mpr (hSF n hn).2,hr.squarefree,(hSF n hn).1⟩
    have hcard : 2 ≤ (r*n).primeFactors.card := by
      rw [Nat.primeFactors_mul hr.ne_zero (hSF n hn).1.ne_zero,hr.primeFactors,
        Finset.singleton_union,Finset.card_insert_of_notMem
          (fun h => (hSF n hn).2 (Nat.dvd_of_mem_primeFactors h))]
      have hpos := Nat.nonempty_primeFactors.mpr (by have := Finset.mem_Ioc.mp (hS hn); omega : 2 ≤ n)
      have hc := Finset.card_pos.mpr hpos
      omega
    have hfilter : P.filter (fun p => p ∈ Q n)=Q n := by
      rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr (hQ n hn)]
    simp only [W,ite_mul,zero_mul,← Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro p hpn
    rw [atom_eq A L y N hs hcard (hp n hn p hpn).1 (hp n hn p hpn).2,
      divisor_pulse hr (hSF n hn).2]
    ring
  rw [he] at hb
  exact abs_le.mp hb


open ZetaRieszPrimeEndpoint ZetaRieszOwnedCells

/-- The extracted prime is fixed by the actual label, without any arbitrary
assignment or averaging over incidences. -/
def smallFactor (m : ℕ) : ℕ := (ownerCofactor m).minFac

/-- The population left AFTER both genuine prime differences. -/
def baseCofactor (m : ℕ) : ℕ := ownerCofactor m/smallFactor m

private theorem base_data {m : ℕ} (hm : Squarefree m) (hc : 3 ≤ m.primeFactors.card) :
    (smallFactor m).Prime ∧ smallFactor m*baseCofactor m=ownerCofactor m ∧
      Squarefree (baseCofactor m) ∧ 1 < baseCofactor m ∧
      ¬smallFactor m ∣ baseCofactor m := by
  have hd := owner_data hm hc
  have hn1 : ownerCofactor m ≠ 1 := by intro h; simp [h] at hd
  have hnp : ¬(ownerCofactor m).Prime := by
    intro h
    have hcount := hd.2.2.2.1
    simp [h.primeFactors] at hcount
  have hr : (smallFactor m).Prime := Nat.minFac_prime hn1
  have he : smallFactor m*baseCofactor m=ownerCofactor m :=
    Nat.mul_div_cancel' (Nat.minFac_dvd _)
  have hs : Squarefree (smallFactor m*baseCofactor m) := by rw [he]; exact hd.2.2.1
  have hmin := Nat.minFac_le_div (Nat.pos_of_ne_zero hd.2.2.1.ne_zero) hnp
  exact ⟨hr,he,hs.of_mul_right,lt_of_lt_of_le hr.one_lt hmin,
    hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)⟩

/-- The original atom, with its full phase and allocation, now has the
small-prime cancellation INSIDE its divisor response. -/
theorem atom_pulse {m : ℕ} (hm : Squarefree m) (hc : 3 ≤ m.primeFactors.card)
    (A : Finset ℕ) (L y : ℝ) (N : ℕ) :
    (residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m).re =
      primeWeight A L y N (ownerCofactor m) (largestPrime m)*
        divisorResponse (pulse L (largestPrime m) (smallFactor m)) (baseCofactor m) := by
  have hd := owner_data hm hc
  have hb := base_data hm hc
  have hs : Squarefree (largestPrime m*ownerCofactor m) := by rw [hd.2.1]; exact hm
  have hp : ¬largestPrime m ∣ ownerCofactor m :=
    hd.1.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have ha := atom_eq A L y N hd.2.2.1 hd.2.2.2.1 hd.1 hp
  rw [hd.2.1] at ha
  rw [ha,← hb.2.1,divisor_pulse hb.1 hb.2.2.2.2]

/-- Whole-support cost with all counts, least-prime choices and owner
incidences coupled in ONE common finite coordinate system. Labels merely
index the existing profiles; equal profiles may share coordinates. -/
def wholeDifferenceCost (E : ℝ) (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ) : ℝ :=
  let S := B.image baseCofactor;
  differenceCost E (S.sup id) S I B O
    (fun n m => if baseCofactor m=n then
      scale*primeWeight A L y N (ownerCofactor m) (largestPrime m) else 0)
    (fun m => pulse L (largestPrime m) (smallFactor m))

/-- BOTH bounds for the actual finite carrier, including ALL counts >=3.
No covering, prime-density, zero or signed-cancellation premise remains.
The common cost retains cross terms across different counts and small primes;
only its eventual total size remains to be bounded. -/
theorem exists_whole_difference_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
      (N : ℕ) (L y scale : ℝ),
      (∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) → Coordinates I B O →
      let J := scale*(∑ m ∈ B,
        residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      let C := wholeDifferenceCost E A B I O N L y scale;
      -C ≤ J ∧ J ≤ C := by
  obtain ⟨E,hE,hbound⟩ := raw_joint_bounds
  refine ⟨E,hE,fun A B I O N L y scale hB hO => ?_⟩
  let S := B.image baseCofactor
  let W := fun n m => if baseCofactor m=n then
      scale*primeWeight A L y N (ownerCofactor m) (largestPrime m) else 0
  let F := fun m => pulse L (largestPrime m) (smallFactor m)
  have hS : S ⊆ Finset.Ioc 1 (S.sup id) := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ioc.mpr ⟨(base_data (hB m hm).1 (hB m hm).2).2.2.2.1,
      Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨m,hm,rfl⟩)⟩
  have hSF : ∀ n ∈ S, Squarefree n := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact (base_data (hB m hm).1 (hB m hm).2).2.2.1
  have hb := hbound (S.sup id) S I B O W F hO hS hSF
  have he : (∑ n ∈ S, ∑ m ∈ B, W n m*divisorResponse (F m) n) =
      scale*(∑ m ∈ B,
        residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m).re := by
    rw [Finset.sum_comm]
    simp only [Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmem : baseCofactor m ∈ S := Finset.mem_image.mpr ⟨m,hm,rfl⟩
    simp only [W,ite_mul,zero_mul,Finset.sum_ite_eq,hmem,if_true,F]
    rw [atom_pulse (hB m hm).1 (hB m hm).2]
    ring
  rw [he] at hb
  exact abs_le.mp hb

/-- The actual least-prime energy cap is strict whenever its square is
below the owner prime. This covers a geometry automatically, at every order. -/
theorem pulse_energy_lt_owner (X : ℕ) (L : ℝ) {p r : ℕ}
    (hr : r.Prime) (hsmall : r^2 < p) : rawEnergy X (pulse L p r) < log p := by
  apply (pulse_energy_le X L p hr.one_lt.le).trans_lt
  have hr0 : 0 < r := hr.pos
  have h := log_lt_log (show (0 : ℝ) < (r^2 : ℕ) by positivity)
    (show ((r^2 : ℕ) : ℝ) < p by exact_mod_cast hsmall)
  simpa only [Nat.cast_pow,log_pow,Nat.cast_ofNat] using h


/-- The exact least-prime choice makes the saving automatic in the count:
the residual energy is at most twice the MEAN cofactor prime logarithm.
No count classes are separated in the signed carrier. -/
theorem pulse_energy_count {m : ℕ} (hm : Squarefree m) (hc : 3 ≤ m.primeFactors.card)
    (X : ℕ) (L : ℝ) :
    ((ownerCofactor m).primeFactors.card : ℝ)*
        rawEnergy X (pulse L (largestPrime m) (smallFactor m)) ≤ 2*log (ownerCofactor m) := by
  have hb := base_data hm hc
  have hd := owner_data hm hc
  have hlog := Finset.sum_le_sum (fun q (hq : q ∈ (ownerCofactor m).primeFactors) =>
    log_le_log (show (0 : ℝ) < smallFactor m by exact_mod_cast hb.1.pos)
      (show (smallFactor m : ℝ) ≤ q by
        exact_mod_cast (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le
          (Nat.dvd_of_mem_primeFactors hq))))
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hd.2.2.1,
    Finset.sum_const,nsmul_eq_mul] at hlog
  have hp := mul_le_mul_of_nonneg_left
    (pulse_energy_le X L (largestPrime m) hb.1.one_lt.le)
    (Nat.cast_nonneg (ownerCofactor m).primeFactors.card)
  nlinarith only [hlog,hp]

open ZetaRieszParityPacket ZetaRieszCubicPrimeEnergy

/-- The new joint small-prime estimate is applied to the surviving CENTRAL
range and intersected with both existing signed enclosures. The paid outer
strips are added only once. This can never weaken either whole-core bound;
the total central cost remains an explicit unevaluated arithmetic target. -/
theorem exists_central_joint_bounds :
    ∃ E D C : ℝ, 0 < E ∧ 0 < D ∧ 0 ≤ C ∧
      ∀ (u y : ℝ) (N K : ℕ) (I V : Finset ℕ) (O T : ℕ → ℕ → ℝ),
      0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      let B := LogarithmicDeviation.deviationBand ((coreBand u N K).filter Squarefree)
        (1971/1000) (2029/1000) N;
      Coordinates I (ownerPrimes B) O → Coordinates V B T →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
      let L := SquarefreeVaughanLogSource.length u N;
      let H₂ := wholeCenter A B I O N L y (u^(N+1));
      let C₂ := wholeQuadraticCost E A B I O N L y (u^(N+1));
      let H₃ := wholeCubicCenter A B I O N L y (u^(N+1));
      let C₃ := wholeCubicCost E A B I O N L y (u^(N+1));
      let D₀ := wholeDifferenceCost D A B V T N L y (u^(N+1));
      let J := u^(N+1)*(coreResponse u y N K).re;
      max (max (H₂-C₂) (H₃-C₃)) (-D₀)-ZetaRieszLargeOrderCore.rate^N*C ≤ J ∧
        J ≤ min (min (H₂+C₂) (H₃+C₃)) D₀+ZetaRieszLargeOrderCore.rate^N*C := by
  obtain ⟨E,hE,hcube⟩ := exists_whole_cubic_bounds
  obtain ⟨D,hD,hdiff⟩ := exists_whole_difference_bounds
  obtain ⟨C,hC,hgeo⟩ := ZetaRieszLargeOrderCore.exists_edge_bound
  refine ⟨E,D,C,hE,hD,hC,fun u y N K I V O T hu hU hO hT => ?_⟩
  let S := (coreBand u N K).filter Squarefree
  let B := LogarithmicDeviation.deviationBand S (1971/1000) (2029/1000) N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  have hB : ∀ n ∈ B, Squarefree n ∧ 3 ≤ n.primeFactors.card := by
    intro n hn
    have hs := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
    exact ⟨hs.2,core_count hs.1⟩
  have hq := hcube A B I O N L y (u^(N+1)) hB hO
  have hd := hdiff A B V T N L y (u^(N+1)) hB hT
  have hg := hgeo N S (residualCoefficient A L N)
    (fun n _ => norm_residualCoefficient_le A (SquarefreeVaughanLogSource.length_pos u N) N n)
    y u hu hU
  have he := (Complex.abs_re_le_norm _).trans hg
  dsimp only [S,A,L] at he
  rw [← core_eq_squarefree] at he
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_re,mul_sub] at he
  have hel := (abs_le.mp he).1
  have heu := (abs_le.mp he).2
  have hlo := max_le hq.1 hd.1
  have hhi := le_min hq.2.1 hd.2
  dsimp only [A,B,S,L] at hlo hhi
  dsimp only
  constructor
  · linarith only [hlo,hel]
  · linarith only [hhi,heu]


/-- Extracting a second genuine cofactor prime keeps all four signed
cutoffs together. Its smaller arithmetic population is used below. -/
def secondPulse (L : ℝ) (p r s d : ℕ) : ℝ :=
  pulse L p r d-pulse (L-log s) p r d

private theorem hinge_pair_delta {L M : ℝ} {r k : ℕ}
    (hr : 1 ≤ r) (hk : 1 ≤ k) (hsep : M+log r ≤ L) :
    (hinge L r k-hinge L r (k+1))+(hinge M r k-hinge M r (k+1)) ≤
      log (k+1 : ℕ)-log k := by
  have hl : log k ≤ log (k+1 : ℕ) := log_le_log (by exact_mod_cast hk)
    (by exact_mod_cast Nat.le_succ k)
  by_cases hhi : log (k+1 : ℕ) ≤ L-log r
  · have he (d : ℕ) (hd : log d ≤ L-log r) : hinge L r d=log r := by
      rw [hinge_cap L hr,min_eq_left]
      exact le_trans (by linarith : log r ≤ L-log d) (le_max_right _ _)
    rw [he k (hl.trans hhi),he (k+1) hhi,sub_self,zero_add]
    exact (hinge_delta M hr hk).2
  by_cases hlo : M ≤ log k
  · have he (d : ℕ) (hd : M ≤ log d) : hinge M r d=0 := by
      rw [hinge_cap M hr,max_eq_left (by linarith),min_eq_right (log_natCast_nonneg r)]
    rw [he k hlo,he (k+1) (hlo.trans hl),sub_self,add_zero]
    exact (hinge_delta L hr hk).2
  have hupper : hinge L r k ≤ log r := by rw [hinge_cap L hr]; exact min_le_left _ _
  have hlower : L-log (k+1 : ℕ) ≤ hinge L r (k+1) := by
    rw [hinge_cap L hr]
    exact le_min (by linarith) (le_max_right _ _)
  have hM : hinge M r k ≤ M-log k := by
    rw [hinge_cap M hr,max_eq_right (by linarith)]
    exact min_le_right _ _
  have hM0 : 0 ≤ hinge M r (k+1) := by
    rw [hinge_cap M hr]
    exact le_min (log_natCast_nonneg r) (le_max_left _ _)
  linarith

private theorem hinge_variation (L : ℝ) {r : ℕ} (hr : 1 ≤ r) (X : ℕ) :
    (∑ k ∈ Finset.Ico 1 X, (hinge L r k-hinge L r (k+1))) ≤ log r := by
  by_cases hX : 1 ≤ X
  · have he : (∑ k ∈ Finset.Ico 1 X, (hinge L r k-hinge L r (k+1))) =
        hinge L r 1-hinge L r X := by
      calc
        _ = -(∑ k ∈ Finset.Ico 1 X, (hinge L r (k+1)-hinge L r k)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
        _ = _ := by rw [Finset.sum_Ico_sub _ hX]; ring
    rw [he,hinge_cap L hr,hinge_cap L hr]
    have h0 : 0 ≤ min (log r) (max 0 (L-log X)) :=
      le_min (log_natCast_nonneg r) (le_max_left _ _)
    linarith [min_le_left (log r) (max 0 (L-log (1 : ℕ)))]
  · have he : Finset.Ico 1 X=∅ := Finset.Ico_eq_empty_of_le (by omega)
    simpa only [he,Finset.sum_empty] using log_natCast_nonneg r

/-- A second small-prime extraction costs at most 4 log r when the owner
is at least r*s. This is uniform in the length, order and all literal masks.
The proof keeps opposite cutoff slopes coupled before squaring. -/
theorem secondPulse_energy_le (X : ℕ) (L : ℝ) {p r s : ℕ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hp : r*s ≤ p) :
    rawEnergy X (secondPulse L p r s) ≤ 4*log r := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hlog : log r+log s ≤ log p := by
    have h := log_le_log (show (0 : ℝ) < (r*s : ℕ) by positivity)
      (show ((r*s : ℕ) : ℝ) ≤ p by exact_mod_cast hp)
    simpa only [Nat.cast_mul,log_mul hr0 hs0] using h
  have hstep k (hk : k ∈ Finset.Ico 1 X) :
      (k : ℝ)*(secondPulse L p r s k-secondPulse L p r s (k+1))^2 ≤
        (hinge L r k-hinge L r (k+1))+
        (hinge (L-log p) r k-hinge (L-log p) r (k+1))+
        (hinge (L-log s) r k-hinge (L-log s) r (k+1))+
        (hinge (L-log s-log p) r k-hinge (L-log s-log p) r (k+1)) := by
    have hkN := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hkN
    let a := hinge L r k-hinge L r (k+1)
    let b := hinge (L-log p) r k-hinge (L-log p) r (k+1)
    let c := hinge (L-log s) r k-hinge (L-log s) r (k+1)
    let d := hinge (L-log s-log p) r k-hinge (L-log s-log p) r (k+1)
    have ha : 0 ≤ a := (hinge_delta L hr hkN).1
    have hb : 0 ≤ b := (hinge_delta (L-log p) hr hkN).1
    have hc : 0 ≤ c := (hinge_delta (L-log s) hr hkN).1
    have hd : 0 ≤ d := (hinge_delta (L-log s-log p) hr hkN).1
    have hpos : a+d ≤ log (k+1 : ℕ)-log k :=
      hinge_pair_delta hr hkN (by linarith [log_natCast_nonneg s])
    have hneg : c+b ≤ log (k+1 : ℕ)-log k := hinge_pair_delta hr hkN (by linarith)
    have hlogstep := log_le_sub_one_of_pos (show (0 : ℝ) < (k+1 : ℕ)/k by positivity)
    rw [log_div (by positivity) hk0.ne'] at hlogstep
    have he : (k : ℝ)*((k+1 : ℕ)/k-1)=1 := by push_cast; field_simp; ring
    have hkl : (k : ℝ)*(log (k+1 : ℕ)-log k) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hlogstep hk0.le).trans_eq he
    have hkp := (mul_le_mul_of_nonneg_left hpos hk0.le).trans hkl
    have hkn := (mul_le_mul_of_nonneg_left hneg hk0.le).trans hkl
    have hpp := mul_le_mul_of_nonneg_right hkp (add_nonneg ha hd)
    have hnn := mul_le_mul_of_nonneg_right hkn (add_nonneg hc hb)
    have hcross := mul_nonneg hk0.le (mul_nonneg (add_nonneg ha hd) (add_nonneg hb hc))
    have hh : secondPulse L p r s k-secondPulse L p r s (k+1)=(a-b)-(c-d) := by
      dsimp [secondPulse,pulse,a,b,c,d]
      ring
    rw [hh]
    change (k : ℝ)*((a-b)-(c-d))^2 ≤ a+b+c+d
    nlinarith only [hpp,hnn,hcross]
  have h := Finset.sum_le_sum hstep
  simp only [Finset.sum_add_distrib] at h
  have h0 := hinge_variation L hr X
  have h1 := hinge_variation (L-log p) hr X
  have h2 := hinge_variation (L-log s) hr X
  have h3 := hinge_variation (L-log s-log p) hr X
  exact h.trans (by linarith only [h0,h1,h2,h3])


/-- Both genuine Möbius insertions are evaluated before any norm or
prime/count split. Every Riesz cutoff remains exact. -/
theorem divisor_secondPulse {r s n : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrn : ¬r ∣ s*n) (hsn : ¬s ∣ n) (L : ℝ) (p : ℕ) :
    divisorResponse (hinge L p) (r*(s*n)) = divisorResponse (secondPulse L p r s) n := by
  rw [divisor_pulse hr hrn,divisor_prime_mul hs hsn]
  apply Finset.sum_congr rfl
  intro d hd
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne_zero
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have he (M : ℝ) : hinge M r (s*d)=hinge (M-log s) r d := by
    simp only [hinge,Nat.cast_mul,log_mul hs0 hd0]
    ring_nf
  simp only [pulse,secondPulse,he]
  have he' : L-log p-log s=L-log s-log p := by ring
  rw [he']

/-- The smaller population pays an explicit factor 2/s in the squared
mean allowance, with the SAME arithmetic constant and signed weights. -/
theorem second_allowance_contraction {E W : ℝ} (hE : 0 ≤ E) (hW : 0 ≤ W)
    (X : ℕ) (L : ℝ) {p r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hp : r*s ≤ p) :
    W*E*X*rawEnergy X (secondPulse L p r s) ≤
      (2/(s : ℝ))*(W*E*(s*X)*(2*log r)) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  calc
    _ ≤ W*E*X*(4*log r) :=
      mul_le_mul_of_nonneg_left (secondPulse_energy_le X L hr hs hp) (by positivity)
    _ = _ := by field_simp; ring

/-- The gain is strict for every second prime s>=3 when the old explicit
squared allowance is nonzero. No asymptotic or phase premise is used. -/
theorem second_allowance_strict {E W : ℝ} (hE : 0 < E) (hW : 0 < W)
    {X : ℕ} (hX : 0 < X) (L : ℝ) {p r s : ℕ}
    (hr : r.Prime) (hs : 3 ≤ s) (hp : r*s ≤ p) :
    W*E*X*rawEnergy X (secondPulse L p r s) < W*E*(s*X)*(2*log r) := by
  have hlog : 0 < log r := log_pos (by exact_mod_cast hr.one_lt)
  have hsR : (2 : ℝ) < s := by exact_mod_cast hs
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hfac : 2/(s : ℝ) < 1 := (div_lt_one (by linarith)).mpr hsR
  apply (second_allowance_contraction hE.le hW.le X L hr.one_lt.le (by omega) hp).trans_lt
  have hpos : 0 < W*E*(s*X)*(2*log r) := by positivity
  nlinarith only [mul_lt_mul_of_pos_right hfac hpos]

/-- The actual second-prime fibre has BOTH signed bounds with a common
coordinate energy. All counts, masks and full factorial/phase weights stay
coupled. The explicit 4 log r cap is separately proved above. -/
theorem exists_second_prime_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (r s X N : ℕ) (A S I P : Finset ℕ)
      (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ),
      r.Prime → s.Prime → Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree (r*(s*n))) → (∀ n ∈ S, Q n ⊆ P) →
      (∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ r*(s*n)) →
      let W := fun n p => if p ∈ Q n then scale*primeWeight A L y N (r*(s*n)) p else 0;
      let J := scale*(∑ n ∈ S, ∑ p ∈ Q n,
        residualCoefficient A L N (p*(r*(s*n)))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(r*(s*n)))).re;
      let C := differenceCost E X S I P O W (fun p => secondPulse L p r s);
      -C ≤ J ∧ J ≤ C := by
  obtain ⟨E,hE,hbound⟩ := raw_joint_bounds
  refine ⟨E,hE,fun r s X N A S I P Q O L y scale hr hs hO hS hSF hQ hp => ?_⟩
  let W := fun n p => if p ∈ Q n then scale*primeWeight A L y N (r*(s*n)) p else 0
  have hb := hbound X S I P O W (fun p => secondPulse L p r s) hO hS
    (fun n hn => (hSF n hn).of_mul_right.of_mul_right)
  have he : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (secondPulse L p r s) n) =
      scale*(∑ n ∈ S, ∑ p ∈ Q n,
        residualCoefficient A L N (p*(r*(s*n)))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(r*(s*n)))).re := by
    simp only [Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hrn := hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul (hSF n hn))
    have hsn := hs.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul (hSF n hn).of_mul_right)
    have hcard : 2 ≤ (r*(s*n)).primeFactors.card := by
      rw [Nat.primeFactors_mul hr.ne_zero (hSF n hn).of_mul_right.ne_zero,hr.primeFactors,
        Finset.singleton_union,Finset.card_insert_of_notMem
          (fun h => hrn (Nat.dvd_of_mem_primeFactors h))]
      have hpos := Nat.nonempty_primeFactors.mpr
        (show 2 ≤ s*n from (Nat.le_mul_of_pos_right s (by have := Finset.mem_Ioc.mp (hS hn); omega)).trans' hs.two_le)
      have hc := Finset.card_pos.mpr hpos
      omega
    have hfilter : P.filter (fun p => p ∈ Q n)=Q n := by
      rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr (hQ n hn)]
    simp only [W,ite_mul,zero_mul,← Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro p hpn
    rw [atom_eq A L y N (hSF n hn) hcard (hp n hn p hpn).1 (hp n hn p hpn).2,
      divisor_secondPulse hr hs hrn hsn]
    ring
  rw [he] at hb
  exact abs_le.mp hb


/-- Literal second-prime subpopulation. The quotient condition retains a
nontrivial squarefree mean row; all unselected labels remain in the rest. -/
def secondSector (B : Finset ℕ) (r s : ℕ) : Finset ℕ :=
  B.filter (fun m => r*s ∣ ownerCofactor m ∧
    1 < ownerCofactor m/(r*s) ∧ r*s ≤ largestPrime m)

/-- The exact smaller cofactor population, without interval completion. -/
def secondRows (B : Finset ℕ) (r s : ℕ) : Finset ℕ :=
  (cofactors B).image (fun n => n/(r*s))

/-- Joint cost for a selected second-prime sector. A common coordinate map
retains all owner-prime/count/weight cross terms on the smaller population. -/
def wholeSecondCost (E : ℝ) (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (r s N : ℕ) (L y scale : ℝ) : ℝ :=
  let S := secondRows B r s;
  differenceCost E (S.sup id) S I (ownerPrimes B) O
    (fun n p => if p ∈ ownerRows B (r*(s*n)) then
      scale*primeWeight A L y N (r*(s*n)) p else 0)
    (fun p => secondPulse L p r s)

/-- The second-prime bound applies directly to original labels; the
quotient reindexing is exact and largest-prime ownership forbids duplicates.
No hypothesis about cancellation, density or zero locations enters. -/
theorem exists_whole_second_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
      (r s N : ℕ) (L y scale : ℝ), r.Prime → s.Prime →
      (∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) →
      (∀ m ∈ B, r*s ∣ ownerCofactor m ∧ 1 < ownerCofactor m/(r*s)) →
      Coordinates I (ownerPrimes B) O →
      let J := scale*(∑ m ∈ B,
        residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      let C := wholeSecondCost E A B I O r s N L y scale;
      -C ≤ J ∧ J ≤ C := by
  obtain ⟨E,hE,hbound⟩ := exists_second_prime_bounds
  refine ⟨E,hE,fun A B I O r s N L y scale hr hs hB hdiv hO => ?_⟩
  have hd n (hn : n ∈ cofactors B) : r*s ∣ n ∧ 1 < n/(r*s) := by
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact hdiv m hm
  have he n (hn : n ∈ cofactors B) : r*(s*(n/(r*s)))=n := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_cancel' (hd n hn).1
  have hS : secondRows B r s ⊆ Finset.Ioc 1 ((secondRows B r s).sup id) := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ioc.mpr ⟨(hd m hm).2,Finset.le_sup (f := id)
      (Finset.mem_image.mpr ⟨m,hm,rfl⟩)⟩
  have hSF : ∀ n ∈ secondRows B r s, Squarefree (r*(s*n)) := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    rw [he m hm]
    exact (cofactors_data B hB hm).1
  have hQ : ∀ n ∈ secondRows B r s, ownerRows B (r*(s*n)) ⊆ ownerPrimes B := by
    intro n _
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hb := hbound r s ((secondRows B r s).sup id) N A (secondRows B r s) I
    (ownerPrimes B) (fun n => ownerRows B (r*(s*n))) O L y scale hr hs hO hS hSF hQ
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.1⟩)
  let f := fun m => residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m
  have hsum : (∑ n ∈ secondRows B r s, ∑ p ∈ ownerRows B (r*(s*n)), f (p*(r*(s*n)))) =
      ∑ m ∈ B, f m := by
    rw [secondRows,Finset.sum_image]
    · calc
        _ = ∑ n ∈ cofactors B, ∑ p ∈ ownerRows B n, f (n*p) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [he n hn]
          exact Finset.sum_congr rfl (fun p _ => congrArg f (Nat.mul_comm p n))
        _ = _ := by
          rw [← ZetaRieszCoupledWindow.sum_owned_products (cofactors B) (ownerRows B) f
            (fun _ hn => (cofactors_data B hB hn).1.ne_zero)
            (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.2⟩),
            owner_labels_eq B hB]
    · intro n hn m hm hnm
      calc
        n = r*(s*(n/(r*s))) := (he n hn).symm
        _ = r*(s*(m/(r*s))) := congrArg (fun v => r*(s*v)) hnm
        _ = m := he m hm
  change -wholeSecondCost E A B I O r s N L y scale ≤
      scale*(∑ n ∈ secondRows B r s, ∑ p ∈ ownerRows B (r*(s*n)), f (p*(r*(s*n)))).re ∧
    scale*(∑ n ∈ secondRows B r s, ∑ p ∈ ownerRows B (r*(s*n)), f (p*(r*(s*n)))).re ≤
      wholeSecondCost E A B I O r s N L y scale at hb
  simpa only [hsum,f] using hb

end RiemannGaussian.ZetaRieszCentralPrimeDifference
