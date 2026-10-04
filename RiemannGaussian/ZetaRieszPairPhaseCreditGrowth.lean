/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPairSignCover

/-!
# Cofinal actual-prime mass in the joined signed credit

At every fixed nonzero height, bounded translates of two disjoint prime
intervals have the favorable negative product phase. The ordinary PNT
supplies their actual prime counts. Their original complete-period masks
remain, and their full factorial weight gives a cofinal geometric lower
bound for the existing negative credit. This does not bound the signed
rest minus that exact credit by 399/5000.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairPhaseCreditGrowth
open ZetaRieszJoinedPairSignCover ZetaRieszAllowancePrimeBoxes
open ZetaRieszGlobalCentralPayment ZetaRieszGlobalHeadCentralPayment
open ZetaRieszGlobalPeriodEdgePayment ZetaRieszGlobalBulkPayment
open ZetaRieszLowCountSignedBoundary
open ZetaRieszPairPrefixPayment ZetaRieszLowCountSelbergAudit
open ZetaRieszPrimeEndpoint

/-- Fixed-width prime boxes in a negative half of the ACTUAL product
phase. Their bounded shift is uniform in the order, at fixed height. -/
theorem exists_negative_pair_boxes {y : ℝ} (hy : y≠0) :
    ∃ h C : ℝ,0<h ∧ 0≤C ∧ ∀ b : ℝ,∃ a : ℝ,
      b≤a ∧ a≤b+C ∧ ∀ t : ℝ,
        2*a+h≤t → t≤2*a+3*h → cos (y*t)≤-(1/2 : ℝ) := by
  let z := |y|
  have hz : 0<z := abs_pos.mpr hy
  let h := 1/(8*(z+1))
  let C := Real.pi/z
  have hh : 0<h := by dsimp [h]; positivity
  refine ⟨h,C,hh,by dsimp [C]; positivity,?_⟩
  intro b
  let k : ℤ := ⌈(z*(2*b+h)-Real.pi)/(2*Real.pi)⌉
  let a := (((k : ℝ)*(2*Real.pi)+Real.pi)/z-h)/2
  have hlo : z*(2*b+h)-Real.pi≤(k : ℝ)*(2*Real.pi) :=
    (div_le_iff₀ (by positivity : (0 : ℝ)<2*Real.pi)).mp (Int.le_ceil _)
  have hhi : (k : ℝ)*(2*Real.pi)<z*(2*b+h)-Real.pi+2*Real.pi := by
    have ht := Int.ceil_lt_add_one ((z*(2*b+h)-Real.pi)/(2*Real.pi))
    have ht' := mul_lt_mul_of_pos_right ht (by positivity : (0 : ℝ)<2*Real.pi)
    simpa only [add_mul,div_mul_cancel₀ _ (by positivity : 2*Real.pi≠0),one_mul] using ht'
  have ha : z*(2*a+h)=(k : ℝ)*(2*Real.pi)+Real.pi := by dsimp [a]; field_simp; ring
  have hb : b≤a := by nlinarith only [hlo,ha,hz]
  have hab : a≤b+C := by
    have hC : C*z=Real.pi := by dsimp [C]; field_simp
    nlinarith only [hhi,ha,hC,hz]
  refine ⟨a,hb,hab,?_⟩
  intro t ht htu
  have he : cos (z*(2*a+h))=-1 := by
    rw [ha,add_comm,cos_add_int_mul_two_pi,cos_pi]
  have hw : 2*z*h≤1/2 := by
    dsimp [h]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<8*(z+1))).mpr
    nlinarith only [hz]
  have hd : |z*t-z*(2*a+h)|≤1/2 := by
    rw [abs_of_nonneg (by nlinarith only [ht,hz])]
    nlinarith only [htu,hw,hz]
  have hc := (abs_le.mp ((abs_cos_sub_cos_le (z*t) (z*(2*a+h))).trans hd)).2
  rw [he] at hc
  have hec : cos (z*t)=cos (y*t) := by
    dsimp [z]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_mul,cos_neg]
  rw [hec] at hc
  linarith only [hc]

/-- One ordered incidence per actual label, inside two adjacent boxes. -/
def pairProducts (a h : ℝ) : Finset ℕ :=
  ((logPrimes a h).product (logPrimes (a+h) h)).image (fun pq => pq.1*pq.2)

private theorem largest_box_pair {a h : ℝ} {p q : ℕ}
    (hp : p∈logPrimes a h) (hq : q∈logPrimes (a+h) h) :
    largestPrime (p*q)=q := by
  have pp := (logPrimes_bounds hp).1
  have qp := (logPrimes_bounds hq).1
  have hpq := logPrimes_order le_rfl hp hq
  rw [mul_comm]
  apply ZetaRieszPrimeIntervals.largestPrime_mul q p qp pp.ne_zero
  intro r hr
  rw [pp.primeFactors,Finset.mem_singleton] at hr
  subst r
  exact hpq

private theorem product_injective (a h : ℝ) :
    Set.InjOn (fun pq : ℕ×ℕ => pq.1*pq.2)
      ((logPrimes a h).product (logPrimes (a+h) h)) := by
  rintro ⟨p,q⟩ he ⟨p',q'⟩ hf hh
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp he
  obtain ⟨hp',hq'⟩ := Finset.mem_product.mp hf
  change p∈logPrimes a h at hp
  change q∈logPrimes (a+h) h at hq
  change p'∈logPrimes a h at hp'
  change q'∈logPrimes (a+h) h at hq'
  change p*q=p'*q' at hh
  have hqq : q=q' := by rw [←largest_box_pair hp hq,←largest_box_pair hp' hq',hh]
  subst q'
  have hpp := Nat.eq_of_mul_eq_mul_right (logPrimes_bounds hq).1.pos hh
  simp only [hpp]

theorem pairProducts_card (a h : ℝ) :
    (pairProducts a h).card=(logPrimes a h).card*(logPrimes (a+h) h).card := by
  rw [pairProducts,Finset.card_image_of_injOn (product_injective a h)]
  simp only [Finset.product_eq_sprod,Finset.card_product]

private theorem box_geometry {N : ℕ} (hN : 65536≤N) {a h C : ℝ}
    (hh : 0<h) (_hC : 0≤C) (ha : (N : ℝ)≤a) (hau : a≤N+C)
    (hsize : 2*C+3*h+2≤(N : ℝ)/100) {p q : ℕ}
    (hp : p∈logPrimes a h) (hq : q∈logPrimes (a+h) h) :
    Squarefree (p*q) ∧ (p*q).primeFactors.card=2 ∧
      2*(N : ℝ)≤log (p*q : ℕ) ∧ log (p*q : ℕ)≤2*N+2*C+3*h ∧
      (1971/1000 : ℝ)*N+1<log (p*q : ℕ) ∧
      log (p*q : ℕ)≤(2029/1000 : ℝ)*N-1 ∧
      (12/25 : ℝ)≤log p/log (p*q : ℕ) ∧
      (12/25 : ℝ)≤log q/log (p*q : ℕ) := by
  have pp := (logPrimes_bounds hp).1
  have qp := (logPrimes_bounds hq).1
  have hpb := (logPrimes_bounds hp).2
  have hqb := (logPrimes_bounds hq).2
  have hpq := logPrimes_order le_rfl hp hq
  have hlog : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast pp.ne_zero) (by exact_mod_cast qp.ne_zero)]
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have htlo : 2*(N : ℝ)≤log (p*q : ℕ) := by rw [hlog]; linarith only [ha,hpb.1,hqb.1,hh]
  have hthi : log (p*q : ℕ)≤2*N+2*C+3*h := by rw [hlog]; linarith only [hau,hpb.2,hqb.2]
  have hT : 0<log (p*q : ℕ) := by linarith only [htlo,hNr]
  have hcop := pp.coprime_iff_not_dvd.mpr
    (fun hd => hpq.ne ((Nat.prime_dvd_prime_iff_eq pp qp).mp hd))
  refine ⟨Nat.squarefree_mul_iff.mpr ⟨hcop,pp.squarefree,qp.squarefree⟩,?_,htlo,hthi,
    ?_,?_,?_,?_⟩
  · simp only [Nat.primeFactors_mul pp.ne_zero qp.ne_zero,
      pp.primeFactors,qp.primeFactors,Finset.union_singleton]
    rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hpq.ne.symm),
      Finset.card_singleton]
  · nlinarith only [htlo,hNr]
  · linarith only [hthi,hsize,hNr]
  · apply (le_div_iff₀ hT).mpr
    nlinarith only [hthi,hsize,ha,hpb.1,hNr]
  · apply (le_div_iff₀ hT).mpr
    nlinarith only [hthi,hsize,ha,hqb.1,hh,hNr]

/-- Every funded label is in the ORIGINAL support, including its exact
radial flag and complete period. No edge or physical mask is completed. -/
theorem pairProducts_subset_favorable {N : ℕ} (hN : 65536≤N) {u y a h C : ℝ}
    (hy : 54≤|y|) (hh : 0<h) (hC : 0≤C) (ha : (N : ℝ)≤a) (hau : a≤N+C)
    (hsize : 2*C+3*h+2≤(N : ℝ)/100)
    (hphase : ∀ t : ℝ,2*a+h≤t → t≤2*a+3*h → cos (y*t)≤-(1/2 : ℝ)) :
    pairProducts a h⊆favorableLabels u y N := by
  intro n hn
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp he
  obtain ⟨hs,hcount,htlo,hthi,hilo,hihi,hps,hqs⟩ := box_geometry hN hh hC ha hau hsize hp hq
  have pp := (logPrimes_bounds hp).1
  have qp := (logPrimes_bounds hq).1
  have hpq := logPrimes_order le_rfl hp hq
  have hn0 : (0 : ℝ)<(p*q : ℕ) := by exact_mod_cast Nat.mul_pos pp.pos qp.pos
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have hlo : (39/20 : ℝ)*N<log (p*q : ℕ) := by linarith only [htlo,hNr]
  have hhi : log (p*q : ℕ)≤(203/100 : ℝ)*N := by linarith only [hthi,hsize,hNr]
  have hf : p*q∈fullLabels N := by
    apply Finset.mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (exp_pos _).le).mpr
      rw [sub_zero]
      exact (exp_lt_exp.mpr hlo).trans_eq (exp_log hn0)
    · apply Nat.le_floor
      rw [sub_zero,←exp_log hn0]
      exact exp_le_exp.mpr hhi
  have hsemi : p*q∈semiprimeLabels N := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hf,?_,?_⟩,hs,hcount⟩
    all_goals linarith only [hilo,hihi]
  have hj : p*q∈joinedLabels u N :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hsemi)))
  have hperiod : p*q∈completePeriodLabels (joinedLabels u N) N y := by
    apply interiorLabels_subset_completePeriods _ _ hy
    exact Finset.mem_filter.mpr ⟨hj,hilo,hihi⟩
  have hnot : ¬(p*q).Prime := by
    intro hprime
    rw [hprime.primeFactors,Finset.card_singleton] at hcount
    omega
  have hlog : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast pp.ne_zero) (by exact_mod_cast qp.ne_zero)]
  have hc : cos (y*log (p*q : ℕ))≤-(1/2 : ℝ) := by
    apply hphase
    · rw [hlog]; linarith only [(logPrimes_bounds hp).2.1,(logPrimes_bounds hq).2.1]
    · rw [hlog]; linarith only [(logPrimes_bounds hp).2.2,(logPrimes_bounds hq).2.2]
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hperiod,hnot⟩,hsemi,
    p,q,pp,qp,hpq,rfl,hlo.le,hhi,Or.inl ⟨hps,hqs,by linarith only [hc]⟩⟩

/-- The same actual boxes supply distinct labels at the full prime-pair
exponential scale, uniformly over bounded logarithmic translates. -/
theorem eventually_pairProducts_card_lower {h C : ℝ} (hh : 0<h) (hC : 0≤C) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,∀ a : ℝ,
      (N : ℝ)≤a → a≤N+C →
      c^2*exp (2*(N : ℝ))/((N : ℝ)+1)^2≤((pairProducts a h).card : ℝ) := by
  obtain ⟨c,hc,hbound⟩ := eventually_logPrimes_card_lower_slope
    (by norm_num : (0 : ℝ)<1) hh (show 0≤C+h by linarith only [hC,hh])
  refine ⟨c,hc,?_⟩
  filter_upwards [hbound] with N hN a ha hau
  have hp := hN a (by simpa only [one_mul] using ha)
    (by simpa only [one_mul] using (show a≤N+(C+h) by linarith only [hau,hh]))
  have hq := hN (a+h)
    (by simpa only [one_mul] using (show (N : ℝ)≤a+h by linarith only [ha,hh]))
    (by simpa only [one_mul] using (show a+h≤N+(C+h) by linarith only [hau]))
  simp only [one_mul] at hp hq
  have hm := mul_le_mul hp hq (by positivity : 0≤c*exp N/((N : ℝ)+1))
    (Nat.cast_nonneg _)
  rw [pairProducts_card,Nat.cast_mul]
  apply le_trans _ hm
  rw [←pow_two,div_pow,mul_pow,←exp_nat_mul]
  norm_num

private theorem kernel_lower {N n : ℕ} {y D : ℝ}
    (hlo : 2*(N : ℝ)≤log n) (hhi : log n≤2*N+D) :
    exp (-(3/2 : ℝ)*(2*N+D))*(2*N)^N/(N.factorial : ℝ)≤
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by
  rw [norm_zetaPrimeLogKernel]
  have hsre : ((3/2 : ℂ)+Complex.I*y).re=3/2 := by simp
  simp only [zetaPrimeExpWeight,hsre]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤2*N) hlo N
  have hex := exp_le_exp.mpr (show -(3/2 : ℝ)*(2*N+D)≤-(3/2 : ℝ)*log n by
    nlinarith only [hhi])
  exact (div_le_div_of_nonneg_right
    (mul_le_mul hex hpow (by positivity) (exp_pos _).le)
    (Nat.cast_nonneg (α:=ℝ) N.factorial)).trans_eq (by ring)

/-- A finite, independent signed credit with the exact factorial weight.
No hypothetical zero or replacement of the phase is involved. -/
theorem pair_box_credit_lower {N : ℕ} (hN : 65536≤N) {u y a h C : ℝ}
    (hu : 0≤u) (hy : 54≤|y|) (hh : 0<h) (hC : 0≤C)
    (ha : (N : ℝ)≤a) (hau : a≤N+C)
    (hsize : 2*C+3*h+2≤(N : ℝ)/100)
    (hphase : ∀ t : ℝ,2*a+h≤t → t≤2*a+3*h → cos (y*t)≤-(1/2 : ℝ)) :
    ((pairProducts a h).card : ℝ)*(u^(N+1)/800*
      (exp (-(3/2 : ℝ)*(2*N+2*C+3*h))*(2*N)^N/N.factorial))≤
      signCredit u y N := by
  let Q := exp (-(3/2 : ℝ)*(2*N+2*C+3*h))*(2*N)^N/(N.factorial : ℝ)
  have hsub := pairProducts_subset_favorable (u := u) hN hy hh hC ha hau hsize hphase
  have hs : ∑ _n∈pairProducts a h,Q/4≤∑ n∈pairProducts a h,
      log n*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖*(cos (y*log n))^2 := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp he
    change p∈logPrimes a h at hp
    change q∈logPrimes (a+h) h at hq
    obtain ⟨_,_,htlo,hthi,_,_,_,_⟩ := box_geometry hN hh hC ha hau hsize hp hq
    have ht1 : 1≤log (p*q : ℕ) := by
      have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
      linarith only [htlo,hNr]
    have hlog : log (p*q : ℕ)=log p+log q := by
      rw [Nat.cast_mul,log_mul
        (by exact_mod_cast (logPrimes_bounds hp).1.ne_zero)
        (by exact_mod_cast (logPrimes_bounds hq).1.ne_zero)]
    have hc : cos (y*log (p*q : ℕ))≤-(1/2 : ℝ) := by
      apply hphase
      · rw [hlog]; linarith only [(logPrimes_bounds hp).2.1,(logPrimes_bounds hq).2.1]
      · rw [hlog]; linarith only [(logPrimes_bounds hp).2.2,(logPrimes_bounds hq).2.2]
    have hcs : (1/4 : ℝ)≤(cos (y*log (p*q : ℕ)))^2 := by
      nlinarith only [hc,sq_nonneg (cos (y*log (p*q : ℕ))+1/2)]
    have hk : Q≤‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖ := by
      simpa only [Q,add_assoc] using
        (kernel_lower (y := y) (D := 2*C+3*h) htlo (by linarith only [hthi]))
    have hm := hk.trans (le_mul_of_one_le_left (norm_nonneg _) ht1)
    calc
      _ ≤ (1/4 : ℝ)*(log (p*q : ℕ)*‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖) := by
        linarith only [hm]
      _ ≤ _ := by
        simpa only [mul_comm,mul_left_comm,mul_assoc] using
          mul_le_mul_of_nonneg_left hcs
            (mul_nonneg (log_natCast_nonneg (p*q))
              (norm_nonneg (zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q))))
  have hfull := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun n : ℕ => log n*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖*(cos (y*log n))^2)
    (fun n _ _ => mul_nonneg (mul_nonneg (log_natCast_nonneg n) (norm_nonneg _)) (sq_nonneg _))
  have hb := mul_le_mul_of_nonneg_left (hs.trans hfull)
    (by positivity : 0≤u^(N+1)/200)
  unfold signCredit
  apply le_trans _ hb
  simp only [Finset.sum_eq_card_nsmul,nsmul_eq_mul]
  dsimp only [Q]
  ring_nf
  exact le_rfl

/-- Exact saddle normalization of the funding boxes. The constant may
depend on the fixed box width/height, but the rate is the native `2*u`. -/
theorem pair_box_scalar_lower {u c D : ℝ} (hu : 0≤u) {N : ℕ} (hN : 1≤N) :
    (u*c^2*exp (-(3/2 : ℝ)*D)/4800)*(2*u)^N/((N : ℝ)+1)^3≤
      (c^2*exp (2*(N : ℝ))/((N : ℝ)+1)^2)*
        (u^(N+1)/800*(exp (-(3/2 : ℝ)*(2*N+D))*(2*N)^N/N.factorial)) := by
  have hs := PrimeWindow.local_monomial_lower hN (by norm_num : (0 : ℝ)≤2)
  norm_num [PrimeWindow.localGrowth] at hs
  rw [show -(2*(N : ℝ))/2=-(N : ℝ) by ring] at hs
  have hs' : (2 : ℝ)^N/(6*((N : ℝ)+1))≤
      exp (-(N : ℝ))*(2*N)^N/N.factorial := by
    apply le_trans _ hs
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have he : exp (2*(N : ℝ))*exp (-(3/2 : ℝ)*(2*N+D))=
      exp (-(3/2 : ℝ)*D)*exp (-(N : ℝ)) := by
    rw [←exp_add,←exp_add]
    congr 1
    ring
  let k := c^2*u^(N+1)*exp (-(3/2 : ℝ)*D)/(800*((N : ℝ)+1)^2)
  have hk : 0≤k := by dsimp only [k]; positivity
  calc
    _ = k*((2 : ℝ)^N/(6*((N : ℝ)+1))) := by
      dsimp only [k]
      rw [mul_pow,pow_succ]
      field_simp
      ring
    _ ≤ k*(exp (-(N : ℝ))*(2*N)^N/N.factorial) :=
      mul_le_mul_of_nonneg_left hs' hk
    _ = _ := by
      dsimp only [k]
      calc
        _ = c^2*u^(N+1)/(800*((N : ℝ)+1)^2)*
          (exp (-(3/2 : ℝ)*D)*exp (-(N : ℝ)))*((2*N)^N/N.factorial) := by ring
        _ = _ := by rw [←he]; field_simp

/-- An actual-prime, fixed-height geometric lower bound for the signed
credit at EVERY sufficiently large order, not only a model or subsequence.
The remaining sum still has to be bounded jointly with the exact credit. -/
theorem eventually_signCredit_growth {u y : ℝ} (hu : 1/2<u) (hy : 54≤|y|) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      c*(2*u)^N/((N : ℝ)+1)^3≤ signCredit u y N := by
  have hy0 : y≠0 := by intro hz; simp only [hz,abs_zero] at hy; linarith only [hy]
  obtain ⟨h,C,hh,hC,hphase⟩ := exists_negative_pair_boxes hy0
  obtain ⟨c,hc,hcard⟩ := eventually_pairProducts_card_lower hh hC
  let d := u*c^2*exp (-(3/2 : ℝ)*(2*C+3*h))/4800
  have hd : 0<d := by dsimp only [d]; positivity
  refine ⟨d,hd,?_⟩
  have hsize : ∀ᶠ N : ℕ in atTop,2*C+3*h+2≤(N : ℝ)/100 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (100*(2*C+3*h+2)))] with N hN
    linarith only [hN]
  filter_upwards [hcard,hsize,eventually_ge_atTop (65536 : ℕ)] with N hn hs hN
  obtain ⟨a,ha,hau,hcos⟩ := hphase N
  have hb := hn a ha hau
  have hu0 : 0≤u := by linarith only [hu]
  have hm : 0≤u^(N+1)/800*
      (exp (-(3/2 : ℝ)*(2*N+(2*C+3*h)))*(2*N)^N/N.factorial) := by positivity
  calc
    _ ≤ (c^2*exp (2*(N : ℝ))/((N : ℝ)+1)^2)*
        (u^(N+1)/800*(exp (-(3/2 : ℝ)*(2*N+(2*C+3*h)))*(2*N)^N/N.factorial)) :=
      pair_box_scalar_lower hu0 (by omega : 1≤N)
    _ ≤ ((pairProducts a h).card : ℝ)*(u^(N+1)/800*
        (exp (-(3/2 : ℝ)*(2*N+(2*C+3*h)))*(2*N)^N/N.factorial)) :=
      mul_le_mul_of_nonneg_right hb hm
    _ ≤ signCredit u y N := by
      simpa only [add_assoc] using pair_box_credit_lower hN hu0 hy hh hC ha hau hs hcos

/-- The exact favorable signed contribution receives the same cofinal
credit. Its excess is retained, not discarded by a rational benchmark. -/
theorem eventually_exactSignCredit_growth {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      c*(2*u)^N/((N : ℝ)+1)^3≤exactSignCredit u y N := by
  obtain ⟨c,hc,hbound⟩ := eventually_signCredit_growth hu hy
  refine ⟨c,hc,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (65536 : ℕ)] with N hn hN
  exact hn.trans (signCredit_le_exact hu.le hU hN y)

/-- A direct, independent signed inequality for a literal retained
population. The magnitude grows at source scale, so it must be matched
against the signed rest rather than replaced by a fixed positive cost. -/
theorem eventually_favorable_sum_upper {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      ((u : ℂ)^(N+1)*∑ n∈favorableLabels u y N,
        (prefixCoefficient u N n-selbergCoefficient n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re≤
      -(c*(2*u)^N/((N : ℝ)+1)^3) := by
  obtain ⟨c,hc,hbound⟩ := eventually_exactSignCredit_growth hu hU hy
  refine ⟨c,hc,?_⟩
  filter_upwards [hbound] with N hN
  unfold exactSignCredit at hN
  linarith only [hN]

theorem signCredit_tendsto_atTop {u y : ℝ} (hu : 1/2<u) (hy : 54≤|y|) :
    Tendsto (signCredit u y) atTop atTop := by
  obtain ⟨c,hc,hbound⟩ := eventually_signCredit_growth hu hy
  have ht := ZetaRieszAllowanceGrowth.geometric_over_successor_four_tendsto
    (show 1<2*u by linarith only [hu])
  have hct : Tendsto (fun N : ℕ => c*((2*u)^N/((N : ℝ)+1)^4)) atTop atTop :=
    ht.const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ hct
  filter_upwards [hbound] with N hN
  apply le_trans _ hN
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hn : 1≤(N : ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) N]
  simpa only [pow_succ] using le_mul_of_one_le_right (pow_nonneg (by positivity) 3) hn

theorem exactSignCredit_tendsto_atTop {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    Tendsto (exactSignCredit u y) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (signCredit_tendsto_atTop hu hy)
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with N hN
  exact signCredit_le_exact hu.le hU hN y

/-- The quantitative credit applies to the actual native endgame order
sequence, with every original mask and the full signed contribution. -/
theorem native_exactSignCredit_tendsto_atTop {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    Tendsto (fun j => exactSignCredit u y
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)) atTop atTop :=
  (exactSignCredit_tendsto_atTop hu hU hy).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder

end RiemannGaussian.ZetaRieszPairPhaseCreditGrowth
