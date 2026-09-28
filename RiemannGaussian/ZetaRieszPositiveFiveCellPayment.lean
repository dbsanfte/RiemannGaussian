/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveCells

/-!
# Spending the complete checked positive-five cover

The accepted leaf costs transfer to the original finite prime sum. The
last-prime endpoint, least-prime weight and moving angular masks stay
coupled until the explicit upper inequality is proved.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveCellPayment
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators Classical
open ZetaRieszPositiveFiveCover ZetaRieszPositiveFiveInterior
open ZetaRieszPositiveFiveCells ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszPrimeEndpoint

/-- Accepted nonempty leaves bound the complete translated harmonic cap.
This exports the numerical debit for the literal prime transfer. -/
theorem checked_cap_integral_le {lo hi owner : ℚ} {B : Cover.Box} {w : ℚ × ℚ}
    (hc : check lo hi owner B w = true)
    (hn : ¬ ((B 2).2 ≤ (B 1).1 ∨ (cap lo hi B w.1 w.2).height ≤ offset lo B ∨
      (cap lo hi B w.1 w.2).b ≤ offset lo B)) :
    let c := cap lo hi B w.1 w.2
    (c.b : ℝ) < c.total ∧
    (∫ r : ℝ in 0..(c.b : ℝ),
      max 0 (min (r-offset lo B) ((c.height : ℝ)-offset lo B))/(r*(c.total-r))) ≤
      (w.2 : ℝ)*((lo : ℝ)*(B 0).1*(B 1).1*(B 2).1) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hr : 0 ≤ offset lo B := le_max_left _ _
  let c := cap lo hi B w.1 w.2
  have hnum := hc.2
  change (if (B 2).2 ≤ (B 1).1 ∨ c.height ≤ offset lo B ∨ c.b ≤ offset lo B then true
    else if offset lo B = 0 then decide (w.1 = 0) && ZetaRieszCapacityCheck.check c
    else ZetaRieszCapacityCheck.check c &&
      ZetaRieszCapacityCheck.check {c with height := offset lo B,lower := w.1,upper := 1000000}) = true
    at hnum
  rw [if_neg hn] at hnum
  have hbig : ZetaRieszCapacityCheck.check c = true := by
    split_ifs at hnum with h
    · simp only [Bool.and_eq_true] at hnum
      exact hnum.2
    · simp only [Bool.and_eq_true] at hnum
      exact hnum.1
  have hg : 0 ≤ c.a ∧ c.a < c.b ∧ c.b < c.total ∧ 0 < c.height := by
    have h := hbig
    simp only [ZetaRieszCapacityCheck.check,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  refine ⟨by exact_mod_cast hg.2.2.1,?_⟩
  have hpay : (c.upper : ℝ)-(w.1 : ℝ) =
      (w.2 : ℝ)*((lo : ℝ)*(B 0).1*(B 1).1*(B 2).1) := by
    simp only [c,cap,Rat.cast_add,Rat.cast_mul]
    ring
  rw [← hpay]
  by_cases hr0 : offset lo B = 0
  · rw [if_pos hr0] at hnum
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hnum
    have hw0 : (w.1 : ℝ) = 0 := by exact_mod_cast hnum.1
    have hh : (0 : ℝ) ≤ c.height := by exact_mod_cast hg.2.2.2.le
    have hb : (0 : ℝ) ≤ c.b := by
      have : (0 : ℚ) < c.b := hg.2.1
      exact_mod_cast this.le
    have he : (offset lo B : ℝ) = 0 := by rw [hr0,Rat.cast_zero]
    rw [he,hw0,sub_zero]
    calc
      _ = ∫ r : ℝ in 0..(c.b : ℝ), min r (c.height : ℝ)/(r*(c.total-r)) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [Set.uIcc_of_le hb] at hr
        change max 0 (min (r-0) (c.height : ℝ))/(r*(c.total-r)) = _
        rw [sub_zero,max_eq_right (le_min hr.1 hh)]
      _ ≤ _ := by simpa only [c,cap,Rat.cast_zero,sub_zero] using
          (ZetaRieszCapacityCheck.check_sound hbig).2
  · rw [if_neg hr0] at hnum
    simp only [Bool.and_eq_true] at hnum
    have hs := hnum.2
    have hrc : offset lo B ≤ c.height := by
      dsimp [c,cap]
      exact le_add_of_nonneg_right (le_max_left _ _)
    simpa only [c,cap,Rat.cast_zero] using
      checked_shifted_cap_integral_le c (offset lo B) w.1 1000000 hbig hs hrc


/-- The five-prime estimate may use the complete nonnegative cap interval;
only its lower harmonic integration endpoint is extended. -/
theorem eventually_weightedPrimeMass_full_upper {h α β a b Q r c ε : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β)
    (ha : 0 < a) (hab : a < b) (hbQ : b < Q) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 3 → ℝ) (t : ℝ),
      (N : ℝ) ≤ t → (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∑ i, (lo i+H i)) ≤ t*(1-Q) →
      weightedPrimeMass lo H a b r c t h ≤
        ((1001/1000 : ℝ)*(∏ i, H i/lo i))*((10001/10000 : ℝ)*h/t)*
          ((10003/10000 : ℝ)*
            (∫ x : ℝ in 0..b, max 0 (min (x-r) c)/(x*(Q-x)))+ε) := by
  have hi : IntervalIntegrable (fun x : ℝ => max 0 (min (x-r) c)/(x*(Q-x))) volume 0 b := by
    have hbig := ZetaRieszOrderedCapacity.cap_integrable_nonneg le_rfl (ha.le.trans hab.le)
      hbQ (add_nonneg hr hc)
    have hsmall := ZetaRieszOrderedCapacity.cap_integrable_nonneg le_rfl (ha.le.trans hab.le) hbQ hr
    convert hbig.sub hsmall using 1
    funext x
    rw [shifted_cap_eq_cap_sub hc,sub_div]
  have hI : (∫ x : ℝ in a..b, max 0 (min (x-r) c)/(x*(Q-x))) ≤
      ∫ x : ℝ in 0..b, max 0 (min (x-r) c)/(x*(Q-x)) := by
    apply intervalIntegral.integral_mono_interval ha.le hab.le le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact div_nonneg (le_max_left _ _) (mul_nonneg hx.1.le (by linarith [hx.2]))
    · exact hi
  filter_upwards [eventually_weightedPrimeMass_upper hh hhu hα hβ ha hab hbQ hc hε,
    eventually_ge_atTop (1 : ℕ)] with N hN hpos lo H t ht hlo hH hsum
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hpos)
  have ht0 : 0 < t := hn.trans_le ht
  have hp : 0 ≤ ∏ i, H i/lo i := Finset.prod_nonneg (fun i _ =>
    div_nonneg ((mul_pos hβ hn).le.trans (hH i)) ((mul_pos hα hn).le.trans (hlo i)))
  exact (hN lo H t ht hlo hH hsum).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 10003/10000)) le_rfl)
      (by positivity))

private def reps (lo H : Fin 3 → ℝ) (a b t h : ℝ) :
    Finset ((Fin 3 → ℕ) × ℕ × ℕ) :=
  (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).biUnion (fun v =>
    (logPrimes (t*a) (t*(b-a))).biUnion (fun p =>
      (logPrimes (t-Real.log ((∏ i, v i)*p : ℕ)) h).image (fun q => (v,p,q))))

private def label (v : (Fin 3 → ℕ) × ℕ × ℕ) : ℕ :=
  (∏ i, v.1 i)*v.2.1*v.2.2

/-- A finite incidence bound with the original product endpoint. Every
label supplies an actual representation and its pointwise coefficient
inequality; the final sum only overcounts nonnegative arithmetic cost. -/
theorem mass_le_weightedPrimeMass_of_cover (S : Finset ℕ) (L : ℝ)
    (lo H : Fin 3 → ℝ) (a b r c t h D : ℝ) (hD : 0 ≤ D)
    (hcover : ∀ n ∈ S, ∃ (v : Fin 3 → ℕ) (p q : ℕ),
      (∀ i, v i ∈ logPrimes (lo i) (H i)) ∧
      p ∈ logPrimes (t*a) (t*(b-a)) ∧
      q ∈ logPrimes (t-Real.log ((∏ i, v i)*p : ℕ)) h ∧
      n = (∏ i, v i)*p*q ∧
      max 0 (SquarefreeVaughanLogSource.coefficient L n).re ≤
        D*max 0 (min (Real.log p/t-r) c)) :
    (∑ n ∈ S, max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)) ≤
      D*weightedPrimeMass lo H a b r c t h := by
  let F := fun p : ℕ => max 0 (min (Real.log p/t-r) c)
  let cost := fun n : ℕ => max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)
  let U := (reps lo H a b t h).filter (fun v => label v ∈ S ∧
    max 0 (SquarefreeVaughanLogSource.coefficient L (label v)).re ≤ D*F v.2.1)
  have hsub : S ⊆ U.image label := by
    intro n hn
    obtain ⟨v,p,q,hv,hp,hq,he,hc⟩ := hcover n hn
    refine Finset.mem_image.mpr ⟨(v,p,q),?_,he.symm⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_,?_⟩
    · exact Finset.mem_biUnion.mpr ⟨v,Fintype.mem_piFinset.mpr hv,
        Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩⟩
    · change (∏ i, v i)*p*q ∈ S
      rwa [← he]
    · change max 0 (SquarefreeVaughanLogSource.coefficient L ((∏ i, v i)*p*q)).re ≤ D*F p
      rwa [← he]
  let G := fun v : (Fin 3 → ℕ) × ℕ × ℕ =>
    D*(∏ i, (v.1 i : ℝ)⁻¹)*(F v.2.1/(v.2.1 : ℝ))*(v.2.2 : ℝ)⁻¹
  have hG : ∀ v, 0 ≤ G v := by intro v; dsimp [G,F]; positivity
  have hpoint (v : (Fin 3 → ℕ) × ℕ × ℕ) (hv : v ∈ U) : cost (label v) ≤ G v := by
    have hc := (Finset.mem_filter.mp hv).2.2
    have hb := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (label v))
    apply hb.trans_eq
    dsimp [G,label]
    simp only [Nat.cast_mul,Nat.cast_prod,div_eq_mul_inv,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  calc
    _ ≤ ∑ n ∈ U.image label, cost n := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => by dsimp [cost]; positivity)
    _ ≤ ∑ v ∈ U, cost (label v) := Finset.sum_image_le_of_nonneg
      (fun v _ => by dsimp [cost]; positivity)
    _ ≤ ∑ v ∈ U, G v := Finset.sum_le_sum hpoint
    _ ≤ ∑ v ∈ reps lo H a b t h, G v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun v _ _ => hG v)
    _ ≤ D*weightedPrimeMass lo H a b r c t h := by
      unfold reps
      rw [Finset.sum_biUnion (by
        intro v _ w _ hvw
        apply Finset.disjoint_left.mpr
        intro x hx hy
        obtain ⟨p,_,hx⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨q,_,hy⟩ := Finset.mem_biUnion.mp hy
        obtain ⟨p',_,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨q',_,he⟩ := Finset.mem_image.mp hy
        exact hvw (congrArg Prod.fst he).symm)]
      unfold weightedPrimeMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v hv
      rw [Finset.sum_biUnion (by
        intro p _ q _ hpq
        apply Finset.disjoint_left.mpr
        intro x hx hy
        obtain ⟨p',_,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨q',_,he⟩ := Finset.mem_image.mp hy
        exact hpq (congrArg (fun e : (Fin 3 → ℕ) × ℕ × ℕ => e.2.1) he).symm)]
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      apply (Finset.sum_image_le_of_nonneg (fun v _ => hG v)).trans
      exact le_of_eq (by dsimp [G,F]; congr 1; ext q; ring)

/-- Outer prime windows enclose the original moving-share cell. -/
def outerLower (B : Cover.Box) (t : ℝ) (i : Fin 3) : ℝ := t*(B i).1

/-- The upper endpoint is `(t+h)*B.high`, not the frozen-share endpoint. -/
def outerWidth (B : Cover.Box) (t h : ℝ) (i : Fin 3) : ℝ :=
  t*((B i).2-(B i).1)+h*(B i).2

/-- The literal selected population is bounded by the five coupled prime
sums. The extra least-prime endpoint is paid explicitly by `hpad`. -/
theorem population_mass_le_primeMass {lo hi owner : ℚ} {B : Cover.Box}
    (hv : valid lo hi owner B) (w : ℚ × ℚ)
    (hlo : (2 : ℝ) ≤ 3*(lo : ℝ)) (hhi : 4*(hi : ℝ) ≤ 3)
    (S : Finset ℕ) {L t h δ a b : ℝ} (ht : 0 < t) (hh : 0 ≤ h)
    (haδ : a ≤ δ) (hδ : 0 ≤ δ)
    (hpad : ((cap lo hi B w.1 w.2).b : ℝ)*(t+h) ≤ t*b)
    (hLlo : (lo : ℝ)*(t+h) ≤ L) (hLhi : L ≤ (hi : ℝ)*t) :
    (∑ n ∈ population B S L t h δ,
      max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)) ≤
      ((t+h)/(lo : ℝ))*weightedPrimeMass (outerLower B t) (outerWidth B t h)
        a b (offset lo B) ((cap lo hi B w.1 w.2).height-offset lo B) t h := by
  have hlo0 : (0 : ℝ) < lo := by exact_mod_cast hv.1
  have hhi0 : (0 : ℝ) < hi := hlo0.trans_le (by exact_mod_cast hv.2.1)
  have hBlo (i : Fin 3) : (0 : ℝ) < (B i).1 := by exact_mod_cast (hv.2.2.2.1 i).1
  have hBhi (i : Fin 3) : (0 : ℝ) < (B i).2 :=
    (hBlo i).trans_le (by exact_mod_cast (hv.2.2.2.1 i).2)
  apply mass_le_weightedPrimeMass_of_cover _ _ _ _ _ _ _ _ _ _ _ (by positivity)
  intro n hn
  obtain ⟨_,hs,hc,htn,hnth,hpos,q,A,B',r,he,hrb,hba,haq,hrδ,hshare⟩ := Finset.mem_filter.mp hn
  obtain ⟨hp,hq,hA,hB,hr,hnprod,hlog⟩ := cofactor_data hs hc he hrb hba haq
  have hT : 0 < Real.log n := ht.trans htn
  let v : Fin 3 → ℕ := ![largestPrime n,B',A]
  have hvprime (i : Fin 3) : (v i).Prime := by fin_cases i <;> assumption
  have hshare' (i : Fin 3) : (B i).1 < Real.log (v i)/Real.log n ∧
      Real.log (v i)/Real.log n ≤ (B i).2 := by
    have hx := Set.mem_pi.mp hshare i (Set.mem_univ i)
    fin_cases i <;> simpa [shares,v,Set.mem_Ioc] using hx
  have hvwindow (i : Fin 3) : v i ∈ logPrimes (outerLower B t i) (outerWidth B t h i) := by
    apply (mem_logPrimes_iff _ _ _).mpr
    refine ⟨hvprime i,?_,?_⟩
    · have hl := (lt_div_iff₀ hT).mp (hshare' i).1
      dsimp [outerLower]
      nlinarith [mul_le_mul_of_nonneg_left htn.le (hBlo i).le]
    · have hu := (div_le_iff₀ hT).mp (hshare' i).2
      dsimp [outerLower,outerWidth]
      nlinarith [mul_le_mul_of_nonneg_left hnth (hBhi i).le]
  have hR := least_share_le_cap_endpoint (lo := lo) (hi := hi) w hs hc he hrb hba haq hshare hT
  have hR0 : 0 ≤ ((cap lo hi B w.1 w.2).b : ℝ) :=
    (div_nonneg (Real.log_natCast_nonneg r) hT.le).trans hR
  have hrwin : r ∈ logPrimes (t*a) (t*(b-a)) := by
    apply (mem_logPrimes_iff _ _ _).mpr
    refine ⟨hr,?_,?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left htn.le hδ,
        mul_le_mul_of_nonneg_left haδ ht.le]
    · have hr' := (div_le_iff₀ hT).mp hR
      nlinarith [mul_le_mul_of_nonneg_left hnth hR0]
  have hvprod : (∏ i, v i : ℕ) = largestPrime n*B'*A := by simp [v,Fin.prod_univ_three,mul_assoc]
  have hprod : n = (∏ i, v i)*r*q := by rwa [hvprod]
  have hlog' : Real.log n = Real.log ((∏ i, v i)*r : ℕ)+Real.log q := by
    rw [hprod,Nat.cast_mul,Real.log_mul]
    · exact_mod_cast Nat.mul_ne_zero
        (Finset.prod_ne_zero_iff.mpr (fun i _ => (hvprime i).ne_zero)) hr.ne_zero
    · exact_mod_cast hq.ne_zero
  refine ⟨v,r,q,hvwindow,hrwin,(mem_logPrimes_iff _ _ _).mpr
    ⟨hq,by linarith,by linarith⟩,hprod,?_⟩
  have hLlon : (lo : ℝ)*Real.log n ≤ L :=
    (mul_le_mul_of_nonneg_left hnth hlo0.le).trans hLlo
  have hLhin : L ≤ (hi : ℝ)*Real.log n :=
    hLhi.trans (mul_le_mul_of_nonneg_left htn.le hhi0.le)
  have hc' := coefficient_le_window_cap hv hs hc he hrb hba haq hshare ht htn.le hnth
    hLlon hLhin (by nlinarith [mul_le_mul_of_nonneg_right hlo hT.le])
    (by nlinarith [mul_le_mul_of_nonneg_right hhi hT.le])
  simpa only [cap,Rat.cast_add,Rat.cast_max,Rat.cast_min,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_zero,Rat.cast_one,Rat.cast_ofNat,add_sub_cancel_left] using hc'

private theorem population_empty_of_flat {B : Cover.Box} {i : Fin 3}
    (hi : (B i).2 ≤ (B i).1) (S : Finset ℕ) (L t h δ : ℝ) :
    population B S L t h δ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨_,_,_,_,_,_,q,a,b,r,_,_,_,_,_,hshare⟩ := Finset.mem_filter.mp hn
  have hx := Set.mem_pi.mp hshare i (Set.mem_univ i)
  have hi' : ((B i).2 : ℝ) ≤ (B i).1 := by exact_mod_cast hi
  exact (hx.1.trans_le (hx.2.trans hi')).false

/-- A zero-cost certificate branch contains no positive original label.
It does not discard a positive boundary mass. -/
theorem population_empty_of_zero_branch {lo hi owner : ℚ} {B : Cover.Box}
    (hv : valid lo hi owner B) (w : ℚ × ℚ)
    (hlo : (2 : ℝ) ≤ 3*(lo : ℝ)) (hhi : 4*(hi : ℝ) ≤ 3)
    (hz : (B 2).2 ≤ (B 1).1 ∨ (cap lo hi B w.1 w.2).height ≤ offset lo B ∨
      (cap lo hi B w.1 w.2).b ≤ offset lo B)
    (S : Finset ℕ) {L t h δ : ℝ} (ht : 0 < t)
    (hLlo : (lo : ℝ)*(t+h) ≤ L) (hLhi : L ≤ (hi : ℝ)*t) :
    population B S L t h δ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨_,hs,hc,htn,hnth,hpos,q,a,b,r,he,hrb,hba,haq,_,hshare⟩ := Finset.mem_filter.mp hn
  obtain ⟨_,_,ha,hb,_,_,_⟩ := cofactor_data hs hc he hrb hba haq
  have hT := ht.trans htn
  have hlo0 : (0 : ℝ) < lo := by exact_mod_cast hv.1
  have hhi0 : (0 : ℝ) < hi := hlo0.trans_le (by exact_mod_cast hv.2.1)
  have hLlon : (lo : ℝ)*Real.log n ≤ L :=
    (mul_le_mul_of_nonneg_left hnth hlo0.le).trans hLlo
  have hLhin : L ≤ (hi : ℝ)*Real.log n :=
    hLhi.trans (mul_le_mul_of_nonneg_left htn.le hhi0.le)
  have hcoeff := coefficient_le_cell_cap hv hs hc he hrb hba haq hshare hLlon hLhin
    (by nlinarith [mul_le_mul_of_nonneg_right hlo hT.le])
    (by nlinarith [mul_le_mul_of_nonneg_right hhi hT.le])
  rcases hz with hz | hz | hz
  · have hx1 := Set.mem_pi.mp hshare 1 (Set.mem_univ 1)
    have hx2 := Set.mem_pi.mp hshare 2 (Set.mem_univ 2)
    change (B 1).1 < Real.log b/Real.log n ∧ Real.log b/Real.log n ≤ (B 1).2 at hx1
    change (B 2).1 < Real.log a/Real.log n ∧ Real.log a/Real.log n ≤ (B 2).2 at hx2
    have hz' : ((B 2).2 : ℝ) ≤ (B 1).1 := by exact_mod_cast hz
    have hlog : Real.log b/Real.log n ≤ Real.log a/Real.log n :=
      div_le_div_of_nonneg_right
        (Real.log_le_log (by exact_mod_cast hb.pos) (by exact_mod_cast hba.le)) hT.le
    linarith
  · have hm : max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ))) = 0 := by
      have h := hz
      simp only [cap] at h
      have : max 0 (min (hi-(B 0).1) (1+2*(B 0).2-3*lo)) = 0 :=
        le_antisymm (by linarith) (le_max_left _ _)
      exact_mod_cast this
    rw [hm,max_eq_left (min_le_right _ _),mul_zero,max_eq_right hpos.le] at hcoeff
    exact hpos.not_ge hcoeff
  · have hr := least_share_le_cap_endpoint (lo := lo) (hi := hi) w hs hc he hrb hba haq hshare hT
    have hz' : ((cap lo hi B w.1 w.2).b : ℝ) ≤ offset lo B := by exact_mod_cast hz
    have hF : max 0 (min (Real.log r/Real.log n-(offset lo B : ℝ))
        (max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ))))) = 0 := by
      apply max_eq_left
      exact (min_le_left _ _).trans (sub_nonpos.mpr (hr.trans hz'))
    rw [hF,mul_zero,max_eq_right hpos.le] at hcoeff
    exact hpos.not_ge hcoeff

end
end RiemannGaussian.ZetaRieszPositiveFiveCellPayment
