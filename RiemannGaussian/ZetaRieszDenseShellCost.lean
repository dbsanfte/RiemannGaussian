/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszIntermediateScaleCost

/-!
# Dense intermediate populations in a union of logarithmic shells

Many intermediate prime factors do not imply large reciprocal prime mass.
Dense clusters can therefore be priced after the ORIGINAL signed prime
period, without any cap on their number of factors. All literal ownership
clips, phases and factorial allocations remain. This covers unions of a
growing number of shells; an unrestricted spread over the full gap and a
complete original fibre cover are still open.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszDenseShellCost
open ZetaRieszIntermediateScaleCost ZetaRieszParityLayerCost
open ZetaRieszBroadOwnerPeriodFloor ZetaRieszSmallCofactorCancellation
open ZetaRieszSmallOwnerBoundary ZetaRieszSignedPeriodFloor
open ZetaRieszFixedCountPeriod ZetaRieszPrimeEndpoint
open ZetaRieszAllowancePrimeBoxes ZetaRieszOwnerCurvatureFloor
open ZetaRieszJointOwnerFibreFloor ZetaRieszClippedOwnerPeriodFloor
open ZetaRieszStaggeredFloor

set_option maxHeartbeats 800000

/-- A canonical shell exists for every intermediate prime log. Closed
upper endpoints belong to the lower shell, so even exact dyadic boundary
points are neither dropped nor counted twice. -/
theorem exists_unique_log_shell {B x : ℝ} (hB : 0<B) (hx : B<x) :
    ∃! j : ℕ,B*(2 : ℝ)^j<x ∧ x≤2*(B*(2 : ℝ)^j) := by
  have hr : 1<x/B := (lt_div_iff₀ hB).mpr (by simpa using hx)
  have he : ∃ n : ℕ,x/B≤(2 : ℝ)^n := by
    obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (x/B) (by norm_num : (1 : ℝ)<2)
    exact ⟨n,hn.le⟩
  let n := Nat.find he
  have hn : x/B≤(2 : ℝ)^n := Nat.find_spec he
  have hn0 : 0<n := by
    by_contra h
    have hz : n=0 := by omega
    rw [hz,pow_zero] at hn
    linarith only [hr,hn]
  have hpred : n-1+1=n := by omega
  have hlo : (2 : ℝ)^(n-1)<x/B := lt_of_not_ge (Nat.find_min he (by dsimp [n]; omega))
  have hlow : B*(2 : ℝ)^(n-1)<x := by
    have hh := (lt_div_iff₀ hB).mp hlo
    simpa only [mul_comm] using hh
  have hupp : x≤2*(B*(2 : ℝ)^(n-1)) := by
    have hh := (div_le_iff₀ hB).mp hn
    rw [← hpred,pow_succ] at hh
    convert hh using 1 <;> first | rfl | ring
  refine ⟨n-1,⟨hlow,hupp⟩,?_⟩
  intro j hj
  rcases lt_trichotomy j (n-1) with h | h | h
  · have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by omega : j+1≤n-1)) hB.le
    rw [pow_succ] at hp
    nlinarith only [hp,hj.2,hlow]
  · exact h
  · have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by omega : n-1+1≤j)) hB.le
    rw [pow_succ] at hp
    nlinarith only [hp,hj.1,hupp]

/-- The ENTIRE available dyadic logarithmic grid below the physical
cofactor bound has at most `2 log x+1` bins. This bounds global location
multiplicity; it is not an assumption that all labels share one cluster. -/
theorem available_shell_count_le (I : Finset ℕ) {B x : ℝ}
    (hB : 16≤B) (hx : 1≤x) (hI : ∀ j∈I,B*(2 : ℝ)^j≤16*x) :
    (I.card : ℝ)≤2*log x+1 := by
  have hB0 : 0<B := by linarith only [hB]
  have hx0 : 0<x := (by norm_num : (0 : ℝ)<1).trans_le hx
  have hlx : 0≤log x := log_nonneg hx
  by_cases he : I=∅
  · simp only [he,Finset.card_empty,Nat.cast_zero]
    linarith only [hlx]
  obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hlarge : 1≤16*x/B := by
    apply (le_div_iff₀ hB0).mpr
    have hh := mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)) hB0.le
    nlinarith only [hh,hI j hj]
  have hgrid z (hz : z∈I) : (1 : ℝ)*2^z≤16*x/B := by
    apply (le_div_iff₀ hB0).mpr
    simpa only [one_mul,mul_comm] using hI z hz
  have hc := dyadic_owner_card_le I (by norm_num : (1 : ℝ)≤1) hlarge hgrid
  have hupper : 16*x/B≤x := (div_le_iff₀ hB0).mpr (by nlinarith only [hB,hx0])
  have hlog := div_le_div_of_nonneg_right
    (log_le_log (by positivity : 0<16*x/B) hupper)
    (log_pos (by norm_num : (1 : ℝ)<2)).le
  have hrate : log x/log 2≤2*log x := by
    apply (div_le_iff₀ (log_pos (by norm_num : (1 : ℝ)<2))).mpr
    have hh := mul_le_mul_of_nonneg_left
      (show (1/2 : ℝ)≤log 2 by linarith [log_two_gt_d9]) hlx
    nlinarith only [hh]
  linarith only [hc,hlog,hrate]

/-- An arbitrary finite prime population is covered by actual dyadic
LOGARITHMIC intervals. Overlaps are charged only in the upper bound;
no literal label is copied or deleted. -/
theorem reciprocal_mass_shell_cover (E I : Finset ℕ) (α : ℕ→ℝ)
    {B : ℝ} (hB : 5000≤B) (hα : ∀ i∈I,B≤α i)
    (hE : ∀ p∈E,p.Prime)
    (hcover : ∀ p∈E,∃ i∈I,α i<log p ∧ log p≤2*α i) :
    (∑ p∈E,(p : ℝ)⁻¹)≤(I.card : ℝ)*(log 2+1/B) := by
  have hB0 : 0<B := by linarith
  have hpoint p (hp : p∈E) :
      (p : ℝ)⁻¹≤∑ i∈I,if α i<log p ∧ log p≤2*α i then (p : ℝ)⁻¹ else 0 := by
    obtain ⟨i,hi,hpi⟩ := hcover p hp
    have hh := Finset.single_le_sum
      (fun j (_hj : j∈I) => show 0≤(if α j<log p ∧ log p≤2*α j then (p : ℝ)⁻¹ else 0) by
        split_ifs <;> positivity) hi
    simpa only [if_pos hpi] using hh
  have hh := Finset.sum_le_sum hpoint
  rw [Finset.sum_comm] at hh
  have hrow i (hi : i∈I) :
      (∑ p∈E,if α i<log p ∧ log p≤2*α i then (p : ℝ)⁻¹ else 0)≤log 2+1/B := by
    let Q := E.filter (fun p : ℕ => α i<log p ∧ log p≤2*α i)
    have hα0 : 0<α i := hB0.trans_le (hα i hi)
    have hsub : Q⊆(Finset.Ioc ⌊exp (α i)⌋₊ ⌊exp (2*α i)⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpE,hpl,hpu⟩ := Finset.mem_filter.mp hp
      have hpp := hE p hpE
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hpp⟩
      · apply (Nat.floor_lt (exp_pos _).le).mpr
        rw [← exp_log (by exact_mod_cast hpp.pos : (0 : ℝ)<p)]
        exact exp_lt_exp.mpr hpl
      · apply Nat.le_floor
        simpa only [exp_log (by exact_mod_cast hpp.pos : (0 : ℝ)<p)] using
          exp_le_exp.mpr hpu
    have ht := (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (by intro p _ _; positivity)).trans
        (prime_interval_mass_le (hB.trans (hα i hi)) (by linarith : α i≤2*α i))
    rw [show 2*α i/α i=(2 : ℝ) by field_simp] at ht
    have hb : 1/(α i)≤1/B := one_div_le_one_div_of_le hB0 (hα i hi)
    have heq : (∑ p∈E,if α i<log p ∧ log p≤2*α i then (p : ℝ)⁻¹ else 0)=
        ∑ p∈Q,(p : ℝ)⁻¹ := by rw [Finset.sum_filter]
    rw [heq]
    exact ht.trans (by linarith only [hb])
  exact hh.trans (by simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hrow)

/-- A growing union of up to `log(N+1)/8` shells has a small actual
reciprocal prime mass even when its labels have ARBITRARILY MANY factors
inside those shells. The finite prime universe is not approximated. -/
theorem dense_shell_mass_budget (E I : Finset ℕ) (α : ℕ→ℝ) (N : ℕ)
    (hB : 5000≤32*log ((N : ℝ)+1))
    (hα : ∀ i∈I,32*log ((N : ℝ)+1)≤α i)
    (hE : ∀ p∈E,p.Prime)
    (hcover : ∀ p∈E,∃ i∈I,α i<log p ∧ log p≤2*α i)
    (hcard : (I.card : ℝ)≤log ((N : ℝ)+1)/8) :
    (∑ p∈E,(p : ℝ)⁻¹)≤log ((N : ℝ)+1)/8+1/4 := by
  have hB0 : 0<32*log ((N : ℝ)+1) := by linarith
  have hh := reciprocal_mass_shell_cover E I α hB hα hE hcover
  have hl2 : log 2≤1 := by linarith [log_two_lt_d9]
  have hmain : (I.card : ℝ)*log 2≤log ((N : ℝ)+1)/8 :=
    (mul_le_mul_of_nonneg_left hl2 (by positivity)).trans (by simpa using hcard)
  have herror : (I.card : ℝ)/(32*log ((N : ℝ)+1))≤1/256 := by
    apply (div_le_iff₀ hB0).mpr
    convert hcard using 1 <;> first | rfl | ring
  have hbound : (I.card : ℝ)*(log 2+1/(32*log ((N : ℝ)+1)))≤
      log ((N : ℝ)+1)/8+1/4 := by
    rw [mul_add,mul_one_div]
    linarith only [hmain,herror]
  exact hh.trans hbound

/-- The cluster price has NO cofactor-prime count ceiling. Both missed
sign selections spend the one literal ownership boundary, and the exact
owner factorial allocation stays in the original signed prime period. -/
theorem uncapped_intermediate_period_floor (S D P Q U E : Finset ℕ)
    (N : ℕ) (e : ℝ) (A : Finset ℕ) {v y L H J B W : ℝ}
    (he : |e|=1) (hH : 10000≤H) (hNv : (N : ℝ)+2≤v)
    (hy : 54≤y) (hL : v/2≤L)
    (hB : 5000≤B) (hW : 1≤W) (hJ : 10000*W≤J) (hJH : J≤H)
    (hE : E⊆U) (hU : ∀ p∈U,p.Prime ∧ log p≤4*J)
    (hgood : ∀ p∈U\E,log p≤B ∨ J/W≤log p)
    (hS : ∀ a∈S,Squarefree a ∧ 2≤a.primeFactors.card ∧ a.primeFactors⊆U ∧
      v/4≤4*J*((a.primeFactors.card : ℝ)+3))
    (hP : ∀ a∈S,H≤v-Real.pi/y-log a)
    (howner : ∀ a∈S,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ a∈S,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(221440*gappedHeadCost*B^4*W^4*exp (4*(∑ p∈E,(p : ℝ)⁻¹))/v)*
        (amplitude N v/v)≤
      (∑ a∈S,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a))+
      (∑ n∈D\P,signedPart 1 (A∩{largestPrime n}) L y N n)+
      (∑ n∈D\Q,signedPart (-1) (A∩{largestPrime n}) L y N n) := by
  have hcount (a : ℕ) (ha : a.primeFactors⊆U) : (a.primeFactors∩E).card≤U.card :=
    Finset.card_le_card (fun _ hp => ha (Finset.mem_inter.mp hp).1)
  have hh := sparse_intermediate_period_floor S D P Q U E U.card N e A
    he hH hNv hy hL hB hW hJ hJH (by norm_num : (1 : ℝ)≤1) hE hU hgood
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.1,
      hcount a (hS a ha).2.2.1,(hS a ha).2.2.2⟩) hP howner hA
    (fun n hn => ⟨(hD n hn).1,(hD n hn).2.1,(hD n hn).2.2.1,
      (hD n hn).2.2.2.1,(hD n hn).2.2.2.2,hcount _ (hD n hn).2.2.2.2⟩)
    hpeak hsign
  simpa only [one_pow,mul_one,div_one] using hh

private theorem mass_exponential_bound {x M : ℝ} (hx : 0<x)
    (hM : M≤log x/8+1/4) : exp (4*M)≤exp 1*sqrt x := by
  have hh := exp_le_exp.mpr (show 4*M≤1+log x/2 by linarith only [hM])
  rw [exp_add] at hh
  have heq : exp (log x/2)=sqrt x := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hx]
    congr 1
    ring
  simpa only [heq] using hh

/-- One global price for ALL selected counts and owner/radial periods
with small intermediate reciprocal mass. Density in number of factors
is unrestricted; only the actual prime-universe mass is constrained. -/
theorem global_uncapped_mass_cost_le (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v : ℕ→ℝ) (E : ℕ→ℕ→Finset ℕ) {H : ℝ}
    (hH : 10000≤H) (hNv : ∀ i∈V,(N : ℝ)+2≤v i)
    (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (hM : ∀ i∈V,∀ j∈O i,(∑ p∈E i j,(p : ℝ)⁻¹)≤log ((N : ℝ)+1)/8+1/4) :
    (∑ i∈V,∑ j∈O i,
      (221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*
        exp (4*(∑ p∈E i j,(p : ℝ)⁻¹))/v i)*(amplitude N (v i)/v i))≤
      intermediateSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i) := by
  have hx : 0<(N : ℝ)+1 := by positivity
  have hpoint i (hi : i∈V) j (hj : j∈O i) :
      (221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*
        exp (4*(∑ p∈E i j,(p : ℝ)⁻¹))/v i)*(amplitude N (v i)/v i)≤
      (221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8*
        (sqrt ((N : ℝ)+1))^1/v i)*(amplitude N (v i)/v i) := by
    have hv : 0<v i := by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have he := mass_exponential_bound hx (hM i hi j hj)
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left he
        (show 0≤221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8 by positivity [gappedHeadCost_pos])) hv.le
    have ht := mul_le_mul_of_nonneg_right hh
      (div_nonneg (amplitude_nonneg N hv.le) hv.le)
    convert ht using 1 <;> first | rfl | ring
  have hh := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hpoint i hi))
  exact hh.trans (global_sparse_cost_le V O N v (fun _ _ => 1) hH (sqrt_pos.mpr hx)
    hNv hvG hO (by
      intro i _hi j _hj
      rw [log_sqrt hx.le]
      norm_num
      ring_nf
      exact le_rfl))

/-- Dense intermediate clusters, including arbitrary mixtures of counts,
obey a total signed floor in the ACTUAL radial-supply units. The shell
cover may grow; the factor count does not need to fit `log(N+1)/4`.
Complete physical fibres and disjoint spending remain explicit. -/
theorem global_dense_shell_floor (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v e : ℕ→ℝ) (J : ℕ→ℕ→ℝ)
    (S D P Q U E I : ℕ→ℕ→Finset ℕ) (α : ℕ→ℕ→ℕ→ℝ) (A : Finset ℕ)
    {H y L : ℝ} (hH : 10000≤H) (hy : 54≤y)
    (hB : 5000≤32*log ((N : ℝ)+1))
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (he : ∀ i∈V,|e i|=1) (hL : ∀ i∈V,v i/2≤L)
    (hJ : ∀ i∈V,∀ j∈O i,10000*(32*log ((N : ℝ)+1))≤J i j ∧ J i j≤H*(2 : ℝ)^j)
    (hE : ∀ i∈V,∀ j∈O i,E i j⊆U i j)
    (hU : ∀ i∈V,∀ j∈O i,∀ p∈U i j,p.Prime ∧ log p≤4*J i j)
    (hgood : ∀ i∈V,∀ j∈O i,∀ p∈U i j\E i j,
      log p≤32*log ((N : ℝ)+1) ∨ J i j/(32*log ((N : ℝ)+1))≤log p)
    (hα : ∀ i∈V,∀ j∈O i,∀ z∈I i j,32*log ((N : ℝ)+1)≤α i j z)
    (hcover : ∀ i∈V,∀ j∈O i,∀ p∈E i j,∃ z∈I i j,α i j z<log p ∧ log p≤2*α i j z)
    (hcard : ∀ i∈V,∀ j∈O i,((I i j).card : ℝ)≤log ((N : ℝ)+1)/8)
    (hS : ∀ i∈V,∀ j∈O i,∀ a∈S i j,Squarefree a ∧ 2≤a.primeFactors.card ∧
      a.primeFactors⊆U i j ∧ v i/4≤4*J i j*((a.primeFactors.card : ℝ)+3))
    (hP : ∀ i∈V,∀ j∈O i,∀ a∈S i j,H*(2 : ℝ)^j≤v i-Real.pi/y-log a)
    (howner : ∀ i∈V,∀ j∈O i,∀ a∈S i j,∀ q∈a.primeFactors,log q≤v i-Real.pi/y-log a)
    (hA : ∀ i∈V,∀ j∈O i,∀ a∈S i j,∀ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ i∈V,∀ j∈O i,∀ n∈D i j,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v i-1/16<log n ∧ log n≤v i+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U i j)
    (hpeak : ∀ i∈V,sin (y*v i)=0) (hsign : ∀ i∈V,e i*cos (y*v i)≤0) :
    -intermediateSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
      ∑ i∈V,∑ j∈O i,
        ((∑ a∈S i j,∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
          signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
          (∑ n∈D i j\P i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
          (∑ n∈D i j\Q i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
  have hrow i (hi : i∈V) j (hj : j∈O i) :
      -(221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*
        exp (4*(∑ p∈E i j,(p : ℝ)⁻¹))/v i)*(amplitude N (v i)/v i)≤
      ((∑ a∈S i j,∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
        signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
        (∑ n∈D i j\P i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
        (∑ n∈D i j\Q i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
    have hHj : 10000≤H*(2 : ℝ)^j := by
      have hh := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
      nlinarith only [hh,hH]
    have hh := uncapped_intermediate_period_floor (S i j) (D i j) (P i j) (Q i j)
      (U i j) (E i j) N (e i) A (he i hi) hHj (hNv i hi) hy (hL i hi)
      hB (by linarith : 1≤32*log ((N : ℝ)+1)) (hJ i hi j hj).1 (hJ i hi j hj).2
      (hE i hi j hj) (hU i hi j hj) (hgood i hi j hj) (hS i hi j hj)
      (hP i hi j hj) (howner i hi j hj) (hA i hi j hj) (hD i hi j hj)
      (hpeak i hi) (hsign i hi)
    convert hh using 1
    first | rfl | ring
  have hh := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hrow i hi))
  simp only [neg_mul,Finset.sum_neg_distrib] at hh
  have hc := global_uncapped_mass_cost_le V O N v E hH hNv hvG hO (by
    intro i hi j hj
    exact dense_shell_mass_budget (E i j) (I i j) (α i j) N hB (hα i hi j hj)
      (fun p hp => (hU i hi j hj p (hE i hi j hj hp)).1) (hcover i hi j hj) (hcard i hi j hj))
  simpa only [neg_mul] using (neg_le_neg hc).trans hh

/-- The ACTUAL occupied shell pattern of one literal cofactor. It is
used only to partition existing labels, with their original weights. -/
def occupiedShells (a : ℕ) (E : Finset ℕ) (bin : ℕ→ℕ) : Finset ℕ :=
  (a.primeFactors∩E).image bin

theorem occupiedShells_mono {a b : ℕ} (ha : Squarefree a) (hba : b∣a)
    (E : Finset ℕ) (bin : ℕ→ℕ) : occupiedShells b E bin⊆occupiedShells a E bin := by
  intro i hi
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_image.mpr ⟨p,Finset.mem_inter.mpr
    ⟨Nat.primeFactors_mono hba ha.ne_zero (Finset.mem_inter.mp hp).1,
      (Finset.mem_inter.mp hp).2⟩,rfl⟩

/-- Every selected original cofactor belongs to exactly ONE occupied
pattern. The formula is valid for its full complex phase or any literal
allocation/factorial weight. It does not complete prime fibres. -/
theorem sum_occupied_pattern_partition {M : Type*} [AddCommMonoid M]
    (S E I : Finset ℕ) (bin : ℕ→ℕ) (h : ℕ) (f : ℕ→M)
    (hI : ∀ a∈S,occupiedShells a E bin⊆I) :
    (∑ a∈S.filter (fun a => (occupiedShells a E bin).card≤h),f a)=
      ∑ K∈I.powerset.filter (fun K => K.card≤h),
        ∑ a∈S.filter (fun a => occupiedShells a E bin=K),f a := by
  simp only [Finset.sum_filter]
  have hswap (K : Finset ℕ) :
      (if K.card≤h then ∑ a∈S,if occupiedShells a E bin=K then f a else 0 else 0)=
      ∑ a∈S,if K.card≤h then (if occupiedShells a E bin=K then f a else 0) else 0 := by
    by_cases hK : K.card≤h <;> simp [hK]
  simp_rw [hswap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hc : (occupiedShells a E bin).card≤h
  · simp only [hc,if_true]
    have hmem : occupiedShells a E bin∈I.powerset := Finset.mem_powerset.mpr (hI a ha)
    rw [Finset.sum_eq_single (occupiedShells a E bin)]
    · simp [hc]
    · intro K _hK hneq
      simp [Ne.symm hneq]
    · exact fun h => False.elim (h hmem)
  · simp only [hc,if_false]
    symm
    apply Finset.sum_eq_zero
    intro K hK
    by_cases he : occupiedShells a E bin=K
    · rw [← he]
      simp [hc]
    · simp [he]

/-- A dyadic log shell has a finite all-count Euler price at most 32.
The number of prime factors within that shell is completely unrestricted. -/
theorem shell_exponential_price_le (E I : Finset ℕ) (α : ℕ→ℝ)
    {B : ℝ} (hB : 5000≤B) (hα : ∀ i∈I,B≤α i)
    (hE : ∀ p∈E,p.Prime)
    (hcover : ∀ p∈E,∃ i∈I,α i<log p ∧ log p≤2*α i) :
    exp (4*(∑ p∈E,(p : ℝ)⁻¹))≤(32 : ℝ)^I.card := by
  have hmass := reciprocal_mass_shell_cover E I α hB hα hE hcover
  have hl2 : (1/2 : ℝ)≤log 2 := by linarith [log_two_gt_d9]
  have hB0 : 0<B := by linarith
  have hsmall : 4/B≤log 2 := by
    have hh : 4/B≤1/2 := (div_le_iff₀ hB0).mpr (by linarith only [hB])
    exact hh.trans hl2
  have harg : 4*(∑ p∈E,(p : ℝ)⁻¹)≤(I.card : ℝ)*(5*log 2) := by
    have hh := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ)≤4 by norm_num)
    have ht := mul_le_mul_of_nonneg_left hsmall (show 0≤(I.card : ℝ) by positivity)
    calc
      _ ≤ 4*((I.card : ℝ)*(log 2+1/B)) := hh
      _ = 4*(I.card : ℝ)*log 2+(I.card : ℝ)*(4/B) := by ring
      _ ≤ 4*(I.card : ℝ)*log 2+(I.card : ℝ)*log 2 := add_le_add le_rfl ht
      _ = _ := by ring
  have hh := exp_le_exp.mpr harg
  have heq : (I.card : ℝ)*(5*log 2)=log ((32 : ℝ)^I.card) := by
    rw [log_pow,show (32 : ℝ)=2^5 by norm_num,log_pow]
    norm_num
  rw [heq,exp_log (by positivity)] at hh
  exact hh

/-- Price ALL possible occupied shell patterns together. This is not
an assumption that every label uses one common set of locations. For up
to `log x/16` occupied bins among at most `2 log x+1` available bins, the
entire weighted pattern budget costs only a square root of `x`. -/
theorem truncated_pattern_price_le (I : Finset ℕ) (h : ℕ) {x : ℝ}
    (hx : 1≤x) (hI : (I.card : ℝ)≤2*log x+1) (hh : (h : ℝ)≤log x/16) :
    (∑ K∈I.powerset.filter (fun K => K.card≤h),(32 : ℝ)^K.card)≤exp 1*sqrt x := by
  have hx0 : 0<x := (by norm_num : (0 : ℝ)<1).trans_le hx
  have hpoint K (hK : K∈I.powerset.filter (fun K => K.card≤h)) :
      (32 : ℝ)^K.card≤(1024 : ℝ)^h*(1/32 : ℝ)^K.card := by
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤1024) (Finset.mem_filter.mp hK).2)
      (show 0≤(1/32 : ℝ)^K.card by positivity)
    have heq : (1024 : ℝ)^K.card*(1/32 : ℝ)^K.card=(32 : ℝ)^K.card := by
      rw [← mul_pow]
      norm_num
    rw [heq] at hp
    exact hp
  have hfull : (∑ K∈I.powerset.filter (fun K => K.card≤h),(1/32 : ℝ)^K.card)≤
      exp ((I.card : ℝ)/32) := by
    have hp : (∑ K∈I.powerset,(1/32 : ℝ)^K.card)=∏ i∈I,(1+(1/32 : ℝ)) := by
      simpa only [Finset.prod_const] using (Finset.prod_one_add I (f := fun _ => (1/32 : ℝ))).symm
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro K _ _; positivity) :
      (∑ K∈I.powerset.filter (fun K => K.card≤h),(1/32 : ℝ)^K.card)≤
        ∑ K∈I.powerset,(1/32 : ℝ)^K.card)
    rw [hp] at hh
    have he := Real.prod_one_add_le_exp_sum I (fun _ => show (0 : ℝ)≤1/32 by norm_num)
    simp only [Finset.sum_const,nsmul_eq_mul] at he
    exact hh.trans (by convert he using 1 <;> first | rfl | ring)
  have hsum := (Finset.sum_le_sum hpoint).trans
    (by simpa only [← Finset.mul_sum] using (mul_le_mul_of_nonneg_left hfull
      (show 0≤(1024 : ℝ)^h by positivity)))
  have hlog : log 1024≤7 := by
    rw [show (1024 : ℝ)=2^10 by norm_num,log_pow]
    norm_num
    linarith [log_two_lt_d9]
  have harg : (h : ℝ)*log 1024+(I.card : ℝ)/32≤1+log x/2 := by
    have ht := mul_le_mul_of_nonneg_left hlog (show 0≤(h : ℝ) by positivity)
    linarith only [ht,hI,hh]
  have hexp := exp_le_exp.mpr harg
  rw [exp_add,show (h : ℝ)*log 1024=log ((1024 : ℝ)^h) by rw [log_pow],
    exp_log (by positivity),exp_add] at hexp
  have heq : exp (log x/2)=sqrt x := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hx0]
    congr 1
    ring
  rw [heq] at hexp
  exact hsum.trans hexp

/-- A single total price including the number of ALL possible shell
locations, as well as every selected owner scale and radial period.
Different labels may occupy different intermediate-shell patterns.
Their total prime count remains unrestricted. -/
theorem global_all_pattern_cost_le (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N h : ℕ) (v : ℕ→ℝ) (I : ℕ→ℕ→Finset ℕ)
    (E : ℕ→ℕ→Finset ℕ→Finset ℕ) (α : ℕ→ℕ→ℕ→ℝ) {H : ℝ}
    (hH : 10000≤H) (hB : 5000≤32*log ((N : ℝ)+1))
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (hI : ∀ i∈V,∀ j∈O i,((I i j).card : ℝ)≤2*log ((N : ℝ)+1)+1)
    (hh : (h : ℝ)≤log ((N : ℝ)+1)/16)
    (hα : ∀ i∈V,∀ j∈O i,∀ z∈I i j,32*log ((N : ℝ)+1)≤α i j z)
    (hE : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),∀ p∈E i j K,p.Prime)
    (hcover : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ p∈E i j K,∃ z∈K,α i j z<log p ∧ log p≤2*α i j z) :
    (∑ i∈V,∑ j∈O i,∑ K∈(I i j).powerset.filter (fun K => K.card≤h),
      (221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*
        exp (4*(∑ p∈E i j K,(p : ℝ)⁻¹))/v i)*(amplitude N (v i)/v i))≤
      intermediateSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i) := by
  have hx : 0<(N : ℝ)+1 := by positivity
  have hrow i (hi : i∈V) j (hj : j∈O i) :
      (∑ K∈(I i j).powerset.filter (fun K => K.card≤h),
        (221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*
          exp (4*(∑ p∈E i j K,(p : ℝ)⁻¹))/v i)*(amplitude N (v i)/v i))≤
      (221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8*
        (sqrt ((N : ℝ)+1))^1/v i)*(amplitude N (v i)/v i) := by
    have hv : 0<v i := by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have hC : 0≤221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8/v i*(amplitude N (v i)/v i) :=
      by positivity [gappedHeadCost_pos,amplitude_nonneg N hv.le]
    have hpoint K (hK : K∈(I i j).powerset.filter (fun K => K.card≤h)) :
        exp (4*(∑ p∈E i j K,(p : ℝ)⁻¹))≤(32 : ℝ)^K.card :=
      shell_exponential_price_le (E i j K) K (α i j) hB
        (fun z hz => hα i hi j hj z (Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1 hz))
        (hE i hi j hj K hK) (hcover i hi j hj K hK)
    have hp := (Finset.sum_le_sum hpoint).trans
      (truncated_pattern_price_le (I i j) h (by linarith [Nat.cast_nonneg (α := ℝ) N]) (hI i hi j hj) hh)
    have ht := mul_le_mul_of_nonneg_left hp hC
    rw [Finset.mul_sum] at ht
    convert ht using 1 <;> first | rfl | (apply Finset.sum_congr rfl; intro K _; ring) | ring
  have ht := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hrow i hi))
  exact ht.trans (global_sparse_cost_le V O N v (fun _ _ => 1) hH (sqrt_pos.mpr hx)
    hNv hvG hO (by
      intro i _hi j _hj
      rw [log_sqrt hx.le]
      norm_num
      ring_nf
      exact le_rfl))

/-- Apply the ALL-pattern cost to the original signed prime periods and
their literal ownership clips. No signed cancellation hypothesis is
inserted: each row follows from `uncapped_intermediate_period_floor`.
An exact occupied-pattern partition prevents spending the same label
twice when these sets are supplied from the existing carrier. -/
theorem global_all_pattern_floor (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N h : ℕ) (v e : ℕ→ℝ) (J : ℕ→ℕ→ℝ) (I : ℕ→ℕ→Finset ℕ)
    (S D P Q U E : ℕ→ℕ→Finset ℕ→Finset ℕ) (α : ℕ→ℕ→ℕ→ℝ) (A : Finset ℕ)
    {H y L : ℝ} (hH : 10000≤H) (hy : 54≤y) (hB : 5000≤32*log ((N : ℝ)+1))
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (he : ∀ i∈V,|e i|=1) (hL : ∀ i∈V,v i/2≤L)
    (hJ : ∀ i∈V,∀ j∈O i,10000*(32*log ((N : ℝ)+1))≤J i j ∧ J i j≤H*(2 : ℝ)^j)
    (hI : ∀ i∈V,∀ j∈O i,((I i j).card : ℝ)≤2*log ((N : ℝ)+1)+1)
    (hh : (h : ℝ)≤log ((N : ℝ)+1)/16)
    (hα : ∀ i∈V,∀ j∈O i,∀ z∈I i j,32*log ((N : ℝ)+1)≤α i j z)
    (hE : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),E i j K⊆U i j K)
    (hU : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ p∈U i j K,p.Prime ∧ log p≤4*J i j)
    (hgood : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ p∈U i j K\E i j K,log p≤32*log ((N : ℝ)+1) ∨ J i j/(32*log ((N : ℝ)+1))≤log p)
    (hcover : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ p∈E i j K,∃ z∈K,α i j z<log p ∧ log p≤2*α i j z)
    (hS : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ a∈S i j K,Squarefree a ∧ 2≤a.primeFactors.card ∧ a.primeFactors⊆U i j K ∧
        v i/4≤4*J i j*((a.primeFactors.card : ℝ)+3))
    (hP : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ a∈S i j K,H*(2 : ℝ)^j≤v i-Real.pi/y-log a)
    (howner : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ a∈S i j K,∀ q∈a.primeFactors,log q≤v i-Real.pi/y-log a)
    (hA : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ a∈S i j K,∀ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ i∈V,∀ j∈O i,∀ K∈(I i j).powerset.filter (fun K => K.card≤h),
      ∀ n∈D i j K,Squarefree n ∧ 3≤n.primeFactors.card ∧
        (v i-1/16<log n ∧ log n≤v i+1/16) ∧
        (∃ q∈(n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
        (n/largestPrime n).primeFactors⊆U i j K)
    (hpeak : ∀ i∈V,sin (y*v i)=0) (hsign : ∀ i∈V,e i*cos (y*v i)≤0) :
    -intermediateSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
      ∑ i∈V,∑ j∈O i,∑ K∈(I i j).powerset.filter (fun K => K.card≤h),
        ((∑ a∈S i j K,∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
          signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
          (∑ n∈D i j K\P i j K,signedPart 1 (A∩{largestPrime n}) L y N n)+
          (∑ n∈D i j K\Q i j K,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
  have hrow i (hi : i∈V) j (hj : j∈O i) K
      (hK : K∈(I i j).powerset.filter (fun K => K.card≤h)) :
      -(221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*
        exp (4*(∑ p∈E i j K,(p : ℝ)⁻¹))/v i)*(amplitude N (v i)/v i)≤
      ((∑ a∈S i j K,∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
        signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
        (∑ n∈D i j K\P i j K,signedPart 1 (A∩{largestPrime n}) L y N n)+
        (∑ n∈D i j K\Q i j K,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
    have hHj : 10000≤H*(2 : ℝ)^j := by
      have ht := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
      nlinarith only [ht,hH]
    have ht := uncapped_intermediate_period_floor (S i j K) (D i j K) (P i j K) (Q i j K)
      (U i j K) (E i j K) N (e i) A (he i hi) hHj (hNv i hi) hy (hL i hi)
      hB (by linarith : 1≤32*log ((N : ℝ)+1)) (hJ i hi j hj).1 (hJ i hi j hj).2
      (hE i hi j hj K hK) (hU i hi j hj K hK) (hgood i hi j hj K hK)
      (hS i hi j hj K hK) (hP i hi j hj K hK) (howner i hi j hj K hK)
      (hA i hi j hj K hK) (hD i hi j hj K hK) (hpeak i hi) (hsign i hi)
    convert ht using 1
    first | rfl | ring
  have ht := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum
    (fun j hj => Finset.sum_le_sum (hrow i hi j hj)))
  simp only [neg_mul,Finset.sum_neg_distrib] at ht
  have hc := global_all_pattern_cost_le V O N h v I E α hH hB hNv hvG hO hI hh hα
    (fun i hi j hj K hK p hp => (hU i hi j hj K hK p (hE i hi j hj K hK hp)).1) hcover
  simpa only [neg_mul] using (neg_le_neg hc).trans ht

end RiemannGaussian.ZetaRieszDenseShellCost
