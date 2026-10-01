/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityLayerCost

/-!
# Signed period prices with intermediate cofactor-prime scales retained

The old gapped population excluded every intermediate prime. Here those
primes stay in the literal cofactor, with their exact phase and allocation.
An auxiliary positive marker prices only their count AFTER the complete
signed owner period has been summed. The cofactor count itself is unrestricted.
All prices use the actual `amplitude/v` radial-supply unit.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszIntermediateScaleCost
open ZetaRieszParityLayerCost ZetaRieszBroadOwnerPeriodFloor
open ZetaRieszSmallCofactorCancellation ZetaRieszSmallOwnerBoundary
open ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod
open ZetaRieszPrimeEndpoint ZetaRieszAllowancePrimeBoxes
open ZetaRieszOwnerCurvatureFloor ZetaRieszJointOwnerFibreFloor
open ZetaRieszClippedOwnerPeriodFloor ZetaRieszLogShellPeriodFloor
open ZetaRieszStaggeredFloor

set_option maxHeartbeats 800000

/-- A positive prime marker is only a population-budget device. It is
not inserted in the literal arithmetic carrier. -/
def markerWeight (E : Finset ℕ) (t : ℝ) (p : ℕ) : ℝ :=
  4*(p : ℝ)⁻¹*(if p∈E then t⁻¹ else 1)

private theorem product_weight_eq {a : ℕ} (ha : Squarefree a)
    (E : Finset ℕ) (t : ℝ) :
    (∏ p∈a.primeFactors,markerWeight E t p)=
      ((4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹)*
        (t⁻¹)^(a.primeFactors∩E).card := by
  simp only [markerWeight]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.prod_inv_distrib,← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree ha,Finset.prod_ite]
  have heq : a.primeFactors.filter (fun p => p∈E)=a.primeFactors∩E := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_inter]
  simp only [Finset.prod_const,one_pow,mul_one,heq]

/-- Exact squarefree symmetry and the INTERMEDIATE-prime count give
one marked Euler budget. No fixed total prime-count ceiling is imposed. -/
theorem intermediate_population_mass_le (D U E : Finset ℕ) (m : ℕ) {t : ℝ}
    (ht : 1≤t) (hE : E⊆U)
    (hD : ∀ a∈D,Squarefree a ∧ a.primeFactors⊆U ∧ (a.primeFactors∩E).card ≤ m) :
    (∑ a∈D,(4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹)≤
      t^m*exp (4*(∑ p∈U\E,(p : ℝ)⁻¹)+4*(∑ p∈E,(p : ℝ)⁻¹)/t) := by
  have ht0 : 0<t := by linarith
  have hinj : Set.InjOn Nat.primeFactors (D : Set ℕ) := by
    intro a ha b hb he
    rw [← Nat.prod_primeFactors_of_squarefree (hD a ha).1,
      ← Nat.prod_primeFactors_of_squarefree (hD b hb).1,he]
  have hpoint a (ha : a∈D) :
      (4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹≤
        t^m*(∏ p∈a.primeFactors,markerWeight E t p) := by
    have hh := pow_le_pow_right₀ ht (hD a ha).2.2
    have hc : 0≤(4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹ := by positivity
    have hh' := mul_le_mul_of_nonneg_right hh
      (mul_nonneg hc (pow_nonneg (inv_nonneg.mpr ht0.le) (a.primeFactors∩E).card))
    rw [product_weight_eq (hD a ha).1 E t]
    have heq : t^(a.primeFactors∩E).card*
        (((4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹)*(t⁻¹)^(a.primeFactors∩E).card)=
        (4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹ := by
      rw [inv_pow]
      field_simp
    rw [heq] at hh'
    exact hh'
  have hprod : (∑ a∈D,∏ p∈a.primeFactors,markerWeight E t p)≤
      exp (∑ p∈U,markerWeight E t p) := by
    calc
      _ = ∑ V∈D.image Nat.primeFactors,∏ p∈V,markerWeight E t p :=
        (Finset.sum_image hinj).symm
      _ ≤ ∑ V∈U.powerset,∏ p∈V,markerWeight E t p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro V hV
          obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hV
          exact Finset.mem_powerset.mpr (hD a ha).2.1
        · intro V _ _
          apply Finset.prod_nonneg
          intro p _
          unfold markerWeight
          split_ifs <;> positivity
      _ = ∏ p∈U,(1+markerWeight E t p) := (Finset.prod_one_add U).symm
      _ ≤ _ := Real.prod_one_add_le_exp_sum U (fun p => by
        unfold markerWeight
        split_ifs <;> positivity)
  have hsum : (∑ p∈U,markerWeight E t p)=
      4*(∑ p∈U\E,(p : ℝ)⁻¹)+4*(∑ p∈E,(p : ℝ)⁻¹)/t := by
    rw [← Finset.sum_inter_add_sum_sdiff U E (markerWeight E t),
      Finset.inter_eq_right.mpr hE]
    have hh : (∑ p∈E,markerWeight E t p)=∑ p∈E,4*(p : ℝ)⁻¹*t⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [markerWeight,if_pos hp]
    have he : (∑ p∈U\E,markerWeight E t p)=∑ p∈U\E,4*(p : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [markerWeight,if_neg (Finset.mem_sdiff.mp hp).2,mul_one]
    rw [hh,he]
    simp only [← Finset.mul_sum,← Finset.sum_mul,div_eq_mul_inv]
    ring
  have hp := mul_le_mul_of_nonneg_left hprod (show 0≤t^m by positivity)
  rw [Finset.mul_sum] at hp
  have hh := (Finset.sum_le_sum hpoint).trans hp
  simpa only [hsum] using hh

/-- Intermediate primes may occur at EVERY scale in the formerly
excluded gap. Their marker cost multiplies the existing signed-period
population price; it does not enlarge the arithmetic small-prime head. -/
theorem sparse_intermediate_mass_le (D U E : Finset ℕ) (m : ℕ) {B J W t : ℝ}
    (hB : 5000≤B) (hW : 1≤W) (hJ : 10000*W≤J) (ht : 1≤t)
    (hE : E⊆U) (hEmass : 4*(∑ p∈E,(p : ℝ)⁻¹)≤t)
    (hU : ∀ p∈U\E,p.Prime ∧ log p≤4*J ∧ (log p≤B ∨ J/W≤log p))
    (hD : ∀ a∈D,Squarefree a ∧ a.primeFactors⊆U ∧ (a.primeFactors∩E).card ≤ m) :
    (∑ a∈D,(4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹)≤
      (gappedHeadCost*exp 1)*B^4*W^4*t^m := by
  have ht0 : 0<t := by linarith
  have hm : 4*(∑ p∈E,(p : ℝ)⁻¹)/t≤1 := (div_le_one ht0).mpr hEmass
  have hmass := intermediate_population_mass_le D U E m ht hE hD
  rw [exp_add] at hmass
  have hh := mul_le_mul
    (gapped_count_exponential_le (U\E) hB hW hJ hU)
    (exp_le_exp.mpr hm) (exp_pos _).le (by positivity [gappedHeadCost_pos])
  exact hmass.trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

/-- Without capping the reciprocal mass of intermediate primes, the
entire price retains its marked exponential. This form permits a fixed
marker and a number of intermediate factors proportional to `log N`. -/
theorem general_intermediate_mass_le (D U E : Finset ℕ) (m : ℕ) {B J W t : ℝ}
    (hB : 5000≤B) (hW : 1≤W) (hJ : 10000*W≤J) (ht : 1≤t)
    (hE : E⊆U)
    (hU : ∀ p∈U\E,p.Prime ∧ log p≤4*J ∧ (log p≤B ∨ J/W≤log p))
    (hD : ∀ a∈D,Squarefree a ∧ a.primeFactors⊆U ∧ (a.primeFactors∩E).card ≤ m) :
    (∑ a∈D,(4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹)≤
      gappedHeadCost*B^4*W^4*t^m*exp (4*(∑ p∈E,(p : ℝ)⁻¹)/t) := by
  have hh := intermediate_population_mass_le D U E m ht hE hD
  rw [exp_add] at hh
  have hp := mul_le_mul_of_nonneg_right
    (gapped_count_exponential_le (U\E) hB hW hJ hU)
    (exp_pos (4*(∑ p∈E,(p : ℝ)⁻¹)/t)).le
  exact hh.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring))

private theorem count_marker {v J : ℝ} (hJ : 0<J) {k : ℕ}
    (hc : v≤4*J*((k : ℝ)+3)) :
    (2 : ℝ)^k≤8*exp (-v/(8*J))*(4 : ℝ)^k := by
  have hlog : (1/2 : ℝ)≤log 2 := by linarith [log_two_gt_d9]
  have harg : v/(8*J)≤((k : ℝ)+3)*log 2 := by
    have hh : v/(8*J)≤((k : ℝ)+3)/2 :=
      (div_le_iff₀ (show 0<8*J by positivity)).mpr (by nlinarith only [hc])
    have ht := mul_le_mul_of_nonneg_left hlog (by positivity : 0≤(k : ℝ)+3)
    nlinarith only [hh,ht]
  have hh := exp_le_exp.mpr harg
  rw [show ((k : ℝ)+3)*log 2=log ((2 : ℝ)^(k+3)) by
    rw [log_pow,Nat.cast_add,Nat.cast_ofNat],exp_log (by positivity),pow_add] at hh
  have hm := mul_le_mul_of_nonneg_right hh (exp_pos (-v/(8*J))).le
  rw [← exp_add,show v/(8*J)+(-v/(8*J))=0 by ring,exp_zero] at hm
  have hp := mul_le_mul_of_nonneg_right hm (by positivity : 0≤(2 : ℝ)^k)
  simpa only [one_mul] using hp.trans_eq (by
    rw [show (2 : ℝ)^k*2^3*exp (-v/(8*J))*2^k=
      8*exp (-v/(8*J))*(2^k*2^k) by norm_num; ring,
      ← mul_pow]
    norm_num)

/-- The complete literal owner-prime periods are bounded over a finite
cofactor population BEFORE its intermediate scales are priced. Every
count, phase, hinge and owner factorial order remains in the left sum. -/
theorem retained_population_floor (S : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    {v y L H J P : ℝ} (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hJ : 0<J) (hJH : J≤H)
    (hS : ∀ a∈S,Squarefree a ∧ 2≤a.primeFactors.card ∧
      v/4≤4*J*((a.primeFactors.card : ℝ)+3) ∧ log a.minFac≤4*H)
    (hP : ∀ a∈S,H≤v-Real.pi/y-log a)
    (howner : ∀ a∈S,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ a∈S,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0)
    (hmass : (∑ a∈S,(4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹)≤P) :
    -(123136*P/v)*(amplitude N v/v)≤
      ∑ a∈S,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a) := by
  have hv : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hH0 : 0<H := by linarith
  have hf : 0≤amplitude N v/v := div_nonneg (amplitude_nonneg N hv.le) hv.le
  have hrow a (ha : a∈S) :
      -(123136/v)*(amplitude N v/v)*((4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹)≤
        ∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
          signedPart e (A∩{largestPrime (p*a)}) L y N (p*a) := by
    have hs := hS a ha
    have ht := count_marker hJ (show v/4≤4*J*((a.primeFactors.card : ℝ)+3) from hs.2.2.1)
    have heq : -(v/4)/(8*J)=-v/(32*J) := by ring
    rw [heq] at ht
    have hc := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right ht hH0.le) (show (0 : ℝ)≤481 by norm_num)
    have ho := mul_le_mul_of_nonneg_left (tilted_separated_owner_price_le hv hJ hJH)
      (show 0≤3848*(4 : ℝ)^a.primeFactors.card by positivity)
    have hcost : 481*(2 : ℝ)^a.primeFactors.card/H≤123136/v*(4 : ℝ)^a.primeFactors.card := by
      have hh := hc.trans (by convert ho using 1; first | rfl | ring)
      convert hh using 1 <;> first | rfl | ring
    have hp := mul_le_mul_of_nonneg_left hcost
      (show 0≤(amplitude N v/v)*(a : ℝ)⁻¹ by positivity [amplitude_nonneg N hv.le])
    have hh := retained_owner_row_floor hs.2.1 he A hH hNv hy hL hs.1 rfl hs.2.2.2
      (hP a ha) (howner a ha) (hA a ha) hpeak hsign
    have hc' : -(123136/v)*(amplitude N v/v)*((4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹)≤
        -(amplitude N v/v)*(481*(2 : ℝ)^a.primeFactors.card/H)*(a : ℝ)⁻¹ := by
      calc
        _ = -((amplitude N v/v)*(a : ℝ)⁻¹*(123136/v*(4 : ℝ)^a.primeFactors.card)) := by ring
        _ ≤ -((amplitude N v/v)*(a : ℝ)⁻¹*(481*(2 : ℝ)^a.primeFactors.card/H)) := neg_le_neg hp
        _ = _ := by ring
    exact hc'.trans hh
  have hh := Finset.sum_le_sum hrow
  rw [← Finset.mul_sum] at hh
  have hp := mul_le_mul_of_nonneg_left hmass
    (show 0≤(123136/v)*(amplitude N v/v) by positivity [amplitude_nonneg N hv.le])
  have hp' : -(123136*P/v)*(amplitude N v/v)≤
      -(123136/v)*(amplitude N v/v)*
        (∑ a∈S,(4 : ℝ)^a.primeFactors.card*(a : ℝ)⁻¹) := by
    convert neg_le_neg hp using 1 <;> first | rfl | ring
  have hlow := hp'.trans hh
  exact hlow

private theorem response_count_bound (k : ℕ) : responseConstant k≤6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ)≤(2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    exact_mod_cast hh.trans (Nat.pow_le_pow_right (by norm_num : 1≤(2 : ℕ)) (by omega : k-2≤k))
  have h0 := hp 0
  have h1 := hp 1
  unfold responseConstant
  nlinarith only [h0,h1,one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := k)]

/-- Removing the actual near-tied pair cannot increase the number of
intermediate primes. This is a literal divisibility fact, not a mask
completion or an assumption about the distribution of prime factors. -/
theorem intermediate_count_mono {a b : ℕ} (hs : Squarefree a) (hba : b∣a)
    (E : Finset ℕ) : (b.primeFactors∩E).card≤(a.primeFactors∩E).card := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hpE⟩ := Finset.mem_inter.mp hp
  exact Finset.mem_inter.mpr ⟨Nat.primeFactors_mono hba hs.ne_zero hp,hpE⟩

/-- The same intermediate-prime budget pays ALL literal ownership
clips. Their original varying allocation and phase remain in each atom;
the two near-tied prime reciprocals are priced before the count sum. -/
theorem sparse_intermediate_clipped_norm_bound (A : ℕ→Finset ℕ)
    (D U E : Finset ℕ) (m N : ℕ) (y : ℝ) {v L H J B W t : ℝ}
    (hH : 10000≤H) (hv : 0<v) (hNv : (N : ℝ)+1≤v) (hL : v/2≤L)
    (hB : 5000≤B) (hW : 1≤W) (hJ : 10000*W≤J) (hJH : J≤H)
    (ht : 1≤t) (hE : E⊆U)
    (hU : ∀ p∈U,p.Prime ∧ log p≤4*J)
    (hgood : ∀ p∈U\E,log p≤B ∨ J/W≤log p)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U ∧
      ((n/largestPrime n).primeFactors∩E).card ≤ m) :
    (∑ n∈D,‖ZetaRieszJointAllocation.residualCoefficient (A n) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤
      (98304*gappedHeadCost*B^4*W^4*t^m*exp (4*(∑ p∈E,(p : ℝ)⁻¹)/t)/v)*
        (amplitude N v/v) := by
  have hH0 : 0<H := by linarith
  have hJ0 : 0<J := by nlinarith [hJ,hW]
  let R := (U.powerset.image (fun V : Finset ℕ => V.prod id)).filter (fun b : ℕ =>
    Squarefree b ∧ 0<b.primeFactors.card ∧ b.primeFactors⊆U ∧
      log b≤v-2*H+1/16 ∧ (b.primeFactors∩E).card ≤ m ∧
      v≤4*J*((b.primeFactors.card : ℝ)+3))
  let V := R.sigma (fun b => (ZetaRieszOwnerTieFloor.pairWindow v b).product
    (ZetaRieszOwnerTieFloor.pairWindow v b))
  let label := fun x : Σ _ : ℕ, ℕ×ℕ => x.2.1*(x.2.2*x.1)
  let f := fun n => if n∈D then
    ‖ZetaRieszJointAllocation.residualCoefficient (A n) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ else 0
  let C := fun b : ℕ => 2*amplitude N v*responseConstant (b.primeFactors.card+2)/L
  have hL0 : 0<L := by linarith
  have hf (n : ℕ) : 0≤f n := by dsimp [f]; split_ifs <;> positivity
  have hcover : D⊆V.image label := by
    intro n hn
    obtain ⟨hs,hc,hT,hclip,hsub,hcnt⟩ := hD n hn
    let k := n.primeFactors.card-2
    have hk : 0<k := by dsimp [k]; omega
    have hc' : n.primeFactors.card=k+2 := by dsimp [k]; omega
    obtain ⟨b,q,he,hb,hbc,hbsub,hcap,hpw,hqw⟩ :=
      broad_clipped_cofactor_cover hs hc' hk U hT hclip hsub
    have hba : b∣n/largestPrime n := by
      have hh := canonical_owner_data hs hc
      have hx : q*b=n/largestPrime n := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh.1.ne_zero)
        exact he.symm.trans hh.2.1.symm
      rw [← hx]
      exact dvd_mul_left b q
    have hcount := clipped_count_constraint hs hc
      (by nlinarith [hJ,hW] : 1≤J) hT.1
      (by obtain ⟨q,hq,hqH,hqgap⟩ := hclip; exact ⟨q,hq,hJH.trans hqH,hqgap⟩)
      (fun p hp => (hU p (hsub hp)).2)
    have hgap := (intermediate_count_mono (canonical_owner_data hs hc).2.2.1 hba E).trans hcnt
    have hbm : b∈R := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨b.primeFactors,Finset.mem_powerset.mpr hbsub,
        Nat.prod_primeFactors_of_squarefree hb⟩,hb,by omega,hbsub,hcap,hgap,?_⟩
      simpa only [hbc,k] using hcount
    exact Finset.mem_image.mpr ⟨⟨b,(largestPrime n,q)⟩,Finset.mem_sigma.mpr
      ⟨hbm,Finset.mem_product.mpr ⟨hpw,hqw⟩⟩,he.symm⟩
  have hfirst : (∑ n∈D,‖ZetaRieszJointAllocation.residualCoefficient (A n) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤∑ x∈V,f (label x) := by
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => hf n)).trans
      (Finset.sum_image_le_of_nonneg (fun n _ => hf n))
    simpa only [f,if_true,Finset.sum_congr rfl (fun n hn => if_pos hn)] using hh
  have hpoint (b : ℕ) (hb : b∈R) (p : ℕ)
      (hp : p∈ZetaRieszOwnerTieFloor.pairWindow v b) (q : ℕ)
      (hq : q∈ZetaRieszOwnerTieFloor.pairWindow v b) :
      f (p*(q*b))≤C b*(4*H*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹ := by
    have hs := (Finset.mem_filter.mp hb).2
    have hb1 : b≠1 := by intro hh; simp [hh] at hs
    have hm : log b.minFac≤4*H := ((hU _ (hs.2.2.1
      ((Nat.minFac_prime hb1).mem_primeFactors (Nat.minFac_dvd b) hs.1.ne_zero))).2).trans
        (by linarith)
    by_cases hn : p*(q*b)∈D
    · have hd := hD _ hn
      have hT : |log (p*(q*b) : ℕ)-v|≤1 :=
        abs_le.mpr ⟨by linarith [hd.2.2.1.1],by linarith [hd.2.2.1.2]⟩
      have hcard : (p*(q*b)).primeFactors.card=b.primeFactors.card+2 := by
        have hp' := (logPrimes_bounds hp).1
        have hq' := (logPrimes_bounds hq).1
        have hqb : Squarefree (q*b) := hd.1.of_mul_right
        have hpn : p∉(q*b).primeFactors := fun hh =>
          (hp'.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hd.1))
            (Nat.dvd_of_mem_primeFactors hh)
        have hqn : q∉b.primeFactors := fun hh =>
          (hq'.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hqb))
            (Nat.dvd_of_mem_primeFactors hh)
        rw [Nat.primeFactors_mul hp'.ne_zero hqb.ne_zero,hp'.primeFactors,
          Finset.singleton_union,Finset.card_insert_of_notMem hpn,
          Nat.primeFactors_mul hq'.ne_zero hs.1.ne_zero,hq'.primeFactors,
          Finset.singleton_union,Finset.card_insert_of_notMem hqn]
      have hh := ZetaRieszOwnerTieFloor.boundary_atom_norm (A (p*(q*b))) y hv hNv hL0
        hd.1 hcard hb1 (dvd_mul_of_dvd_right (dvd_mul_left b q) p) hT
      dsimp only [f]
      rw [if_pos hn]
      have hle := mul_le_mul_of_nonneg_left hm
        (by dsimp [C]; positivity [responseConstant_pos (b.primeFactors.card+2),amplitude_nonneg N hv.le] :
          0≤C b*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)
      have heq : C b*(log b.minFac/(p*(q*b) : ℕ))=
          (C b*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)*log b.minFac := by
        simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
        ring
      change _≤C b*(log b.minFac/(p*(q*b) : ℕ)) at hh
      rw [heq] at hh
      exact hh.trans (by convert hle using 1; ring)
    · dsimp only [f]
      rw [if_neg hn]
      dsimp [C]
      positivity [responseConstant_pos (b.primeFactors.card+2),amplitude_nonneg N hv.le]
  have hrow (b : ℕ) (hb : b∈R) :
      (∑ pq∈(ZetaRieszOwnerTieFloor.pairWindow v b).product
        (ZetaRieszOwnerTieFloor.pairWindow v b),f (pq.1*(pq.2*b)))≤
        (98304/v)*(amplitude N v/v)*((4 : ℝ)^b.primeFactors.card*(b : ℝ)⁻¹) := by
    have hs := (Finset.mem_filter.mp hb).2
    rw [Finset.product_eq_sprod,Finset.sum_product]
    have hh := Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
      (fun p hp => Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
        (fun q hq => hpoint b hb p hp q hq))
    have hm := shell_pairWindow_mass hH hs.2.2.2.1
    have hsq := pow_le_pow_left₀ (by positivity) hm 2
    have heq : (∑ p∈ZetaRieszOwnerTieFloor.pairWindow v b,
        ∑ q∈ZetaRieszOwnerTieFloor.pairWindow v b,
          C b*(4*H*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹)=
        (C b*(4*H*(b : ℝ)⁻¹))*
          (∑ p∈ZetaRieszOwnerTieFloor.pairWindow v b,(p : ℝ)⁻¹)^2 := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,← Finset.mul_sum,pow_two]
      ring
    rw [heq] at hh
    have hpre : C b≤4*(amplitude N v/v)*responseConstant (b.primeFactors.card+2) := by
      dsimp [C]
      have hh := div_le_div_of_nonneg_left
        (by positivity [amplitude_nonneg N hv.le,responseConstant_pos (b.primeFactors.card+2)] :
          0≤2*amplitude N v*responseConstant (b.primeFactors.card+2))
        (by positivity : 0<v/2) hL
      convert hh using 1 <;> first | rfl | ring
    have hrc : responseConstant (b.primeFactors.card+2)≤24*(2 : ℝ)^b.primeFactors.card := by
      have hh := response_count_bound (b.primeFactors.card+2)
      norm_num [pow_add] at hh
      convert hh using 1; ring
    have ht := count_marker hJ0 hs.2.2.2.2.2
    have ho : exp (-v/(8*J))/H≤8/v :=
      (div_le_div_of_nonneg_left (exp_pos _).le hJ0 hJH).trans (tilted_owner_price_le hv hJ0)
    have hcost : (C b*(4*H*(b : ℝ)⁻¹))*(4/H^2)≤
        (98304/v)*(amplitude N v/v)*((4 : ℝ)^b.primeFactors.card*(b : ℝ)⁻¹) := by
      have hc := mul_le_mul_of_nonneg_right hpre
        (show 0≤(4*H*(b : ℝ)⁻¹)*(4/H^2) by positivity)
      have hr := mul_le_mul_of_nonneg_left (hrc.trans
        (mul_le_mul_of_nonneg_left ht (show (0 : ℝ)≤24 by norm_num)))
        (show 0≤64*(amplitude N v/v)*(b : ℝ)⁻¹/H by positivity [amplitude_nonneg N hv.le])
      have hp := mul_le_mul_of_nonneg_left ho
        (show 0≤12288*(amplitude N v/v)*((4 : ℝ)^b.primeFactors.card*(b : ℝ)⁻¹)
          by positivity [amplitude_nonneg N hv.le])
      have hp' := hc.trans (by
        have hr' := hr.trans (by convert hp using 1; first | rfl | ring)
        convert hr' using 1; first | rfl | (field_simp; ring))
      convert hp' using 1 <;> first | rfl | ring
    have hsq' : (∑ p∈ZetaRieszOwnerTieFloor.pairWindow v b,(p : ℝ)⁻¹)^2≤4/H^2 := by
      convert hsq using 1 <;> first | rfl | (field_simp; ring)
    exact hh.trans ((mul_le_mul_of_nonneg_left hsq'
      (by dsimp [C]; positivity [amplitude_nonneg N hv.le,responseConstant_pos (b.primeFactors.card+2)])).trans hcost)
  have hmass := general_intermediate_mass_le R U E m hB hW hJ ht hE
    (fun p hp => ⟨(hU p (Finset.mem_sdiff.mp hp).1).1,
      (hU p (Finset.mem_sdiff.mp hp).1).2,hgood p hp⟩)
    (fun b hb => by
      have hs := (Finset.mem_filter.mp hb).2
      exact ⟨hs.1,hs.2.2.1,hs.2.2.2.2.1⟩)
  have hh : (∑ x∈V,f (label x))≤(98304/v)*(amplitude N v/v)*
      (∑ b∈R,(4 : ℝ)^b.primeFactors.card*(b : ℝ)⁻¹) := by
    change (∑ x∈R.sigma _,f (label x))≤_
    rw [Finset.sum_sigma]
    simpa only [← Finset.mul_sum] using Finset.sum_le_sum hrow
  have hp := mul_le_mul_of_nonneg_left hmass
    (show 0≤(98304/v)*(amplitude N v/v) by positivity [amplitude_nonneg N hv.le])
  exact hfirst.trans (hh.trans (by convert hp using 1; first | rfl | ring))

private theorem missed_parts_floor (A : ℕ→Finset ℕ) (D P Q : Finset ℕ)
    (L y : ℝ) (N : ℕ) :
    -(∑ n∈D,‖ZetaRieszJointAllocation.residualCoefficient (A n) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤
      (∑ n∈D\P,signedPart 1 (A n) L y N n)+
      (∑ n∈D\Q,signedPart (-1) (A n) L y N n) := by
  have h₁ := Finset.sum_le_sum_of_subset_of_nonneg
    (show D\P⊆D from Finset.sdiff_subset) (fun n _ _ => abs_nonneg (signedPart 1 (A n) L y N n))
  have h₂ := Finset.sum_le_sum_of_subset_of_nonneg
    (show D\Q⊆D from Finset.sdiff_subset) (fun n _ _ => abs_nonneg (signedPart (-1) (A n) L y N n))
  have hab := Finset.sum_le_sum (fun n (_hn : n∈D) =>
    (ZetaRieszOwnerTieFloor.signedParts_abs_eq (A n) L y N n).le.trans (Complex.abs_re_le_norm _))
  rw [Finset.sum_add_distrib] at hab
  have hl₁ := Finset.sum_le_sum (fun n (_hn : n∈D\P) => neg_abs_le (signedPart 1 (A n) L y N n))
  have hl₂ := Finset.sum_le_sum (fun n (_hn : n∈D\Q) => neg_abs_le (signedPart (-1) (A n) L y N n))
  simp only [Finset.sum_neg_distrib] at hl₁ hl₂
  linarith only [h₁,h₂,hab,hl₁,hl₂]

/-- A floor for the combined original signed periods and their actual
ownership clips. Intermediate primes are retained at arbitrary scales;
only their NUMBER enters the population price, after signed cancellation. -/
theorem sparse_intermediate_period_floor (S D P Q U E : Finset ℕ)
    (m N : ℕ) (e : ℝ) (A : Finset ℕ) {v y L H J B W t : ℝ}
    (he : |e|=1) (hH : 10000≤H) (hNv : (N : ℝ)+2≤v)
    (hy : 54≤y) (hL : v/2≤L)
    (hB : 5000≤B) (hW : 1≤W) (hJ : 10000*W≤J) (hJH : J≤H)
    (ht : 1≤t) (hE : E⊆U)
    (hU : ∀ p∈U,p.Prime ∧ log p≤4*J)
    (hgood : ∀ p∈U\E,log p≤B ∨ J/W≤log p)
    (hS : ∀ a∈S,Squarefree a ∧ 2≤a.primeFactors.card ∧ a.primeFactors⊆U ∧
      (a.primeFactors∩E).card ≤ m ∧ v/4≤4*J*((a.primeFactors.card : ℝ)+3))
    (hP : ∀ a∈S,H≤v-Real.pi/y-log a)
    (howner : ∀ a∈S,∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)
    (hA : ∀ a∈S,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ n∈D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U ∧
      ((n/largestPrime n).primeFactors∩E).card ≤ m)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(221440*gappedHeadCost*B^4*W^4*t^m*exp (4*(∑ p∈E,(p : ℝ)⁻¹)/t)/v)*
        (amplitude N v/v)≤
      (∑ a∈S,∑ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A∩{largestPrime (p*a)}) L y N (p*a))+
      (∑ n∈D\P,signedPart 1 (A∩{largestPrime n}) L y N n)+
      (∑ n∈D\Q,signedPart (-1) (A∩{largestPrime n}) L y N n) := by
  have hJ0 : 0<J := by nlinarith [hJ,hW]
  have hv : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hmass := general_intermediate_mass_le S U E m hB hW hJ ht hE
    (fun p hp => ⟨(hU p (Finset.mem_sdiff.mp hp).1).1,
      (hU p (Finset.mem_sdiff.mp hp).1).2,hgood p hp⟩)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2.1,(hS a ha).2.2.2.1⟩)
  have hmin a (ha : a∈S) : log a.minFac≤4*H := by
    have hs := hS a ha
    have ha1 : a≠1 := by intro h; simp [h] at hs
    have hmem := (Nat.minFac_prime ha1).mem_primeFactors (Nat.minFac_dvd a) hs.1.ne_zero
    exact ((hU _ (hs.2.2.1 hmem)).2).trans (by linarith)
  have hmain := retained_population_floor S N e A he (by linarith) hNv hy hL hJ0 hJH
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2.2,hmin a ha⟩)
    hP howner hA hpeak hsign hmass
  have hnorm := sparse_intermediate_clipped_norm_bound (fun n => A∩{largestPrime n})
    D U E m N y hH hv (by linarith) hL hB hW hJ hJH ht hE hU hgood hD
  have hrest := (neg_le_neg hnorm).trans
    (missed_parts_floor (fun n => A∩{largestPrime n}) D P Q L y N)
  have hh := add_le_add hmain hrest
  convert! hh using 1 <;> ring

/-- The exact intermediate gap is only a partition of the actual
prime universe. In particular its complement satisfies the earlier
head/shell condition without discarding ANY intermediate factor. -/
theorem exact_gap_complement (U : Finset ℕ) (B J W : ℝ) :
    ∀ p∈U\U.filter (fun p : ℕ => B<log p ∧ log p<J/W),
      log p≤B ∨ J/W≤log p := by
  intro p hp
  obtain ⟨hpU,hpg⟩ := Finset.mem_sdiff.mp hp
  have hh : ¬(B<log p ∧ log p<J/W) := fun h => hpg (Finset.mem_filter.mpr ⟨hpU,h⟩)
  by_cases h : log p≤B
  · exact Or.inl h
  · exact Or.inr (le_of_not_gt (fun hg => hh ⟨lt_of_not_ge h,hg⟩))

/-- A logarithmically growing intermediate-count allowance fits inside
the square-root radial price. This has NO fixed total count limit. -/
theorem marker_power_le_sqrt {x t : ℝ} (hx : 0<x) (ht : 0<t) (m : ℕ)
    (hm : 2*(m : ℝ)*log t≤log x) : t^m ≤ sqrt x := by
  apply le_sqrt_of_sq_le
  have hh := exp_le_exp.mpr hm
  rw [show 2*(m : ℝ)*log t=log ((t^m)^2) by
    rw [log_pow,log_pow]; norm_num; ring,
    exp_log (by positivity),exp_log hx] at hh
  exact hh

/-- The new total population cost, in the same radial-supply units as
the existing genuine positive reserve. The fixed arithmetic head is
unevaluated; this theorem does not provide an effective starting order. -/
def intermediateSupplyPrice (N : ℕ) : ℝ :=
  221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8*
    (1+log (4*((N : ℝ)+1))/log 2)/sqrt ((N : ℝ)+1)

/-- Aggregate ALL selected intermediate-count layers, owner scales and
radial periods. The costs are those of the proved literal signed-period
floor and its one original ownership boundary, not raw atom norms. -/
theorem global_sparse_cost_le (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v : ℕ→ℝ) (m : ℕ→ℕ→ℕ)
    {H t : ℝ} (hH : 10000≤H) (ht : 0<t)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i)
    (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (hcount : ∀ i∈V,∀ j∈O i,2*(m i j : ℝ)*log t≤log ((N : ℝ)+1)) :
    (∑ i∈V,∑ j∈O i,
      (221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8*t^(m i j)/v i)*
        (amplitude N (v i)/v i))≤
      intermediateSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i) := by
  have hn : 0<(N : ℝ)+1 := by positivity
  have hsqrt : 0<sqrt ((N : ℝ)+1) := sqrt_pos.mpr hn
  have hC : 0≤221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8 := by
    positivity [gappedHeadCost_pos]
  have hrow i (hi : i∈V) :
      (∑ j∈O i,(221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8*t^(m i j)/v i)*
        (amplitude N (v i)/v i))≤
      intermediateSupplyPrice N*(amplitude N (v i)/v i) := by
    have hv : 0<v i := by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have hf : 0≤amplitude N (v i)/v i := div_nonneg (amplitude_nonneg N hv.le) hv.le
    have hprice j (hj : j∈O i) :
        (221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8*t^(m i j)/v i)*
          (amplitude N (v i)/v i)≤
        (221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8/sqrt ((N : ℝ)+1))*
          (amplitude N (v i)/v i) := by
      have hp := mul_le_mul_of_nonneg_left
        (marker_power_le_sqrt hn ht (m i j) (hcount i hi j hj)) hC
      have hh := (div_le_div_of_nonneg_right hp hv.le).trans
        (div_le_div_of_nonneg_left (mul_nonneg hC hsqrt.le) hn (by linarith [hNv i hi]))
      have hsq := sq_sqrt hn.le
      have heq : 221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8*
          sqrt ((N : ℝ)+1)/((N : ℝ)+1)=
          221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8/sqrt ((N : ℝ)+1) := by
        apply (div_eq_div_iff hn.ne' hsqrt.ne').mpr
        calc
          _ = (221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8)*
              (sqrt ((N : ℝ)+1))^2 := by ring
          _ = _ := by rw [hsq]
      rw [heq] at hh
      exact mul_le_mul_of_nonneg_right hh hf
    have hh := Finset.sum_le_sum hprice
    rw [Finset.sum_const,nsmul_eq_mul] at hh
    have hc := dyadic_owner_card_le (O i) (by linarith : 1≤H)
      (by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N] : 1≤v i) (hO i hi)
    have hlg := div_le_div_of_nonneg_right (log_le_log hv (hvG i hi))
      (log_pos (by norm_num : (1 : ℝ)<2)).le
    have hcg : ((O i).card : ℝ)≤1+log (4*((N : ℝ)+1))/log 2 := by linarith only [hc,hlg]
    have hp := mul_le_mul_of_nonneg_right hcg
      (show 0≤(221440*(gappedHeadCost*exp 1)*(32*log ((N : ℝ)+1))^8/sqrt ((N : ℝ)+1))*
        (amplitude N (v i)/v i) by positivity [gappedHeadCost_pos,amplitude_nonneg N hv.le])
    exact hh.trans (by unfold intermediateSupplyPrice; convert hp using 1; first | rfl | ring)
  have hh := Finset.sum_le_sum hrow
  simpa only [Finset.mul_sum] using hh

private theorem pow_log_div_sqrt_tendsto (d : ℕ) :
    Tendsto (fun N : ℕ => (log ((N : ℝ)+1))^d/sqrt ((N : ℝ)+1)) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp : Tendsto (fun N : ℕ => (log ((N : ℝ)+1))^(2*d)/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul,add_zero] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 (2*d) one_ne_zero).comp hn
  have hh := hp.sqrt
  simp only [sqrt_zero] at hh
  convert hh using 1
  funext N
  rw [show 2*d=d*2 by omega,pow_mul,sqrt_div (sq_nonneg _),sqrt_sq_eq_abs,
    abs_of_nonneg (pow_nonneg (log_nonneg (by
      have h := Nat.cast_nonneg (α := ℝ) N
      linarith : 1≤(N : ℝ)+1)) d)]

/-- The enlarged population has total relative cost
`O(log^9(N)/sqrt(N))` in CORRECT supply units, including the owner clips. -/
theorem tendsto_intermediateSupplyPrice : Tendsto intermediateSupplyPrice atTop (𝓝 0) := by
  have ht := (((pow_log_div_sqrt_tendsto 8).const_mul (1+log 4/log 2)).add
    ((pow_log_div_sqrt_tendsto 9).const_mul (log 2)⁻¹)).const_mul
      (221440*(gappedHeadCost*exp 1)*(32 : ℝ)^8)
  convert ht using 1
  · funext N
    unfold intermediateSupplyPrice
    rw [log_mul (by norm_num : (4 : ℝ)≠0) (by positivity : (N : ℝ)+1≠0)]
    simp only [div_eq_mul_inv,mul_pow]
    ring
  · ring

theorem eventually_intermediateSupplyPrice_lt {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,intermediateSupplyPrice N<ε :=
  tendsto_intermediateSupplyPrice.eventually (gt_mem_nhds hε)

/-- Fixed finite arithmetic head for the optimized intermediate marker.
It is not a numerical certificate or an additional positive reserve. -/
def intermediateHeadFactor : ℝ :=
  exp ((smallPrimeHeadMass+log 16+1/5000)/4)

theorem intermediateHeadFactor_pos : 0 < intermediateHeadFactor := exp_pos _

/-- Marker SIXTEEN prices up to `log(x)/4` intermediate factors, even
when their reciprocal prime mass grows like `log(x)`. It gives a fixed
`x^(-1/20)` saving without enlarging the small-prime head or taking any
absolute norm of the selected carrier before its signed prime period. -/
theorem quarter_count_marker_bound (E : Finset ℕ) (m : ℕ) {x J : ℝ}
    (hx : 1≤x) (hJ : 5000≤J) (hJx : J≤4*x)
    (hE : ∀ p∈E,p.Prime ∧ log p≤4*J)
    (hm : (m : ℝ)≤log x/4) :
    (16 : ℝ)^m*exp ((∑ p∈E,(p : ℝ)⁻¹)/4)/x≤
      intermediateHeadFactor*exp (-log x/20) := by
  have hx0 : 0<x := (by norm_num : (0 : ℝ)<1).trans_le hx
  have hJ0 : 0<J := by linarith
  have hmass := whole_prime_mass_le E hJ hE
  have hlog : log (4*J/5000)≤log 16+log x := by
    have hh := log_le_log (show 0<4*J/5000 by positivity)
      (show 4*J/5000≤16*x by nlinarith)
    rw [log_mul (by norm_num : (16 : ℝ)≠0) hx0.ne'] at hh
    exact hh
  have hmass' : (∑ p∈E,(p : ℝ)⁻¹) ≤ smallPrimeHeadMass+log 16+log x+1/5000 :=
    hmass.trans (by linarith only [hlog])
  have hlog16 : log 16≤14/5 := by
    have hh : log 2≤7/10 := by linarith [log_two_lt_d9]
    rw [show (16 : ℝ)=2^4 by norm_num,log_pow]
    norm_num
    linarith only [hh]
  have hmg := (mul_le_mul_of_nonneg_left hlog16 (Nat.cast_nonneg (α := ℝ) m)).trans
    (mul_le_mul_of_nonneg_right hm (by norm_num : (0 : ℝ)≤14/5))
  have harg : (m : ℝ)*log 16+(∑ p∈E,(p : ℝ)⁻¹)/4-log x≤
      (smallPrimeHeadMass+log 16+1/5000)/4-log x/20 := by
    linarith only [hmass',hmg]
  have hh := exp_le_exp.mpr harg
  rw [show (m : ℝ)*log 16+(∑ p∈E,(p : ℝ)⁻¹)/4-log x=
      log ((16 : ℝ)^m)+(∑ p∈E,(p : ℝ)⁻¹)/4-log x by rw [log_pow],
    exp_sub,exp_add,exp_log (by positivity),exp_log hx0,
    exp_sub] at hh
  simpa only [intermediateHeadFactor,div_eq_mul_inv,neg_mul,exp_neg] using hh

/-- The new intermediate count ceiling grows, rather than freezing the
unmatched population at one or a few exceptional prime factors. -/
def intermediateCountCeiling (N : ℕ) : ℕ := ⌊log ((N : ℝ)+1)/4⌋₊

theorem intermediateCountCeiling_bound (N : ℕ) :
    (intermediateCountCeiling N : ℝ)≤log ((N : ℝ)+1)/4 := by
  apply Nat.floor_le
  exact div_nonneg (log_nonneg (by
    have h := Nat.cast_nonneg (α := ℝ) N
    linarith)) (by norm_num)

theorem intermediateCountCeiling_tendsto : Tendsto intermediateCountCeiling atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := (tendsto_log_atTop.comp hn).atTop_div_const (by norm_num : (0 : ℝ)<4)
  filter_upwards [hl.eventually_ge_atTop (m : ℝ)] with N hN
  exact Nat.le_floor hN

/-- Total marked-population price in the actual radial-supply units,
including every selected count, owner scale and ownership boundary. -/
def quarterCountSupplyPrice (N : ℕ) : ℝ :=
  221440*gappedHeadCost*intermediateHeadFactor*(32*log ((N : ℝ)+1))^8*
    (1+log (4*((N : ℝ)+1))/log 2)*exp (-log ((N : ℝ)+1)/20)

/-- ONE total cost for every selected count/parity layer, owner scale
and radial period with at most `log(N+1)/4` intermediate factors. The
prime reciprocal mass is derived from the actual finite universe; no
unproved cancellation hypothesis or density transport is inserted. -/
theorem global_quarter_count_cost_le (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v : ℕ→ℝ) (J : ℕ→ℕ→ℝ) (E : ℕ→ℕ→Finset ℕ) (m : ℕ→ℕ→ℕ)
    {H : ℝ} (hH : 10000≤H)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i)
    (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (hJ : ∀ i∈V,∀ j∈O i,5000≤J i j ∧ J i j≤v i)
    (hE : ∀ i∈V,∀ j∈O i,∀ p∈E i j,p.Prime ∧ log p≤4*J i j)
    (hcount : ∀ i∈V,∀ j∈O i,(m i j : ℝ)≤log ((N : ℝ)+1)/4) :
    (∑ i∈V,∑ j∈O i,
      (221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*(16 : ℝ)^(m i j)*
        exp ((∑ p∈E i j,(p : ℝ)⁻¹)/4)/v i)*(amplitude N (v i)/v i))≤
      quarterCountSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i) := by
  have hx : 1≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hn : 0<(N : ℝ)+1 := by positivity
  have hC : 0≤221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8 := by
    positivity [gappedHeadCost_pos]
  have hrow i (hi : i∈V) :
      (∑ j∈O i,(221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*(16 : ℝ)^(m i j)*
        exp ((∑ p∈E i j,(p : ℝ)⁻¹)/4)/v i)*(amplitude N (v i)/v i))≤
        quarterCountSupplyPrice N*(amplitude N (v i)/v i) := by
    have hv : 0<v i := by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have hf : 0≤amplitude N (v i)/v i := div_nonneg (amplitude_nonneg N hv.le) hv.le
    have hpoint j (hj : j∈O i) :
        (221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*(16 : ℝ)^(m i j)*
          exp ((∑ p∈E i j,(p : ℝ)⁻¹)/4)/v i)*(amplitude N (v i)/v i)≤
        (221440*gappedHeadCost*intermediateHeadFactor*(32*log ((N : ℝ)+1))^8*
          exp (-log ((N : ℝ)+1)/20))*(amplitude N (v i)/v i) := by
      have hmarker := quarter_count_marker_bound (E i j) (m i j) hx (hJ i hi j hj).1
        ((hJ i hi j hj).2.trans (hvG i hi)) (hE i hi j hj) (hcount i hi j hj)
      have hd : (16 : ℝ)^(m i j)*exp ((∑ p∈E i j,(p : ℝ)⁻¹)/4)/v i≤
          (16 : ℝ)^(m i j)*exp ((∑ p∈E i j,(p : ℝ)⁻¹)/4)/((N : ℝ)+1) := div_le_div_of_nonneg_left
        (show 0≤(16 : ℝ)^(m i j)*exp ((∑ p∈E i j,(p : ℝ)⁻¹)/4) by positivity)
        hn (by linarith [hNv i hi])
      have hh := mul_le_mul_of_nonneg_left (hd.trans hmarker) hC
      have hh' := mul_le_mul_of_nonneg_right hh hf
      convert hh' using 1 <;> first | rfl | ring
    have hh := Finset.sum_le_sum hpoint
    rw [Finset.sum_const,nsmul_eq_mul] at hh
    have hc := dyadic_owner_card_le (O i) (by linarith : 1≤H)
      (by linarith [hNv i hi,Nat.cast_nonneg (α := ℝ) N] : 1≤v i) (hO i hi)
    have hlg := div_le_div_of_nonneg_right (log_le_log hv (hvG i hi))
      (log_pos (by norm_num : (1 : ℝ)<2)).le
    have hcg : ((O i).card : ℝ)≤1+log (4*((N : ℝ)+1))/log 2 := by linarith only [hc,hlg]
    have hp := mul_le_mul_of_nonneg_right hcg
      (show 0≤(221440*gappedHeadCost*intermediateHeadFactor*(32*log ((N : ℝ)+1))^8*
        exp (-log ((N : ℝ)+1)/20))*(amplitude N (v i)/v i) by
          positivity [gappedHeadCost_pos,intermediateHeadFactor_pos,amplitude_nonneg N hv.le])
    exact hh.trans (by unfold quarterCountSupplyPrice; convert hp using 1; first | rfl | ring)
  have hh := Finset.sum_le_sum hrow
  simpa only [Finset.mul_sum] using hh

/-- The total marker-16 cost tends to zero relative to the same positive
radial supply, at the explicit rate `polylog(N)*N^(-1/20)`. This is a
population cost, NOT an absolute source-scale estimate for the carrier. -/
theorem tendsto_quarterCountSupplyPrice : Tendsto quarterCountSupplyPrice atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := tendsto_log_atTop.comp hn
  have hp (d : ℕ) : Tendsto (fun N : ℕ => (log ((N : ℝ)+1))^d*
      exp (-log ((N : ℝ)+1)/20)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) (1/20)
      (by norm_num)).comp hl
    simpa only [Function.comp_def,rpow_natCast,neg_mul,mul_neg,one_mul,div_eq_mul_inv,mul_comm] using hh
  have ht := (((hp 8).const_mul (1+log 4/log 2)).add
    ((hp 9).const_mul (log 2)⁻¹)).const_mul
      (221440*gappedHeadCost*intermediateHeadFactor*(32 : ℝ)^8)
  convert ht using 1
  · funext N
    unfold quarterCountSupplyPrice
    rw [log_mul (by norm_num : (4 : ℝ)≠0) (by positivity : (N : ℝ)+1≠0)]
    simp only [div_eq_mul_inv,mul_pow]
    ring
  · ring

theorem eventually_quarterCountSupplyPrice_lt {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,quarterCountSupplyPrice N<ε :=
  tendsto_quarterCountSupplyPrice.eventually (gt_mem_nhds hε)

/-- The numerical total-cost theorem applied to the LITERAL joined
periods and ownership clips, over every selected cofactor count and
radial/owner scale. The displayed masks are geometric support facts;
there is no assumed signed estimate. Unselected dense-gap populations
and any incomplete physical prime fibres remain outside this theorem. -/
theorem global_quarter_count_floor (V : Finset ℕ) (O : ℕ→Finset ℕ)
    (N : ℕ) (v e : ℕ→ℝ) (J : ℕ→ℕ→ℝ)
    (S D P Q U E : ℕ→ℕ→Finset ℕ) (m : ℕ→ℕ→ℕ) (A : Finset ℕ)
    {H y L : ℝ} (hH : 10000≤H) (hy : 54≤y)
    (hB : 5000≤32*log ((N : ℝ)+1))
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i)
    (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,H*(2 : ℝ)^j≤v i)
    (he : ∀ i∈V,|e i|=1) (hL : ∀ i∈V,v i/2≤L)
    (hJ : ∀ i∈V,∀ j∈O i,10000*(32*log ((N : ℝ)+1))≤J i j ∧ J i j≤H*(2 : ℝ)^j)
    (hE : ∀ i∈V,∀ j∈O i,E i j⊆U i j)
    (hU : ∀ i∈V,∀ j∈O i,∀ p∈U i j,p.Prime ∧ log p≤4*J i j)
    (hgood : ∀ i∈V,∀ j∈O i,∀ p∈U i j\E i j,
      log p≤32*log ((N : ℝ)+1) ∨ J i j/(32*log ((N : ℝ)+1))≤log p)
    (hcount : ∀ i∈V,∀ j∈O i,(m i j : ℝ)≤log ((N : ℝ)+1)/4)
    (hS : ∀ i∈V,∀ j∈O i,∀ a∈S i j,Squarefree a ∧ 2≤a.primeFactors.card ∧
      a.primeFactors⊆U i j ∧ (a.primeFactors∩E i j).card ≤ m i j ∧
      v i/4≤4*J i j*((a.primeFactors.card : ℝ)+3))
    (hP : ∀ i∈V,∀ j∈O i,∀ a∈S i j,H*(2 : ℝ)^j≤v i-Real.pi/y-log a)
    (howner : ∀ i∈V,∀ j∈O i,∀ a∈S i j,∀ q∈a.primeFactors,log q≤v i-Real.pi/y-log a)
    (hA : ∀ i∈V,∀ j∈O i,∀ a∈S i j,∀ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),p∈A)
    (hD : ∀ i∈V,∀ j∈O i,∀ n∈D i j,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v i-1/16<log n ∧ log n≤v i+1/16) ∧
      (∃ q∈(n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors⊆U i j ∧
      ((n/largestPrime n).primeFactors∩E i j).card ≤ m i j)
    (hpeak : ∀ i∈V,sin (y*v i)=0) (hsign : ∀ i∈V,e i*cos (y*v i)≤0) :
    -quarterCountSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
      ∑ i∈V,∑ j∈O i,
        ((∑ a∈S i j,∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
          signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
          (∑ n∈D i j\P i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
          (∑ n∈D i j\Q i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
  have hrow i (hi : i∈V) j (hj : j∈O i) :
      -(221440*gappedHeadCost*(32*log ((N : ℝ)+1))^8*(16 : ℝ)^(m i j)*
        exp ((∑ p∈E i j,(p : ℝ)⁻¹)/4)/v i)*(amplitude N (v i)/v i)≤
      ((∑ a∈S i j,∑ p∈logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
        signedPart (e i) (A∩{largestPrime (p*a)}) L y N (p*a))+
        (∑ n∈D i j\P i j,signedPart 1 (A∩{largestPrime n}) L y N n)+
        (∑ n∈D i j\Q i j,signedPart (-1) (A∩{largestPrime n}) L y N n)) := by
    have hHj : 10000≤H*(2 : ℝ)^j := by
      have hh := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
      nlinarith only [hh,hH]
    have hh := sparse_intermediate_period_floor (S i j) (D i j) (P i j) (Q i j)
      (U i j) (E i j) (m i j) N (e i) A (he i hi) hHj (hNv i hi) hy (hL i hi)
      hB (by linarith : 1≤32*log ((N : ℝ)+1)) (hJ i hi j hj).1 (hJ i hi j hj).2
      (by norm_num : (1 : ℝ)≤16) (hE i hi j hj) (hU i hi j hj) (hgood i hi j hj)
      (hS i hi j hj) (hP i hi j hj) (howner i hi j hj) (hA i hi j hj)
      (hD i hi j hj) (hpeak i hi) (hsign i hi)
    rw [show 4*(∑ p∈E i j,(p : ℝ)⁻¹)/16=(∑ p∈E i j,(p : ℝ)⁻¹)/4 by ring] at hh
    convert hh using 1
    first | rfl | ring
  have hh := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hrow i hi))
  simp only [neg_mul,Finset.sum_neg_distrib] at hh
  have hc := global_quarter_count_cost_le V O N v J E m hH hNv hvG hO
    (fun i hi j hj => ⟨by linarith [(hJ i hi j hj).1],(hJ i hi j hj).2.trans (hO i hi j hj)⟩)
    (fun i hi j hj p hp => hU i hi j hj p (hE i hi j hj hp)) hcount
  have hf := (neg_le_neg hc).trans hh
  simpa only [neg_mul] using hf

/-- An already proved disjoint positive reserve can pay this total cost
by any fixed fraction eventually. No new reserve is manufactured here,
and compatibility with earlier floor credits must still be supplied. -/
theorem quarter_cost_paid_by_reserve (N : ℕ) (V : Finset ℕ) (v : ℕ→ℝ)
    {κ ε T : ℝ} (hε : 0≤ε) (hv : ∀ i∈V,0<v i)
    (hprice : quarterCountSupplyPrice N≤ε*κ)
    (hreserve : κ*(∑ i∈V,amplitude N (v i)/v i)≤T) :
    quarterCountSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤ε*T := by
  have hs : 0≤∑ i∈V,amplitude N (v i)/v i :=
    Finset.sum_nonneg (fun i hi => div_nonneg (amplitude_nonneg N (hv i hi).le) (hv i hi).le)
  have hh := mul_le_mul_of_nonneg_right hprice hs
  have ht := mul_le_mul_of_nonneg_left hreserve hε
  exact hh.trans (by simpa only [mul_assoc] using ht)

/-- Simply extending the fixed-marker price to a dense intermediate
layer does not pay the whole remainder. At `m >= log(N+1)` its positive
price already grows linearly, before owner/radial multiplicity. This is
an audit of this allowance, NOT a no-go for further signed cancellation. -/
theorem dense_marker_price_lower (N m : ℕ) {v B W M : ℝ} (hv : 0<v)
    (hvN : v≤4*((N : ℝ)+1)) (hB : 1≤B) (hW : 1≤W) (hM : 0≤M)
    (hm : log ((N : ℝ)+1)≤(m : ℝ)) :
    55360*gappedHeadCost*((N : ℝ)+1)≤
      221440*gappedHeadCost*B^4*W^4*(16 : ℝ)^m*exp (M/4)/v := by
  have hn : 0<(N : ℝ)+1 := by positivity
  have hl16 : (2 : ℝ)≤log 16 := by
    rw [show (16 : ℝ)=2^4 by norm_num,log_pow]
    norm_num
    linarith [log_two_gt_d9]
  have hmg : 2*log ((N : ℝ)+1)≤(m : ℝ)*log 16 := by
    have hh := mul_le_mul_of_nonneg_left hl16 (Nat.cast_nonneg (α := ℝ) m)
    linarith only [hh,hm]
  have hp : ((N : ℝ)+1)^2≤(16 : ℝ)^m := by
    have hh := exp_le_exp.mpr hmg
    rw [show 2*log ((N : ℝ)+1)=log (((N : ℝ)+1)^2) by rw [log_pow]; norm_num,
      show (m : ℝ)*log 16=log ((16 : ℝ)^m) by rw [log_pow],
      exp_log (by positivity),exp_log (by positivity)] at hh
    exact hh
  have he : 1≤exp (M/4) := one_le_exp_iff.mpr (by positivity)
  have hb : 1≤B^4*W^4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) (one_le_pow₀ hW)
  have hh : ((N : ℝ)+1)^2≤B^4*W^4*(16 : ℝ)^m*exp (M/4) :=
    (hp.trans (le_mul_of_one_le_left (by positivity) hb)).trans
      (le_mul_of_one_le_right (by positivity) he)
  apply (le_div_iff₀ hv).mpr
  have hc := mul_le_mul_of_nonneg_left hvN
    (show 0≤55360*gappedHeadCost*((N : ℝ)+1) by positivity [gappedHeadCost_pos])
  have ht := mul_le_mul_of_nonneg_left hh (show 0≤221440*gappedHeadCost by positivity [gappedHeadCost_pos])
  exact hc.trans (by convert ht using 1 <;> first | rfl | ring)

/-- Retuning the positive marker cannot cure a dense population whose
actual reciprocal intermediate-prime mass is at least half `log x`.
This is a quantitative statement about the allowance, not a lower bound
on the signed carrier. Neither mass nor density is assumed implicitly. -/
theorem dense_every_marker_budget_lower {x t M : ℝ} (m : ℕ)
    (hx : 1≤x) (ht : 1≤t) (hm : log x≤(m : ℝ))
    (hM : log x/2≤M) :
    exp (3*log x/2)≤t^m*exp (4*M/t) := by
  have hx0 : 0<x := (by norm_num : (0 : ℝ)<1).trans_le hx
  have ht0 : 0<t := (by norm_num : (0 : ℝ)<1).trans_le ht
  have hlx : 0≤log x := log_nonneg hx
  have hlt : 0≤log t := log_nonneg ht
  have hl2 : (1/2 : ℝ)≤log 2 := by linarith [log_two_gt_d9]
  have hlog := log_le_sub_one_of_pos (show 0<2/t by positivity)
  rw [log_div (by norm_num : (2 : ℝ)≠0) ht0.ne'] at hlog
  have hprice : (3/2 : ℝ)≤log t+2/t := by linarith only [hlog,hl2]
  have hcount := mul_le_mul_of_nonneg_right hm hlt
  have hmass := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hM (show (0 : ℝ)≤4 by norm_num)) ht0.le
  have hboth := mul_le_mul_of_nonneg_left hprice hlx
  have harg : 3*log x/2≤(m : ℝ)*log t+4*M/t := by
    calc
      _ = log x*(3/2) := by ring
      _ ≤ log x*(log t+2/t) := hboth
      _ = log x*log t+4*(log x/2)/t := by ring
      _ ≤ _ := add_le_add hcount hmass
  have hh := exp_le_exp.mpr harg
  rw [exp_add,show (m : ℝ)*log t=log (t^m) by rw [log_pow],
    exp_log (by positivity)] at hh
  exact hh

/-- Even the optimally retuned positive marker costs at least a square
root of the radial scale on this dense population, before owner-scale
multiplicity. The displayed mass lower bound is essential. A new signed
cross-label cancellation can still improve the actual carrier. -/
theorem dense_every_marker_price_lower (N m : ℕ) {v B W M t : ℝ}
    (hv : 0<v) (hvN : v≤4*((N : ℝ)+1)) (hB : 1≤B) (hW : 1≤W)
    (ht : 1≤t) (hm : log ((N : ℝ)+1)≤(m : ℝ))
    (hM : log ((N : ℝ)+1)/2≤M) :
    55360*gappedHeadCost*exp (log ((N : ℝ)+1)/2)≤
      221440*gappedHeadCost*B^4*W^4*t^m*exp (4*M/t)/v := by
  have hx : 1≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hx0 : 0<(N : ℝ)+1 := by positivity
  have hp := dense_every_marker_budget_lower m hx ht hm hM
  rw [show 3*log ((N : ℝ)+1)/2=log ((N : ℝ)+1)+log ((N : ℝ)+1)/2 by ring,
    exp_add,exp_log hx0] at hp
  have hb : 1≤B^4*W^4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) (one_le_pow₀ hW)
  have hh : ((N : ℝ)+1)*exp (log ((N : ℝ)+1)/2)≤
      B^4*W^4*t^m*exp (4*M/t) :=
    hp.trans (by
      have hh := le_mul_of_one_le_left (show 0≤t^m*exp (4*M/t) by positivity) hb
      convert hh using 1
      first | rfl | ring)
  apply (le_div_iff₀ hv).mpr
  have hc := mul_le_mul_of_nonneg_left hvN
    (show 0≤55360*gappedHeadCost*exp (log ((N : ℝ)+1)/2) by positivity [gappedHeadCost_pos])
  have ht' := mul_le_mul_of_nonneg_left hh
    (show 0≤221440*gappedHeadCost by positivity [gappedHeadCost_pos])
  exact hc.trans (by convert ht' using 1 <;> first | rfl | ring)

end RiemannGaussian.ZetaRieszIntermediateScaleCost
