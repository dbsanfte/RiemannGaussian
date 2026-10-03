/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWeightedZeroFloor

/-!
# Cancel complete affine tails inside every native label before pricing

The same rank-two divisor cancellation applies even when a label has a
nonzero whole Riesz response. Select only COMPLETE canonical-pair blocks
whose least divisor is beyond the physical hinge. They have exactly zero
pairing with the original corrected profile. Their coefficients may depend
on the literal label, while every original phase/mask/factorial allocation
remains in the carrier. All previous corrections and paid rows stay joined.
The resulting signed whole-floor comparison adds no funding/error cost;
the numerical cofinal bound is still open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszClosedTailFloor
open ZetaRieszCutoffPeriodFloor ZetaRieszCenteredPrimeEnergy
open ZetaRieszPaidIncidenceFloor ZetaRieszZeroResponseFloor ZetaRieszWeightedZeroFloor
open ZetaRieszShortDivisorCancellation ZetaRieszComplexProjection
open ZetaRieszCofactorPhaseEnergy ZetaRieszJointPrimeEnergy
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket

/-- Only complete canonical least-pair blocks ABOVE the original hinge.
This selects original divisor coordinates even for nonzero-response labels. -/
def tailIndices (D n : ℕ) : Finset (ℕ×ℕ) :=
  ((n/leastPairBlock n).divisors.filter (fun d=>D≤d)).product
    (leastPairBlock n).divisors

/-- Original divisor incidences, once each; no prime or cofactor is
completed. Their product coordinate is the original divisor itself. -/
def tailDivisors (D n : ℕ) : Finset ℕ :=
  (tailIndices D n).image (fun de=>de.1*de.2)

theorem tailIndices_injective {n : ℕ} (hs : Squarefree n)
    (hc : 2≤n.primeFactors.card) (D : ℕ) :
    Set.InjOn (fun de : ℕ×ℕ=>de.1*de.2) (tailIndices D n : Set (ℕ×ℕ)) := by
  have hr := (leastPairBlock_data hs hc).1
  have he : n/leastPairBlock n*leastPairBlock n=n := Nat.div_mul_cancel hr
  have hp := Nat.coprime_of_squarefree_mul (he.symm ▸ hs)
  apply hp.mul_injOn_divisors.mono
  intro de hde
  obtain ⟨hd,he⟩ := Finset.mem_product.mp hde
  exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hd).1,he⟩

theorem tailDivisors_subset {n : ℕ} (hs : Squarefree n)
    (hc : 2≤n.primeFactors.card) (D : ℕ) : tailDivisors D n⊆n.divisors := by
  intro l hl
  obtain ⟨⟨d,e⟩,hde,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨hd,he⟩ := Finset.mem_product.mp hde
  have hr := (leastPairBlock_data hs hc).1
  apply Nat.mem_divisors.mpr
  refine ⟨?_,hs.ne_zero⟩
  exact (Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
    (Nat.dvd_of_mem_divisors he)).trans (dvd_of_eq (Nat.div_mul_cancel hr))

/-- The FULL affine block annihilates both its constant and first-log
moment. The exact finite endpoint and every Möbius sign are retained. -/
theorem affine_tail_block_zero {B R X D d : ℕ} (hs : Squarefree (B*R))
    (hc : 2≤R.primeFactors.card) (hX : B*R≤X) (hD : 0<D)
    (hd : d∈B.divisors) (hDd : D≤d) :
    (∑ e∈R.divisors,(μ (d*e) : ℝ)*correctedProfile X (log D) 1 0 (d*e))=0 := by
  have hR1 : R≠1 := by intro h; simp [h] at hc
  have hm : (∑ e∈R.divisors,(μ e : ℝ))=0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero hR1
  have hl : (∑ e∈R.divisors,(μ e : ℝ)*log e)=0 := by
    simpa only [ArithmeticFunction.log_apply,
      ZetaRieszSignedConvolution.vonMangoldt_zero_of_squarefree_count hs.of_mul_right hc,
      neg_zero] using (ArithmeticFunction.sum_moebius_mul_log_eq (n:=R))
  have hcop := Nat.coprime_of_squarefree_mul hs
  have hdp : (0 : ℝ)<d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hlogd : log D≤log d := log_le_log (by exact_mod_cast hD)
    (by exact_mod_cast hDd)
  let c := max 0 (log D-log X)+log X
  have hterm e (he : e∈R.divisors) :
      (μ (d*e) : ℝ)*correctedProfile X (log D) 1 0 (d*e)=
        (μ d : ℝ)*(μ e : ℝ)*(log d+log e-c) := by
    have hep : (0 : ℝ)<e := by exact_mod_cast Nat.pos_of_mem_divisors he
    have hdeX : d*e≤X := (Nat.mul_le_mul
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.of_mul_left.ne_zero) (Nat.dvd_of_mem_divisors hd))
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.of_mul_right.ne_zero) (Nat.dvd_of_mem_divisors he))).trans hX
    have hlog : log D≤log (d*e : ℕ) := by
      rw [Nat.cast_mul,log_mul hdp.ne' hep.ne']
      linarith [log_natCast_nonneg e]
    have hmu : (μ (d*e) : ℝ)=(μ d : ℝ)*(μ e : ℝ) := by
      exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        ((hcop.of_dvd_left (Nat.dvd_of_mem_divisors hd)).of_dvd_right
          (Nat.dvd_of_mem_divisors he))
    rw [hmu]
    simp only [correctedProfile,centeredProfile,if_pos hdeX,zero_mul,add_zero,
      one_mul,max_eq_left (sub_nonpos.mpr hlog)]
    rw [Nat.cast_mul,log_mul hdp.ne' hep.ne']
    dsimp only [c]
    ring
  rw [Finset.sum_congr rfl hterm]
  calc
    _ = (μ d : ℝ)*((log d-c)*(∑ e∈R.divisors,(μ e : ℝ))+
      ∑ e∈R.divisors,(μ e : ℝ)*log e) := by
      rw [mul_add]
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 0 := by rw [hm,hl]; ring

set_option backward.isDefEq.respectTransparency false in
theorem tailDivisors_pairing_zero {n X D : ℕ} (hs : Squarefree n)
    (hc : 2≤n.primeFactors.card) (hX : n≤X) (hD : 0<D) :
    (∑ l∈tailDivisors D n,(μ l : ℝ)*correctedProfile X (log D) 1 0 l)=0 := by
  have hr := leastPairBlock_data hs hc
  have he : n/leastPairBlock n*leastPairBlock n=n := Nat.div_mul_cancel hr.1
  have hsprod : Squarefree (n/leastPairBlock n*leastPairBlock n) := by rwa [he]
  have hprodX : n/leastPairBlock n*leastPairBlock n≤X := by rwa [he]
  rw [tailDivisors,Finset.sum_image (tailIndices_injective hs hc D),tailIndices]
  refine (Finset.sum_product ((n/leastPairBlock n).divisors.filter (fun d=>D≤d))
    (leastPairBlock n).divisors
    (fun de : ℕ×ℕ=>(μ (de.1*de.2) : ℝ)*correctedProfile X (log D) 1 0 (de.1*de.2))).trans ?_
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hd,hDd⟩ := Finset.mem_filter.mp hd
  exact affine_tail_block_zero hsprod (by omega) hprodX hD hd hDd

/-- The original phase/allocation can be kept complex until the complete
block response is zero. No real-part or absolute-value cancellation is
assumed, and V may contain the unchanged original factorial kernel. -/
theorem tailDivisors_complex_pairing_zero {n X D : ℕ} (hs : Squarefree n)
    (hc : 2≤n.primeFactors.card) (hX : n≤X) (hD : 0<D) (V : ℂ) :
    (∑ l∈tailDivisors D n,V*(μ l : ℂ)*(correctedProfile X (log D) 1 0 l : ℂ))=0 := by
  have h := congrArg (fun t : ℝ=>V*(t : ℂ)) (tailDivisors_pairing_zero hs hc hX hD)
  push_cast at h
  simpa only [Finset.mul_sum,mul_assoc,mul_zero] using h

/-- The actual cutoff prefix of the selected original divisor incidences. -/
def tailSharp (D n k : ℕ) : ℝ :=
  ∑ l∈Finset.Icc 1 k,if l∈tailDivisors D n then (μ l : ℝ) else 0

theorem sum_tailSharp_profile_zero {n X D : ℕ} (hs : Squarefree n)
    (hc : 2≤n.primeFactors.card) (hX : n≤X) (hD : 0<D) :
    (∑ k∈Finset.Icc 1 X,tailSharp D n k*
      (correctedProfile X (log D) 1 0 k-correctedProfile X (log D) 1 0 (k+1)))=0 := by
  have hh := ZetaRieszSignedCutoffEnergy.abel_profile X (correctedProfile X (log D) 1 0)
    (fun l=>if l∈tailDivisors D n then (μ l : ℝ) else 0)
    (by simp [correctedProfile,centeredProfile])
  have hset : (Finset.Icc 1 X).filter (fun l=>l∈tailDivisors D n)=tailDivisors D n := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_Icc]
    constructor
    · exact fun h=>h.2
    · intro hl
      have hd := tailDivisors_subset hs hc D hl
      exact ⟨⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.dvd_of_mem_divisors hd)).trans hX⟩,hl⟩
  change (∑ l∈Finset.Icc 1 X,correctedProfile X (log D) 1 0 l*
    (if l∈tailDivisors D n then (μ l : ℝ) else 0))=_ at hh
  unfold tailSharp
  simp_rw [mul_comm (∑ l∈Finset.Icc 1 _,if l∈tailDivisors D n then (μ l : ℝ) else 0)]
  rw [← hh]
  simp_rw [mul_ite,mul_zero]
  rw [← Finset.sum_filter,hset]
  simpa only [mul_comm] using tailDivisors_pairing_zero hs hc hX hD

/-- Original weights are retained on EVERY native squarefree label.
Only the complete affine-tail incidence correction is multiplied by v. -/
def tailIncrement (u y : ℝ) (j : ℕ) (v : ℕ→ℂ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let X := nativeEndpoint u j
  let W := sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N) L u y N
  (∑ n∈(nativeLabels u j).filter Squarefree,
    (W n*v n).re*tailSharp (physicalCutoff u j) n k)*
      (correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1))

theorem sum_tailIncrement_zero (u y : ℝ) (j : ℕ) (v : ℕ→ℂ) :
    (∑ k∈Finset.Icc 1 (nativeEndpoint u j),tailIncrement u y j v k)=0 := by
  unfold tailIncrement
  dsimp only
  simp only [Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
  have hX : n≤nativeEndpoint u j :=
    (Finset.le_sup (f:=id) hn).trans (le_max_right _ _)
  rw [← Finset.mul_sum,length_eq_log_physicalCutoff,
    sum_tailSharp_profile_zero hs (by have := core_count hn; omega)
      hX (physicalCutoff_pos u j),mul_zero]

theorem tailIncrement_zero_early {u y : ℝ} {j k : ℕ} (v : ℕ→ℂ)
    (hk : k∈Finset.Icc 1 (nativeEndpoint u j))
    (hL : log (k+1 : ℕ)≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    tailIncrement u y j v k=0 := by
  have hf : correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0 k=
    correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0 (k+1) := by
    by_contra h
    exact low_cutoff_inactive (nativeEndpoint u j) k hL
      (Finset.mem_filter.mpr ⟨hk,h⟩)
  simp only [tailIncrement,hf,sub_self,mul_zero]

/-- Keep every previous correction in the SAME aggregate. The new
closed-block correction is an exact null, including on nonzero labels. -/
def tailCost (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) (v w : ℕ→ℂ) : ℝ :=
  nullCost u y j q a (fun k=>weightedIncrement u y j v k+tailIncrement u y j w k)

theorem tailCost_zero (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ)
    (a : ℝ) (v : ℕ→ℂ) : tailCost u y j q a v 0=weightedCost u y j q a v := by
  simp [tailCost,nullCost,weightedCost,tailIncrement]

theorem eventually_joined_floor_tail {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) (v w : ℕ→ℕ→ℂ) :
    ∀ᶠ j in atTop,
      -tailCost u y j (q j) (a j) (v j) (w j)-nativePaidBudget y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  exact eventually_joined_floor_after_null hu hU hy q a
    (fun j k=>weightedIncrement u y j (v j) k+tailIncrement u y j (w j) k)
    (fun j=>by rw [Finset.sum_add_distrib,sum_weightedIncrement_zero,sum_tailIncrement_zero,add_zero])

/-- One jointly funded price, with the entire old price kept as an
alternative. The numerical cofinal bound is not assumed by the inequality. -/
def tailPrice (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) (v w : ℕ→ℂ) : ℝ :=
  min (weightedPrice u y j q a r v) (tailCost u y j q a v w+nativePaidBudget y j)

theorem tailPrice_le_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ)
    (a r : ℝ) (v w : ℕ→ℂ) : tailPrice u y j q a r v w≤weightedPrice u y j q a r v :=
  min_le_left _ _

theorem tailPrice_zero (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ)
    (a r : ℝ) (v : ℕ→ℂ) : tailPrice u y j q a r v 0=weightedPrice u y j q a r v := by
  unfold tailPrice
  rw [tailCost_zero]
  exact min_eq_left (min_le_right _ _)

theorem eventually_joined_floor_with_closed_tail_credit {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a r : ℕ→ℝ) (v w : ℕ→ℕ→ℂ) :
    ∀ᶠ j in atTop,
      -tailPrice u y j (q j) (a j) (r j) (v j) (w j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_tail hu hU hy q a v w,
    eventually_joined_floor_with_weighted_zero_credit hu hU hy q a r v] with j hnew hold
  unfold tailPrice
  rcases le_total (weightedPrice u y j (q j) (a j) (r j) (v j))
      (tailCost u y j (q j) (a j) (v j) (w j)+nativePaidBudget y j) with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

/-- The final numerical premise is explicit. The null identities above
do not supply a cofinal bound on the actual native signed price. -/
theorem false_of_cofinal_tail_price (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) (hsimple : analyticZetaZeroMultiplicity rho=1)
    (q : ℕ→Fin 6→ℝ) (a r : ℕ→ℝ) (v w : ℕ→ℕ→ℂ)
    (hcost : ∃ᶠ j in atTop,
      tailPrice (3/2-rho.1.re) rho.1.im j (q j) (a j) (r j) (v j) (w j)≤399/5000) : False := by
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
      (ZetaRieszComplexProjection.tendsto_nativeError rho hrho hexposed hU)
  have hf := eventually_joined_floor_with_closed_tail_credit hu hU hy q a r v w
  exact (hcost.and_eventually hf).mono (fun j hj=>by
    obtain ⟨hc,hf⟩ := hj
    linarith only [hc,hf])

end RiemannGaussian.ZetaRieszClosedTailFloor
