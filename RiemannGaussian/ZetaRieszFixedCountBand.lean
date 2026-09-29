/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFixedCountPeriod
import RiemannGaussian.ZetaRieszPairBoundary

/-! # Joint payment of the previously unpaid counts seven through fifty-five

The six-prime population is kept once. Forty-nine new prime-count sectors
share the same signed-period estimate and its literal masks. Their constants
are absorbed by one common eventual threshold, not claimed height-uniform.
-/
namespace RiemannGaussian.ZetaRieszFixedCountBand
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- All newly paid counts: the cofactor has six through fifty-four primes. -/
def extra (v y : ℝ) : Finset ℕ :=
  (Finset.Icc 6 54).biUnion (fun k => ZetaRieszFixedCountPeriod.population k v y)

/-- The previous six-prime payment together with the new disjoint counts. -/
def population (v y : ℝ) : Finset ℕ :=
  ZetaRieszTransitionSixPeriod.population v y ∪ extra v y

/-- All old and new labels obey the same literal geometry. -/
theorem population_data {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) {n : ℕ}
    (hn : n ∈ population v y) :
    Squarefree n ∧ 6 ≤ n.primeFactors.card ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      (∀ a ∈ n.primeFactors, Real.log a ≤ (1189/2000 : ℝ)*Real.log n) := by
  rcases Finset.mem_union.mp hn with ho | hn
  · have hd := ZetaRieszTransitionSixPeriod.population_data hv hy ho
    exact ⟨hd.1,by omega,hd.2.2⟩
  · obtain ⟨k,hk,hn⟩ := Finset.mem_biUnion.mp hn
    have hk := Finset.mem_Icc.mp hk
    have hd := ZetaRieszFixedCountPeriod.population_data hv hy hn
    exact ⟨hd.1,by omega,hd.2.2⟩

/-- New counts cannot spend the previously paid six-prime labels. -/
theorem old_disjoint_extra {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) :
    Disjoint (ZetaRieszTransitionSixPeriod.population v y) (extra v y) := by
  apply Finset.disjoint_left.mpr
  intro n ho hn
  obtain ⟨k,hk,hn⟩ := Finset.mem_biUnion.mp hn
  have hk := Finset.mem_Icc.mp hk
  have ho := (ZetaRieszTransitionSixPeriod.population_data hv hy ho).2.1
  have hn := (ZetaRieszFixedCountPeriod.population_data hv hy hn).2.1
  omega

/-- Different cofactor counts are genuinely disjoint integer populations. -/
theorem count_disjoint {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (ZetaRieszFixedCountPeriod.population k v y)
      (ZetaRieszFixedCountPeriod.population l v y) := by
  apply Finset.disjoint_left.mpr
  intro n hk hl
  have hk := (ZetaRieszFixedCountPeriod.population_data hv hy hk).2.1
  have hl := (ZetaRieszFixedCountPeriod.population_data hv hy hl).2.1
  omega

/-- One signed payment controls all forty-nine new count sectors at once,
along with the previous six-prime sector. The physical masks and allocation
are discharged, and the full phase is summed before its real absolute value. -/
theorem eventually_population_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      population v y ⊆ ZetaRieszParityPacket.coreBand u N K ∧
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        |u^(N+1)*(∑ n ∈ population v y,
          ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
          u^(N+1)*((m : ℝ)/90000*V*(Real.pi/(4*m*|y|))) := by
  have hfam := (eventually_all_finset (Finset.Icc 6 54)).mpr (fun k hk =>
    ZetaRieszFixedCountPeriod.eventually_population_bound
      (by have := (Finset.mem_Icc.mp hk).1; omega : 2 ≤ k)
      (by norm_num : (0 : ℝ) < 1/100000000) hu hU hm hy hsmall hphase)
  filter_upwards [hfam,ZetaRieszSaddleBand.eventually_six_population_bound hu hU hm hy hsmall hphase,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ))] with j hfam hold hN v
  dsimp only
  intro hpeak hv hvu hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let V := Real.exp (-v/2)*v^N/N.factorial
  let h := Real.pi/(4*m*|y|)
  let B := u^(N+1)*(m : ℝ)*V*h
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hv100 : 100 ≤ v := by change 2*(N : ℝ) ≤ v at hv; linarith
  have hV : 0 < V := by dsimp [V]; positivity
  have hu0 : 0 ≤ u := by linarith
  have hB : 0 ≤ B := by dsimp [B,h]; positivity
  obtain ⟨hcore,V₀,hV₀,hV₀u,hcost⟩ := hold v hpeak hv hvu hlo hhi
  have hnew (k : ℕ) (hk : k ∈ Finset.Icc 6 54) :
      ZetaRieszFixedCountPeriod.population k v y ⊆ ZetaRieszParityPacket.coreBand u N K ∧
      |u^(N+1)*(∑ n ∈ ZetaRieszFixedCountPeriod.population k v y, f n).re| ≤ B/100000000 := by
    obtain ⟨hc,Vk,hVk,hVku,hcst⟩ := hfam k hk v hpeak hv hvu hlo hhi
    refine ⟨hc,?_⟩
    apply hcst.trans
    have hh := mul_le_mul_of_nonneg_left hVku
      (show 0 ≤ u^(N+1)*(m : ℝ)*h/100000000 by dsimp [h]; positivity)
    dsimp only [B]
    convert hh using 1 <;> ring
  have ho : |u^(N+1)*(∑ n ∈ ZetaRieszTransitionSixPeriod.population v y, f n).re| ≤ B/100000 := by
    apply hcost.trans
    have hh := mul_le_mul_of_nonneg_left hV₀u
      (show 0 ≤ u^(N+1)*(m : ℝ)*h/100000 by dsimp [h]; positivity)
    dsimp only [B]
    convert hh using 1 <;> ring
  refine ⟨Finset.union_subset hcore ?_,V,hV,le_rfl,?_⟩
  · intro n hn
    obtain ⟨k,hk,hn⟩ := Finset.mem_biUnion.mp hn
    exact (hnew k hk).1 hn
  · have he : u^(N+1)*(∑ n ∈ population v y, f n).re =
        u^(N+1)*(∑ n ∈ ZetaRieszTransitionSixPeriod.population v y, f n).re+
        ∑ k ∈ Finset.Icc 6 54, u^(N+1)*(∑ n ∈ ZetaRieszFixedCountPeriod.population k v y, f n).re := by
      rw [population,Finset.sum_union (old_disjoint_extra hv100 hy),extra,
        Finset.sum_biUnion (fun k _ l _ hkl => count_disjoint hv100 hy hkl),
        Complex.add_re,mul_add]
      simp only [Complex.re_sum,Finset.mul_sum]
    change |u^(N+1)*(∑ n ∈ population v y, f n).re| ≤ _
    rw [he]
    have hn := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun k hk => (hnew k hk).2))
    rw [Finset.sum_const,nsmul_eq_mul] at hn
    have hcard : (Finset.Icc 6 54).card = 49 := by decide
    rw [hcard] at hn
    norm_num only [Nat.cast_ofNat] at hn
    have hh := (abs_add_le _ _).trans (add_le_add ho hn)
    apply hh.trans
    have ht : B/100000+49*(B/100000000) ≤ B/90000 := by linarith only [hB]
    exact ht.trans_eq (by dsimp only [B]; ring)

/-- The new counts are disjoint from the existing five-prime supply. -/
theorem disjoint_supply {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (t h z : ℝ) (lo H : Fin 4 → ℝ) :
    Disjoint (population v y) (ZetaRieszJointPrimeCells.supplyCell t h z lo H) := by
  apply Finset.disjoint_left.mpr
  intro n hn hs
  have hd := population_data hv hy hn
  have hcard : n.primeFactors.card = n.primeFactorsList.length :=
    List.toFinset_card_of_nodup hd.1.nodup_primeFactorsList
  have hc := ZetaRieszJointTriplePayment.supply_count hs
  rw [ArithmeticFunction.cardFactors_apply,← hcard] at hc
  have hh := hd.2.1
  omega

/-- Four-prime payments and the new fixed-count payment have distinct labels. -/
theorem disjoint_adverse {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L t h z a : ℝ) :
    Disjoint (population v y) (ZetaRieszFourBoundaryCover.adversePopulation S L t h z a) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hf).2.2.1
  omega

/-- Full positive-five interior payments have no fixed-count labels. -/
theorem disjoint_interior {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z δ : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveSignedPayment.periodPopulation S L v' z m δ) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- The small-prime five-factor boundary is disjoint from the fixed-counts. -/
theorem disjoint_head {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveBoundary.periodPopulation S L v' z m) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- Every prime share of the new rectangle is below the paid owner band. -/
theorem disjoint_owner {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S A : Finset ℕ) :
    Disjoint (population v y) (ZetaRieszJointOwnerPayment.population S A) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨_,_,hn1,_,p,hp,_,_,hlo,_⟩ := Finset.mem_filter.mp hf
  have hc := (population_data hv hy hn).2.2.2.2 p hp
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  nlinarith


/-- The new fixed-count period has no labels in the previously paid
balanced-triple population. -/
theorem disjoint_balanced {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (t h : ℝ) :
    Disjoint (population v y) (ZetaRieszBroadTripleBudget.population S t h) := by
  apply Finset.disjoint_left.mpr
  intro n hn hb
  have hc := (population_data hv hy hn).2.1
  have hb := (Finset.mem_filter.mp hb).2.2.1
  omega

/-- Nor can it overlap the previously paid unbalanced-triple period. -/
theorem disjoint_triple {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) :
    Disjoint (population v y) (ZetaRieszTriplePeriod.population v y) := by
  apply Finset.disjoint_left.mpr
  intro n hn ht
  have hc := (population_data hv hy hn).2.1
  have ht := (ZetaRieszTriplePeriod.population_data hv hy ht).2.1
  omega



/-- Actual seven-prime labels cross the old cofactor boundary. On the literal
core cutoff-ratio range their second reflected response is strictly positive,
so the extended theorem pays a real unsaturated term rather than an empty set. -/
theorem eventually_unsaturated_extra {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v →
      ∃ a ∈ ZetaRieszFixedCountPeriod.cofactors 6 v,
      ∃ p ∈ ZetaRieszAllowancePrimeBoxes.logPrimes
        (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
      a*p ∈ extra v y ∧ (1733/2500 : ℝ)*v < Real.log a ∧
      ∀ L : ℝ, (693/1000 : ℝ)*v ≤ L → L ≤ (1733/2500 : ℝ)*v →
        0 < VaughanLogAverage.riesz (Real.log a-L) a := by
  have hy0 : 0 < |y| := by linarith
  have hH : 0 < 2*Real.pi/|y| := by positivity
  have hpi : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hne (S : Finset ℕ) (f : ℕ → ℝ) (hp : 0 < ∑ p ∈ S, f p) : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  filter_upwards [ZetaRieszMacroPrimeWindows.eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/10000) (by norm_num : (0 : ℝ) < 1/10000),
    ZetaRieszSharpPrimeWindows.eventually_log_mass_bounds hH
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1000 : ℕ)] with N hmacro hlast hlarge v hv
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hex (i : Fin 6) : ∃ q, q ∈ ZetaRieszAllowancePrimeBoxes.logPrimes
      (((579/5000 : ℝ)+(i : ℕ)/10000)*v) (v/10000) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hm := (hmacro (((579/5000 : ℝ)+(i : ℕ)/10000)*v) (v/10000)
      (by nlinarith) (by linarith)).1
    exact hne _ _ ((by positivity : 0 < (4999/5000 : ℝ)*(v/10000)/
      (((579/5000 : ℝ)+(i : ℕ)/10000)*v+v/10000)).trans_le hm)
  choose q hq using hex
  have hqp (i : Fin 6) := (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds (hq i)).1
  have hqb (i : Fin 6) := (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds (hq i)).2
  have hqu (i : Fin 6) : Real.log (q i) ≤ (291/2500 : ℝ)*v := by
    have hiu : ((i : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show (i : ℕ) ≤ 5 by omega)
    nlinarith [hqb i]
  have hql (i : Fin 6) : (579/5000 : ℝ)*v < Real.log (q i) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    nlinarith [hqb i]
  have hmono : StrictMono q := by
    intro i j hij
    have hijR : ((i : ℕ) : ℝ)+1 ≤ (j : ℕ) := by exact_mod_cast (show (i : ℕ)+1 ≤ j by omega)
    exact ZetaRieszAllowancePrimeBoxes.logPrimes_order
      (by nlinarith) (hq i) (hq j)
  let a := ∏ i, q i
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hqp i).ne_zero)
  have hsf : Squarefree a := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply (hqp i).coprime_iff_not_dvd.mpr
      intro hh
      exact hij (hmono.injective ((Nat.prime_dvd_prime_iff_eq (hqp i) (hqp j)).mp hh))
    · intro i _
      exact (hqp i).squarefree
  have hpf : a.primeFactors = Finset.univ.image q := by
    dsimp only [a]
    rw [← Finset.prod_image (f := fun n : ℕ => n) (s := Finset.univ) hmono.injective.injOn]
    apply Nat.primeFactors_prod
    intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hqp i
  have hc : a.primeFactors.card = 6 := by
    rw [hpf,Finset.card_image_of_injective _ hmono.injective]
    simp
  have hlog : Real.log a = ∑ i, Real.log (q i) := by
    rw [show (a : ℝ) = ∏ i, (q i : ℝ) by simp only [a,Nat.cast_prod],Real.log_prod]
    intro i _
    exact_mod_cast (hqp i).ne_zero
  have hsuml := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin 6)))
    (fun i _ => (hql i).le) ⟨0,Finset.mem_univ _,hql 0⟩
  have hsumu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) (fun i _ => hqu i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,← hlog] at hsuml hsumu
  have haU : ∀ p ∈ a.primeFactors, Real.log p ≤ (291/2500 : ℝ)*v := by
    intro p hp
    rw [hpf] at hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hqu i
  have hca : a ∈ ZetaRieszFixedCountPeriod.cofactors 6 v := by
    apply Finset.mem_filter.mpr
    refine ⟨ZetaRieszCofactorMass.mem_products_of_squarefree hsf hc
      (fun p hp => (haU p hp).trans (by linarith)),hsf,hc,by linarith,by linarith,?_⟩
    intro p hp
    linarith [haU p hp]
  have hpa : (1/4 : ℝ)*N ≤ v-Real.pi/|y|-Real.log a := by linarith
  have hpmass := (hlast _ hpa).1
  have he : 0 < Real.exp (2*Real.pi/|y|)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hH)
  obtain ⟨p,hp⟩ := hne _ _ ((by positivity : 0 < (1-1/2 : ℝ)*(Real.exp (2*Real.pi/|y|)-1)*
    Real.exp (v-Real.pi/|y|-Real.log a)).trans_le hpmass)
  refine ⟨a,hca,p,hp,?_,by linarith,?_⟩
  · exact Finset.mem_biUnion.mpr ⟨6,by decide,
      Finset.mem_biUnion.mpr ⟨a,hca,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩⟩
  · intro L hLl hLu
    have ha1 : a ≠ 1 := by intro he; simp [he] at hc
    have hmin : (579/5000 : ℝ)*v < Real.log a.minFac := by
      have hm : a.minFac ∈ a.primeFactors :=
        (Nat.minFac_prime ha1).mem_primeFactors (Nat.minFac_dvd a) ha0
      rw [hpf] at hm
      obtain ⟨i,_,he⟩ := Finset.mem_image.mp hm
      simpa only [he] using hql i
    rw [ZetaRieszTypeII.riesz_eq_cutoff_below_minFac ha0
      (show 0 ≤ Real.log a-L by linarith)
      (show Real.log a-L ≤ Real.log a.minFac by linarith)]
    linarith

/-- The enlarged payment includes actual near-balanced seven-prime labels.
Their cofactor logarithm lies above 84 percent, beyond the previous 70-percent cap. -/
theorem eventually_near_balanced_extra {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v →
      ∃ a ∈ ZetaRieszFixedCountPeriod.cofactors 6 v,
      ∃ p ∈ ZetaRieszAllowancePrimeBoxes.logPrimes
        (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
      a*p ∈ extra v y ∧ (21/25 : ℝ)*v < Real.log a ∧
        Real.log a ≤ (2109/2500 : ℝ)*v := by
  have hy0 : 0 < |y| := by linarith
  have hH : 0 < 2*Real.pi/|y| := by positivity
  have hpi : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hne (S : Finset ℕ) (f : ℕ → ℝ) (hp : 0 < ∑ p ∈ S, f p) : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  filter_upwards [ZetaRieszMacroPrimeWindows.eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/10000) (by norm_num : (0 : ℝ) < 1/10000),
    ZetaRieszSharpPrimeWindows.eventually_log_mass_bounds hH
      (by norm_num : (0 : ℝ) < 1/8) (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1000 : ℕ)] with N hmacro hlast hlarge v hv
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hex (i : Fin 6) : ∃ q, q ∈ ZetaRieszAllowancePrimeBoxes.logPrimes
      (((7/50 : ℝ)+(i : ℕ)/10000)*v) (v/10000) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hm := (hmacro (((7/50 : ℝ)+(i : ℕ)/10000)*v) (v/10000)
      (by nlinarith) (by linarith)).1
    exact hne _ _ ((by positivity : 0 < (4999/5000 : ℝ)*(v/10000)/
      (((7/50 : ℝ)+(i : ℕ)/10000)*v+v/10000)).trans_le hm)
  choose q hq using hex
  have hqp (i : Fin 6) := (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds (hq i)).1
  have hqb (i : Fin 6) := (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds (hq i)).2
  have hqu (i : Fin 6) : Real.log (q i) ≤ (703/5000 : ℝ)*v := by
    have hiu : ((i : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show (i : ℕ) ≤ 5 by omega)
    nlinarith [hqb i]
  have hql (i : Fin 6) : (7/50 : ℝ)*v < Real.log (q i) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    nlinarith [hqb i]
  have hmono : StrictMono q := by
    intro i j hij
    have hijR : ((i : ℕ) : ℝ)+1 ≤ (j : ℕ) := by exact_mod_cast (show (i : ℕ)+1 ≤ j by omega)
    exact ZetaRieszAllowancePrimeBoxes.logPrimes_order
      (by nlinarith) (hq i) (hq j)
  let a := ∏ i, q i
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hqp i).ne_zero)
  have hsf : Squarefree a := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply (hqp i).coprime_iff_not_dvd.mpr
      intro hh
      exact hij (hmono.injective ((Nat.prime_dvd_prime_iff_eq (hqp i) (hqp j)).mp hh))
    · intro i _
      exact (hqp i).squarefree
  have hpf : a.primeFactors = Finset.univ.image q := by
    dsimp only [a]
    rw [← Finset.prod_image (f := fun n : ℕ => n) (s := Finset.univ) hmono.injective.injOn]
    apply Nat.primeFactors_prod
    intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hqp i
  have hc : a.primeFactors.card = 6 := by
    rw [hpf,Finset.card_image_of_injective _ hmono.injective]
    simp
  have hlog : Real.log a = ∑ i, Real.log (q i) := by
    rw [show (a : ℝ) = ∏ i, (q i : ℝ) by simp only [a,Nat.cast_prod],Real.log_prod]
    intro i _
    exact_mod_cast (hqp i).ne_zero
  have hsuml := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin 6)))
    (fun i _ => (hql i).le) ⟨0,Finset.mem_univ _,hql 0⟩
  have hsumu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) (fun i _ => hqu i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,← hlog] at hsuml hsumu
  have haU : ∀ p ∈ a.primeFactors, Real.log p ≤ (703/5000 : ℝ)*v := by
    intro p hp
    rw [hpf] at hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hqu i
  have hca : a ∈ ZetaRieszFixedCountPeriod.cofactors 6 v := by
    apply Finset.mem_filter.mpr
    refine ⟨ZetaRieszCofactorMass.mem_products_of_squarefree hsf hc
      (fun p hp => (haU p hp).trans (by linarith)),hsf,hc,by linarith,by linarith,?_⟩
    intro p hp
    linarith [haU p hp]
  have hpa : (1/8 : ℝ)*N ≤ v-Real.pi/|y|-Real.log a := by linarith
  have hpmass := (hlast _ hpa).1
  have he : 0 < Real.exp (2*Real.pi/|y|)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hH)
  obtain ⟨p,hp⟩ := hne _ _ ((by positivity : 0 < (1-1/2 : ℝ)*(Real.exp (2*Real.pi/|y|)-1)*
    Real.exp (v-Real.pi/|y|-Real.log a)).trans_le hpmass)
  refine ⟨a,hca,p,hp,?_,by linarith,by linarith⟩
  exact Finset.mem_biUnion.mpr ⟨6,by decide,
    Finset.mem_biUnion.mpr ⟨a,hca,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩⟩

/-- The constant-width ownership margin includes actual labels excluded
by the former relative one-half-percent separation, at every cofactor prime. -/
theorem eventually_thin_gap_extra {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v →
      ∃ a ∈ ZetaRieszFixedCountPeriod.cofactors 6 v,
      ∃ p ∈ ZetaRieszAllowancePrimeBoxes.logPrimes
        (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
      a*p ∈ extra v y ∧ (534/625 : ℝ)*v < Real.log a ∧
        Real.log a ≤ (21369/25000 : ℝ)*v ∧
        (∀ q ∈ a.primeFactors, (199/200 : ℝ)*v-Real.log a < Real.log q) := by
  have hy0 : 0 < |y| := by linarith
  have hH : 0 < 2*Real.pi/|y| := by positivity
  have hpi : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hne (S : Finset ℕ) (f : ℕ → ℝ) (hp : 0 < ∑ p ∈ S, f p) : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  filter_upwards [ZetaRieszMacroPrimeWindows.eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/100000) (by norm_num : (0 : ℝ) < 1/100000),
    ZetaRieszSharpPrimeWindows.eventually_log_mass_bounds hH
      (by norm_num : (0 : ℝ) < 1/8) (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1000 : ℕ)] with N hmacro hlast hlarge v hv
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hex (i : Fin 6) : ∃ q, q ∈ ZetaRieszAllowancePrimeBoxes.logPrimes
      (((178/1250 : ℝ)+(i : ℕ)/100000)*v) (v/100000) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hm := (hmacro (((178/1250 : ℝ)+(i : ℕ)/100000)*v) (v/100000)
      (by nlinarith) (by linarith)).1
    exact hne _ _ ((by positivity : 0 < (4999/5000 : ℝ)*(v/100000)/
      (((178/1250 : ℝ)+(i : ℕ)/100000)*v+v/100000)).trans_le hm)
  choose q hq using hex
  have hqp (i : Fin 6) := (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds (hq i)).1
  have hqb (i : Fin 6) := (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds (hq i)).2
  have hqu (i : Fin 6) : Real.log (q i) ≤ (7123/50000 : ℝ)*v := by
    have hiu : ((i : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show (i : ℕ) ≤ 5 by omega)
    nlinarith [hqb i]
  have hql (i : Fin 6) : (178/1250 : ℝ)*v < Real.log (q i) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    nlinarith [hqb i]
  have hmono : StrictMono q := by
    intro i j hij
    have hijR : ((i : ℕ) : ℝ)+1 ≤ (j : ℕ) := by exact_mod_cast (show (i : ℕ)+1 ≤ j by omega)
    exact ZetaRieszAllowancePrimeBoxes.logPrimes_order
      (by nlinarith) (hq i) (hq j)
  let a := ∏ i, q i
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hqp i).ne_zero)
  have hsf : Squarefree a := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply (hqp i).coprime_iff_not_dvd.mpr
      intro hh
      exact hij (hmono.injective ((Nat.prime_dvd_prime_iff_eq (hqp i) (hqp j)).mp hh))
    · intro i _
      exact (hqp i).squarefree
  have hpf : a.primeFactors = Finset.univ.image q := by
    dsimp only [a]
    rw [← Finset.prod_image (f := fun n : ℕ => n) (s := Finset.univ) hmono.injective.injOn]
    apply Nat.primeFactors_prod
    intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hqp i
  have hc : a.primeFactors.card = 6 := by
    rw [hpf,Finset.card_image_of_injective _ hmono.injective]
    simp
  have hlog : Real.log a = ∑ i, Real.log (q i) := by
    rw [show (a : ℝ) = ∏ i, (q i : ℝ) by simp only [a,Nat.cast_prod],Real.log_prod]
    intro i _
    exact_mod_cast (hqp i).ne_zero
  have hsuml := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin 6)))
    (fun i _ => (hql i).le) ⟨0,Finset.mem_univ _,hql 0⟩
  have hsumu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) (fun i _ => hqu i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,← hlog] at hsuml hsumu
  have haU : ∀ p ∈ a.primeFactors, Real.log p ≤ (7123/50000 : ℝ)*v := by
    intro p hp
    rw [hpf] at hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hqu i
  have hca : a ∈ ZetaRieszFixedCountPeriod.cofactors 6 v := by
    apply Finset.mem_filter.mpr
    refine ⟨ZetaRieszCofactorMass.mem_products_of_squarefree hsf hc
      (fun p hp => (haU p hp).trans (by linarith)),hsf,hc,by linarith,by linarith,?_⟩
    intro p hp
    linarith [haU p hp]
  have hpa : (1/8 : ℝ)*N ≤ v-Real.pi/|y|-Real.log a := by linarith
  have hpmass := (hlast _ hpa).1
  have he : 0 < Real.exp (2*Real.pi/|y|)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hH)
  obtain ⟨p,hp⟩ := hne _ _ ((by positivity : 0 < (1-1/2 : ℝ)*(Real.exp (2*Real.pi/|y|)-1)*
    Real.exp (v-Real.pi/|y|-Real.log a)).trans_le hpmass)
  refine ⟨a,hca,p,hp,?_,by linarith,by linarith,?_⟩
  · exact Finset.mem_biUnion.mpr ⟨6,by decide,
      Finset.mem_biUnion.mpr ⟨a,hca,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩⟩
  · intro q' hq'
    rw [hpf] at hq'
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq'
    linarith [hql i]

/-- The wider population is genuinely nonempty; in fact it includes cofactors
with a strictly positive unsaturated cutoff response. -/
theorem eventually_extra_nonempty {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v → (extra v y).Nonempty := by
  filter_upwards [eventually_unsaturated_extra hy] with N hN v hv
  obtain ⟨a,_,p,_,hp,_,_⟩ := hN v hv
  exact ⟨a*p,hp⟩

end
end RiemannGaussian.ZetaRieszFixedCountBand
