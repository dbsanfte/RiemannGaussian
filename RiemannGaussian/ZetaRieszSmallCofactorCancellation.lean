/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHigherRankHingeFloor
import RiemannGaussian.ZetaRieszBroadOwnerPeriodFloor

/-!
# Join small-prime divisor blocks before pricing a crossing

An arbitrary squarefree block containing the canonical least-prime pair
can be joined after BOTH old zero deletions. No label, phase, factorial
weight or prime-count mask changes. Odd blocks have an exact reflection
zero and a quantitative crossing bound measuring distance from that zero,
rather than the sum of the separately priced canonical blocks.

These are literal signed inequalities at unrestricted cofactor counts.
Smallness alone does not make every crossing zero; the remaining weighted
crossing profile still requires an independent global estimate.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical Pointwise ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSmallCofactorCancellation
open ZetaRieszShortDivisorOrbits ZetaRieszShortDivisorCancellation
open ZetaRieszHingePairCancellation ZetaRieszHigherRankHingeFloor
open ZetaRieszPrimeEndpoint ZetaRieszParityPacket
open ZetaRieszSignedConvolution
open ZetaRieszFixedCountPeriod ZetaRieszSignedPeriodFloor
open ZetaRieszOwnerCurvatureFloor ZetaRieszJointOwnerFibreFloor
open ZetaRieszTinyOwnerPeriodFloor ZetaRieszClippedOwnerPeriodFloor
open ZetaRieszAllowancePrimeBoxes
open ZetaRieszStaggeredFloor ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszBroadOwnerPeriodFloor ZetaRieszSymmetricPeriodPayment

/-- Refining a larger block into canonical-pair blocks keeps the SAME
original unsigned/signed incidence, not an auxiliary integer label. -/
theorem orbit_refine {a R Q e : ℕ} (hQR : Q ∣ R) :
    orbitDivisors a R e =
      (R/Q).divisors.biUnion (fun d => orbitDivisors a Q (e*d)) := by
  unfold orbitDivisors
  have hd : R.divisors=Q.divisors*(R/Q).divisors := by
    rw [← Nat.divisors_mul,Nat.mul_div_cancel' hQR]
  rw [hd]
  ext db
  constructor
  · intro hdb
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hdb
    rw [Finset.mul_def] at hv
    obtain ⟨⟨c,d⟩,hcd,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    apply Finset.mem_biUnion.mpr
    refine ⟨d,hd,Finset.mem_image.mpr ⟨c,hc,?_⟩⟩
    apply Prod.ext
    · change e*d*c=e*(c*d)
      ring
    · change a/(e*d*c)=a/(e*(c*d))
      congr 1
      ring
  · intro hdb
    obtain ⟨d,hd,hdb⟩ := Finset.mem_biUnion.mp hdb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hdb
    apply Finset.mem_image.mpr
    refine ⟨c*d,?_ ,?_⟩
    · rw [Finset.mul_def]
      exact Finset.mem_image.mpr ⟨(c,d),Finset.mem_product.mpr ⟨hc,hd⟩,rfl⟩
    · apply Prod.ext
      · change e*(c*d)=e*d*c
        ring
      · change a/(e*(c*d))=a/(e*d*c)
        congr 1
        ring

/-- Every refined base still divides the actual canonical complement. -/
theorem refined_base_dvd {a R Q e d : ℕ} (hRa : R ∣ a) (hQR : Q ∣ R)
    (he : e ∣ a/R) (hd : d ∈ (R/Q).divisors) : e*d ∣ a/Q := by
  apply (Nat.dvd_div_iff_mul_dvd (hQR.trans hRa)).mpr
  have hh := Nat.mul_dvd_mul he (Nat.dvd_of_mem_divisors hd)
  have heq : Q*(a/R*(R/Q))=a := by
    calc
      _ = (a/R)*(Q*(R/Q)) := by ring
      _ = (a/R)*R := by rw [Nat.mul_div_cancel' hQR]
      _ = a := by rw [mul_comm,Nat.mul_div_cancel' hRa]
  simpa only [heq] using Nat.mul_dvd_mul_left Q hh

private theorem orbit_inter_union {a Q e : ℕ} (hcop : Q.Coprime (a/Q))
    (he : e ∈ (a/Q).divisors) (E : Finset ℕ) (hE : E ⊆ (a/Q).divisors) :
    orbitDivisors a Q e ∩ E.biUnion (orbitDivisors a Q) =
      if e ∈ E then orbitDivisors a Q e else ∅ := by
  by_cases heE : e ∈ E
  · rw [if_pos heE]
    apply Finset.inter_eq_left.mpr
    intro db hdb
    exact Finset.mem_biUnion.mpr ⟨e,heE,hdb⟩
  · rw [if_neg heE]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro db hdb
    obtain ⟨hde,hh⟩ := Finset.mem_inter.mp hdb
    obtain ⟨f,hf,hdf⟩ := Finset.mem_biUnion.mp hh
    exact (Finset.disjoint_left.mp
      (orbitDivisors_disjoint hcop he (hE hf) (fun heq => heE (heq ▸ hf)))) hde hdf

/-- A complete canonical block is unchanged by the earlier zero credits.
This also holds for a crossing which was never individually removed. -/
theorem retained_canonical_orbit_eq_full {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (w : ℂ) :
    let a := n/largestPrime n
    let Q := leastPairBlock a
    let O := orbitDivisors a Q e
    let D := a.divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db ∈ D ∩ O, f db)=(∑ db ∈ O, f db) := by
  dsimp only
  let a := n/largestPrime n
  let Q := leastPairBlock a
  let O := orbitDivisors a Q e
  let B := cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n
  let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
    (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
  have hb := canonical_block_data hn hs
  have ha := (core_data hn hs).2.1
  have hO : O ⊆ a.divisorsAntidiagonal := orbitDivisors_subset
    (Nat.pos_of_ne_zero ha.ne_zero) hb.1 (Nat.dvd_of_mem_divisors he)
  have hz₁ : (∑ db ∈ O ∩ cancelledOrbitDivisors u N n, f db)=0 := by
    unfold cancelledOrbitDivisors
    dsimp only
    rw [if_pos ⟨hb.1,by omega⟩]
    rw [orbit_inter_union hb.2.2 he _ (Finset.filter_subset _ _)]
    split_ifs with h
    · have hg := (Finset.mem_filter.mp h).2
      exact weighted_orbit_eq_zero ha (core_data hn hs).1 hb.1
        (Nat.dvd_of_mem_divisors he) (by omega) (by linarith [hg.2.1]) hg.2.2.1 w
    · exact Finset.sum_empty
  have hz₂ : (∑ db ∈ O ∩ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n, f db)=0 := by
    unfold ZetaRieszCrossingOrbitCancellation.affineDivisors
    dsimp only
    rw [if_pos ⟨hb.1,by omega⟩]
    rw [orbit_inter_union hb.2.2 he _ (Finset.filter_subset _ _)]
    split_ifs with h
    · have hg := (Finset.mem_filter.mp h).2
      exact weighted_orbit_eq_zero ha (core_data hn hs).1 hb.1
        (Nat.dvd_of_mem_divisors he) (by omega) (by linarith [hg.1]) hg.2.1 w
    · exact Finset.sum_empty
  have hz : (∑ db ∈ O ∩ B, f db)=0 := by
    rw [Finset.inter_union_distrib_left,Finset.sum_union (by
      exact (ZetaRieszCrossingOrbitCancellation.affine_disjoint_old_cancelled hn hs).symm.mono
        (Finset.inter_subset_right) (Finset.inter_subset_right))]
    rw [hz₁,hz₂,add_zero]
  have hset : (a.divisorsAntidiagonal \ B) ∩ O=O \ (O ∩ B) := by
    ext db
    simp only [Finset.mem_inter,Finset.mem_sdiff]
    constructor
    · exact fun h => ⟨h.2,fun hh => h.1.2 hh.2⟩
    · exact fun h => ⟨⟨hO h.1,fun hh => h.2 ⟨h.1,hh⟩⟩,h.1⟩
  have hh := Finset.sum_sdiff (Finset.inter_subset_left : O ∩ B ⊆ O) (f := f)
  rw [hz,add_zero] at hh
  change (∑ db ∈ (a.divisorsAntidiagonal \ B) ∩ O, f db)=∑ db ∈ O, f db
  rw [hset,hh]

/-- Joining every small-prime incidence does not restore either old
zero population. The block size and remaining cofactor count may grow. -/
theorem retained_small_orbit_eq_full {u : ℝ} {N K n R e : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hRa : R ∣ n/largestPrime n) (hQR : leastPairBlock (n/largestPrime n) ∣ R)
    (he : e ∈ ((n/largestPrime n)/R).divisors) (w : ℂ) :
    let a := n/largestPrime n
    let D := a.divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let f := fun db : ℕ×ℕ => w*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
    (∑ db ∈ D ∩ orbitDivisors a R e, f db)=(∑ db ∈ orbitDivisors a R e, f db) := by
  dsimp only
  let a := n/largestPrime n
  let Q := leastPairBlock a
  have hb := canonical_block_data hn hs
  have ha := (core_data hn hs).2.1
  have hbase (d : ℕ) (hd : d ∈ (R/Q).divisors) : e*d ∈ (a/Q).divisors :=
    Nat.mem_divisors.mpr ⟨refined_base_dvd hRa hQR (Nat.dvd_of_mem_divisors he) hd,
      (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hb.1) (Nat.pos_of_ne_zero ha.ne_zero)).ne'⟩
  have hdis : ∀ d ∈ (R/Q).divisors, ∀ f ∈ (R/Q).divisors, d≠f →
      Disjoint (orbitDivisors a Q (e*d)) (orbitDivisors a Q (e*f)) := by
    intro d hd f hf hdf
    apply orbitDivisors_disjoint hb.2.2 (hbase d hd) (hbase f hf)
    intro hef
    exact hdf (Nat.mul_left_cancel (Nat.pos_of_mem_divisors he) hef)
  rw [orbit_refine hQR,Finset.inter_biUnion,
    Finset.sum_biUnion (by
      intro d hd f hf hdf
      exact (hdis d hd f hf hdf).mono Finset.inter_subset_right Finset.inter_subset_right),
    Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro d hd
  exact retained_canonical_orbit_eq_full hn hs (hbase d hd) w

/-- An odd small block is priced by displacement from its exact
reflection zero, uniformly in all other factor counts. -/
theorem odd_block_crossing_bound {R : ℕ} (hs : Squarefree R)
    (hc : 2 ≤ R.primeFactors.card) (hmu : μ R = -1) (D : ℝ) :
    |VaughanLogAverage.riesz D R| ≤
      (2 : ℝ)^R.primeFactors.card/4*|D-log R/2| := by
  have hR1 : R≠1 := by intro h; simp [h] at hc
  have hnp : ¬R.Prime := by intro h; rw [h.primeFactors] at hc; simp at hc
  have hz := VaughanLogAverage.riesz_half_log_eq_zero hs hR1 hnp hmu
  have hh := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter D (log R/2) hs hc
  rw [hz,sub_zero,ZetaRieszTentSlope.absolute_divisor_mass_eq_card hs,
    ZetaRieszSmoothHead.card_divisors_of_squarefree hs,Nat.cast_pow,Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

/-- Once the OTHER hinge is saturated, odd-block cancellation pays only
the remaining midpoint displacement. Neither hinge was discarded. -/
theorem odd_two_hinge_bound {R : ℕ} (hs : Squarefree R)
    (hc : 2 ≤ R.primeFactors.card) (hmu : μ R = -1) {P D : ℝ}
    (hfull : log R ≤ P+D) :
    |VaughanLogAverage.riesz (P+D) R-VaughanLogAverage.riesz D R| ≤
      (2 : ℝ)^R.primeFactors.card/4*|D-log R/2| := by
  have hR1 : R≠1 := by intro h; simp [h] at hc
  have hnp : ¬R.Prime := by intro h; rw [h.primeFactors] at hc; simp at hc
  rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hs hR1 hnp hfull,
    zero_sub,abs_neg]
  exact odd_block_crossing_bound hs hc hmu D

/-- A genuine clustered divisor spectrum misses the entire changing
hinge. This cancels all small-prime subset ranks before any norm. -/
theorem spectrum_gap_cutoff_zero {R B : ℕ} (hs : Squarefree R)
    (hc : 2 ≤ R.primeFactors.card) (hcop : B.Coprime R) {D : ℝ}
    (hgap : ∀ d ∈ B.divisors, D≤log d ∨ log d+log R≤D) :
    VaughanLogAverage.riesz D (B*R)=0 := by
  have hR1 : R≠1 := by intro h; simp [h] at hc
  have hnp : ¬R.Prime := by intro h; rw [h.primeFactors] at hc; simp at hc
  rw [ZetaSquarefreeRieszWindows.riesz_coprime_mul D hcop]
  apply Finset.sum_eq_zero
  intro d hd
  rcases hgap d hd with h | h
  · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (by linarith : D-log d≤0),mul_zero]
  · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hs hR1 hnp
      (by linarith : log R≤D-log d),mul_zero]

/-- A whole cutoff interval can be cleared with one finite arithmetic
gap check. Endpoints, empty large-factor subset and every rank remain. -/
theorem spectrum_gap_interval_zero {R B : ℕ} (hs : Squarefree R)
    (hc : 2 ≤ R.primeFactors.card) (hcop : B.Coprime R) {D₀ D₁ : ℝ}
    (hgap : ∀ d ∈ B.divisors, D₁≤log d ∨ log d+log R≤D₀) :
    ∀ D ∈ Set.Icc D₀ D₁, VaughanLogAverage.riesz D (B*R)=0 := by
  intro D hD
  apply spectrum_gap_cutoff_zero hs hc hcop
  intro d hd
  rcases hgap d hd with h | h
  · exact Or.inl (hD.2.trans h)
  · exact Or.inr (h.trans hD.1)

/-- Nearly equal large-prime logarithms give uniformly separated
divisor-count layers. Their count is NOT required to be bounded. -/
theorem clustered_spectrum_gap {R B : ℕ} (hB : Squarefree B) {α ε D₀ D₁ : ℝ}
    (hε : 0≤ε) (hα : 0≤α-ε)
    (hlogs : ∀ q ∈ B.primeFactors, α-ε≤log q ∧ log q≤α+ε)
    (j : ℕ) (hlo : (j : ℝ)*(α+ε)+log R≤D₀)
    (hhi : D₁≤(j+1 : ℕ)*(α-ε)) :
    ∀ d ∈ B.divisors, D₁≤log d ∨ log d+log R≤D₀ := by
  intro d hd
  have hdB := Nat.dvd_of_mem_divisors hd
  have hdS := hB.squarefree_of_dvd hdB
  have hsum := CoprimeEulerPhase.squarefree_log_eq_prime_sum hdS
  have hlogs' q (hq : q ∈ d.primeFactors) :=
    hlogs q (Nat.primeFactors_mono hdB hB.ne_zero hq)
  have hupper : log d≤(d.primeFactors.card : ℝ)*(α+ε) := by
    rw [hsum,← nsmul_eq_mul,← Finset.sum_const]
    exact Finset.sum_le_sum (fun q hq => (hlogs' q hq).2)
  have hlower : (d.primeFactors.card : ℝ)*(α-ε)≤log d := by
    rw [hsum,← nsmul_eq_mul,← Finset.sum_const]
    exact Finset.sum_le_sum (fun q hq => (hlogs' q hq).1)
  by_cases hj : d.primeFactors.card≤j
  · right
    have hjR : (d.primeFactors.card : ℝ)≤j := by exact_mod_cast hj
    have hh := mul_le_mul_of_nonneg_right hjR (by linarith : 0≤α+ε)
    linarith
  · left
    have hjR : (j+1 : ℕ)≤(d.primeFactors.card : ℝ) := by exact_mod_cast (by omega : j+1≤d.primeFactors.card)
    have hh := mul_le_mul_of_nonneg_right hjR hα
    exact hhi.trans (hh.trans hlower)

/-- The literal two-hinge response is EXACTLY constant throughout the
prime period if its changing hinge misses the small-block spectrum. -/
theorem spectrum_gap_response_constant {R B : ℕ} (hs : Squarefree R)
    (hc : 2 ≤ R.primeFactors.card) (hcop : B.Coprime R) {v y L : ℝ}
    (hy : 0<y)
    (hgap : ∀ d ∈ B.divisors,
      v+Real.pi/y-L≤log d ∨ log d+log R≤v-Real.pi/y-L) :
    ∀ T ∈ Set.Icc (v-Real.pi/y) (v+Real.pi/y),
      response L T (B*R)=response L v (B*R) := by
  have hzero := spectrum_gap_interval_zero hs hc hcop hgap
  have hπ : 0≤Real.pi/y := by positivity
  have hv := hzero (v-L) (show v-L∈Set.Icc (v-Real.pi/y-L) (v+Real.pi/y-L) from
    ⟨by linarith,by linarith⟩)
  intro T hT
  have ht := hzero (T-L) ⟨by linarith [hT.1],by linarith [hT.2]⟩
  simp only [response,ht,hv]

/-- The literal unallocated signed period has NO cutoff-variation debit
when the changing hinge is flat. Every factorial order and both original
hinges remain. Small primes and growing cofactor counts are allowed. -/
theorem flat_unallocated_fibre_floor {k N : ℕ} (hk : 2≤k) {e : ℝ} (he : |e|=1)
    {v y L : ℝ} (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : 0<L)
    {a : ℕ} (ha : Squarefree a) (hc : a.primeFactors.card=k)
    (howner : ∀ q ∈ a.primeFactors, log q≤v-Real.pi/y-log a)
    (hlog : 5000≤v-Real.pi/y-log a)
    (hpeak : Real.sin (y*v)=0) (hsign : e*Real.cos (y*v)≤0)
    (hflat : ∀ T ∈ Set.Icc (v-Real.pi/y) (v+Real.pi/y), response L T a=response L v a) :
    -(2*amplitude N v/(L*a))*|partResponse e k L v a| *
        jointPeriodCost N v y (log a) ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  let D := logPrimes (v-Real.pi/y-log a) (2*Real.pi/y)
  let c := e*partResponse e k L v a
  have hsign' : c*Real.cos (y*v)≤0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤partResponse e k L v a from le_max_right _ _) hsign
    dsimp only [c]
    nlinarith only [hh]
  have hperiod := selected_period_floor (Finset.range (N+2)) (Finset.Subset.refl _)
    (log_natCast_nonneg a) hlog hy hNv hpeak hsign'
  have hsum : (∑ p ∈ D, signedPart e ∅ L y N (p*a))=
      (1/L/a)*(c*(∑ p ∈ D, selectedAmplitude N (Finset.range (N+2)) (log a)
        (log p+log a)*(p : ℝ)⁻¹*Real.cos (y*(log p+log a)))) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hg := owner_fibre_geometry ha howner hp
    have ht : log p+log a∈Set.Icc (v-Real.pi/y) (v+Real.pi/y) :=
      ⟨hg.2.2.2.1.le,hg.2.2.2.2⟩
    have hr : partResponse e k L (log p+log a) a=partResponse e k L v a := by
      unfold partResponse
      rw [hflat _ ht]
    rw [unallocated_atom_eq ha hc hk hg.1 hg.2.1 hL e y N,hr,
      selectedAmplitude_full N (log a) _ (by
        have hpos : 0<log p := log_pos (by exact_mod_cast hg.1.one_lt)
        linarith [log_natCast_nonneg a] : log p+log a≠0)]
  change _≤∑ p ∈ D, signedPart e ∅ L y N (p*a)
  rw [hsum]
  have hh := mul_le_mul_of_nonneg_left hperiod (show 0≤1/L/a by positivity)
  have hcabs : |c|=|partResponse e k L v a| := by
    dsimp only [c]
    rw [abs_mul,he,one_mul]
  rw [hcabs] at hh
  convert hh using 1 <;> first | rfl | (simp only [jointPeriodCost,div_eq_mul_inv,mul_inv_rev]; ring)

/-- The clustered log conditions imply the improved ORIGINAL prime-row
floor directly. There is no analytic cancellation hypothesis in the gap. -/
theorem clustered_unallocated_fibre_floor {k N R B : ℕ} (hk : 2≤k)
    (hR : Squarefree R) (hcntR : 2≤R.primeFactors.card) (hB : Squarefree B)
    (hcop : B.Coprime R) (hc : (B*R).primeFactors.card=k)
    {e v y L α ε : ℝ} (he : |e|=1) (hNv : (N : ℝ)+2≤v)
    (hy : 54≤y) (hL : 0<L) (hε : 0≤ε) (hα : 0≤α-ε)
    (hlogs : ∀ q ∈ B.primeFactors, α-ε≤log q ∧ log q≤α+ε)
    (j : ℕ) (hlo : (j : ℝ)*(α+ε)+log R≤v-Real.pi/y-L)
    (hhi : v+Real.pi/y-L≤(j+1 : ℕ)*(α-ε))
    (howner : ∀ q ∈ (B*R).primeFactors, log q≤v-Real.pi/y-log (B*R : ℕ))
    (hlog : 5000≤v-Real.pi/y-log (B*R : ℕ))
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(2*amplitude N v/(L*(B*R)))*|partResponse e k L v (B*R)| *
        jointPeriodCost N v y (log (B*R : ℕ)) ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-log (B*R : ℕ)) (2*Real.pi/y),
        signedPart e ∅ L y N (p*(B*R)) := by
  simpa only [Nat.cast_mul] using flat_unallocated_fibre_floor hk he hNv hy hL
    (Nat.squarefree_mul_iff.mpr ⟨hcop,hB,hR⟩) hc howner hlog hpeak hsign
    (spectrum_gap_response_constant hR hcntR hcop (by linarith : 0<y)
      (clustered_spectrum_gap hB hε hα hlogs j hlo hhi))

private theorem response_constant_bound (k : ℕ) : responseConstant k≤6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ)≤(2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    exact_mod_cast hh.trans (Nat.pow_le_pow_right (by norm_num : 1≤(2 : ℕ)) (by omega : k-2≤k))
  have h0 := hp 0
  have h1 := hp 1
  have hpow : (1 : ℝ)≤(2 : ℝ)^k := one_le_pow₀ (by norm_num)
  unfold responseConstant
  nlinarith only [h0,h1,hpow]

/-- The separated-layer row retains the inverse-SQUARE owner-log
saving, even with arbitrarily small cofactor primes. The former
`2^k*pi/(4*y*H)` crossing debit is absent. -/
theorem flat_unallocated_row_floor {k N : ℕ} (hk : 2≤k) {e : ℝ} (he : |e|=1)
    {v y L H b : ℝ} (hH : 5000≤H) (hNv : (N : ℝ)+2≤v)
    (hy : 54≤y) (hL : v/2≤L) {a : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card=k) (hmin : log a.minFac≤b)
    (hP : H≤v-Real.pi/y-log a)
    (howner : ∀ q ∈ a.primeFactors, log q≤v-Real.pi/y-log a)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0)
    (hflat : ∀ T ∈ Set.Icc (v-Real.pi/y) (v+Real.pi/y), response L T a=response L v a) :
    -((120*b/H^2)*(2 : ℝ)^k*(a : ℝ)⁻¹)*(amplitude N v/v) ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y), signedPart e ∅ L y N (p*a) := by
  have hH0 : 0<H := by linarith
  have hv0 : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have ha0 : (0 : ℝ)<a := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have hb0 : 0≤b := (log_natCast_nonneg a.minFac).trans hmin
  have hL0 : 0<L := (by linarith : 0<v/2).trans_le hL
  have hc₁ := (partResponse_bound he k L v a).trans (response_bound ha hc hk L v)
  have hc₂ : responseConstant k*log a.minFac≤6*(2 : ℝ)^k*b := by
    exact (mul_le_mul_of_nonneg_left hmin (responseConstant_pos k).le).trans
      (mul_le_mul_of_nonneg_right (response_constant_bound k) hb0)
  have hcost := jointPeriodCost_shell_le hy hNv hH0 hP
  have hcost0 : 0≤jointPeriodCost N v y (log a) := by
    have hv' : 0<v-Real.pi/y := by linarith [log_natCast_nonneg a]
    unfold jointPeriodCost
    positivity
  have hpre : 2*amplitude N v/(L*a)≤4*(amplitude N v/v)*(a : ℝ)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity [amplitude_nonneg N hv0.le] : 0≤2*amplitude N v)
        (by positivity : 0<v/2) hL) (inv_nonneg.mpr ha0.le)
    convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have hin := mul_le_mul (hc₁.trans hc₂) hcost hcost0 (by positivity : 0≤6*(2 : ℝ)^k*b)
  have hh := mul_le_mul hpre hin (mul_nonneg (abs_nonneg _) hcost0)
    (by positivity [amplitude_nonneg N hv0.le] : 0≤4*(amplitude N v/v)*(a : ℝ)⁻¹)
  have hfloor := flat_unallocated_fibre_floor hk he hNv hy hL0 ha hc howner
    (hH.trans hP) hpeak hsign hflat
  have heq : (4*(amplitude N v/v)*(a : ℝ)⁻¹)*(6*(2 : ℝ)^k*b*(5/H^2))=
      ((120*b/H^2)*(2 : ℝ)^k*(a : ℝ)⁻¹)*(amplitude N v/v) := by ring
  rw [heq] at hh
  have hfloor' := hfloor
  simp only [neg_mul,mul_assoc] at hfloor'
  simpa only [neg_mul,mul_assoc] using (neg_le_neg hh).trans hfloor'

/-- All selected counts are joined before costing. No cofactor-prime
lower cutoff, fixed count ceiling, or tuple overcount occurs here. -/
theorem flat_all_counts_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (S : ℕ → Finset ℕ) (Q : Finset ℕ) {v y L H b M : ℝ}
    (hI : ∀ k ∈ I,2≤k) (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hb : 0≤b) (hM : 0≤M) (hQmass : (∑ p ∈ Q,(p : ℝ)⁻¹)≤M)
    (hS : ∀ k ∈ I,∀ a ∈ S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ Q)
    (hmin : ∀ k ∈ I,∀ a ∈ S k,log a.minFac≤b)
    (hP : ∀ k ∈ I,∀ a ∈ S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k ∈ I,∀ a ∈ S k,∀ q ∈ a.primeFactors,log q≤v-Real.pi/y-log a)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0)
    (hflat : ∀ k ∈ I,∀ a ∈ S k,∀ T ∈ Set.Icc (v-Real.pi/y) (v+Real.pi/y),
      response L T a=response L v a) :
    -(120*b*exp (2*M)/H^2)*(amplitude N v/v)≤
      ∑ k ∈ I,∑ a ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  have hH0 : 0<H := by linarith
  have hv0 : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hf0 : 0≤amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hrow k (hk : k ∈ I) :
      -(120*b/H^2*(2*M)^k/(k.factorial : ℝ))*(amplitude N v/v)≤
        ∑ a ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
          signedPart e ∅ L y N (p*a) := by
    have hm := interval_cofactor_mass_le (S k) Q k hQmass (hS k hk)
    have hh := Finset.sum_le_sum (fun a ha =>
      flat_unallocated_row_floor (hI k hk) he hH hNv hy hL (hS k hk a ha).1
        (hS k hk a ha).2.1 (hmin k hk a ha) (hP k hk a ha)
        (howner k hk a ha) hpeak hsign (hflat k hk a ha))
    simp only [neg_mul] at hh
    rw [Finset.sum_neg_distrib,← Finset.sum_mul,← Finset.mul_sum] at hh
    have ht := mul_le_mul_of_nonneg_left hm (by positivity : 0≤120*b/H^2*(2 : ℝ)^k)
    have ht' := mul_le_mul_of_nonneg_right ht hf0
    have heq : (120*b/H^2*(2 : ℝ)^k*(M^k/(k.factorial : ℝ))*(amplitude N v/v))=
        (120*b/H^2*(2*M)^k/(k.factorial : ℝ))*(amplitude N v/v) := by
      rw [mul_pow]
      ring
    rw [heq] at ht'
    simpa only [neg_mul] using (neg_le_neg ht').trans hh
  have hh := Finset.sum_le_sum hrow
  simp only [neg_mul] at hh
  rw [Finset.sum_neg_distrib,← Finset.sum_mul] at hh
  have hc0 : 0≤120*b/H^2 := by positivity
  have hp := mul_le_mul_of_nonneg_right (sum_count_price_le I hM hc0) hf0
  convert (neg_le_neg hp).trans hh using 1 <;>
    first | rfl | (simp only [div_eq_mul_inv]; ring)

/-- The finite small-prime head is kept exactly, rather than assuming a
roughness cutoff on the cofactor. Its size is not numerically evaluated. -/
def smallPrimeHeadMass : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊exp (5000 : ℝ)⌋₊, (p : ℝ)⁻¹

/-- Fixed positive Euler cost of the exact small-prime head. -/
def smallPrimeHeadCost : ℝ :=
  16*exp (2*(smallPrimeHeadMass+1/5000))/(5000 : ℝ)^2

theorem smallPrimeHeadCost_pos : 0<smallPrimeHeadCost := by
  unfold smallPrimeHeadCost
  positivity

/-- Actual reciprocal-prime mass with NO lower cutoff. The fixed head
is exact; the already proved leading-one large-range bound pays the tail. -/
theorem whole_prime_mass_le (Q : Finset ℕ) {H : ℝ} (hH : 5000≤H)
    (hQ : ∀ p ∈ Q, p.Prime ∧ log p≤4*H) :
    (∑ p ∈ Q,(p : ℝ)⁻¹) ≤ smallPrimeHeadMass+log (4*H/5000)+1/5000 := by
  let P := Nat.primesLE ⌊exp (5000 : ℝ)⌋₊
  let T := (Finset.Ioc ⌊exp (5000 : ℝ)⌋₊ ⌊exp (4*H)⌋₊).filter Nat.Prime
  have hsub : Q \ P⊆T := by
    intro p hp
    obtain ⟨hpQ,hpP⟩ := Finset.mem_sdiff.mp hp
    have hpp := (hQ p hpQ).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hpp⟩
    · apply lt_of_not_ge
      intro h
      exact hpP (Nat.mem_primesLE.mpr ⟨h,hpp⟩)
    · apply Nat.le_floor
      simpa only [exp_log (by exact_mod_cast hpp.pos : (0 : ℝ)<p)] using
        exp_le_exp.mpr (hQ p hpQ).2
  have hsplit : (∑ p ∈ Q,(p : ℝ)⁻¹)=
      (∑ p ∈ Q∩P,(p : ℝ)⁻¹)+(∑ p ∈ Q \ P,(p : ℝ)⁻¹) := by
    rw [← Finset.sum_union (by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2)]
    congr 1
    ext p
    simp
    tauto
  have hhead : (∑ p ∈ Q∩P,(p : ℝ)⁻¹) ≤ smallPrimeHeadMass :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by intro p _ _; positivity)
  have htail := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (by intro p _ _; positivity)).trans
      (prime_interval_mass_le (by norm_num : (5000 : ℝ)≤5000) (by linarith : (5000 : ℝ)≤4*H))
  rw [hsplit]
  linarith only [hhead,htail]

/-- The all-count Euler price remains QUADRATIC with every small prime
present. Thus it cancels the restored inverse-square owner-log saving. -/
theorem whole_count_exponential_le (Q : Finset ℕ) {H : ℝ} (hH : 5000≤H)
    (hQ : ∀ p ∈ Q, p.Prime ∧ log p≤4*H) :
    exp (2*(∑ p ∈ Q,(p : ℝ)⁻¹)) ≤ smallPrimeHeadCost*H^2 := by
  have hH0 : 0<H := by linarith
  have hh := exp_le_exp.mpr (mul_le_mul_of_nonneg_left (whole_prime_mass_le Q hH hQ)
    (by norm_num : (0 : ℝ)≤2))
  have heq : exp (2*(smallPrimeHeadMass+log (4*H/5000)+1/5000))=
      smallPrimeHeadCost*H^2 := by
    rw [show 2*(smallPrimeHeadMass+log (4*H/5000)+1/5000)=
        2*(smallPrimeHeadMass+1/5000)+2*log (4*H/5000) by ring,
      exp_add,show 2*log (4*H/5000)=log ((4*H/5000)^2) by rw [log_pow]; norm_num,
      exp_log (by positivity)]
    unfold smallPrimeHeadCost
    ring
  exact hh.trans_eq heq

/-- The entire flat-response population, including EVERY small cofactor
prime and every selected growing count, has one signed period price.
Only the actual least-prime upper bound `b` survives; no roughness
cutoff or exponential count penalty remains in this price. -/
theorem whole_small_flat_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (S : ℕ → Finset ℕ) (Q : Finset ℕ) {v y L H b : ℝ}
    (hI : ∀ k ∈ I,2≤k) (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L) (hb : 0≤b)
    (hQ : ∀ p ∈ Q,p.Prime ∧ log p≤4*H)
    (hS : ∀ k ∈ I,∀ a ∈ S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ Q)
    (hmin : ∀ k ∈ I,∀ a ∈ S k,log a.minFac≤b)
    (hP : ∀ k ∈ I,∀ a ∈ S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k ∈ I,∀ a ∈ S k,∀ q ∈ a.primeFactors,log q≤v-Real.pi/y-log a)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0)
    (hflat : ∀ k ∈ I,∀ a ∈ S k,∀ T ∈ Set.Icc (v-Real.pi/y) (v+Real.pi/y),
      response L T a=response L v a) :
    -(120*smallPrimeHeadCost*b)*(amplitude N v/v)≤
      ∑ k ∈ I,∑ a ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  have hH0 : 0<H := by linarith
  have hv0 : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hh := flat_all_counts_floor I N e S Q hI he hH hNv hy hL hb
    (Finset.sum_nonneg (fun p _ => by positivity)) (le_refl _) hS hmin hP howner hpeak hsign hflat
  have hcost := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (whole_count_exponential_le Q hH hQ)
      (show 0≤120*b by positivity)) (sq_nonneg H)
  have heq : 120*b*(smallPrimeHeadCost*H^2)/H^2=120*smallPrimeHeadCost*b := by
    field_simp
  rw [heq] at hcost
  have hp := mul_le_mul_of_nonneg_right hcost
    (div_nonneg (amplitude_nonneg N hv0.le) hv0.le)
  simp only [neg_mul] at hh
  simpa only [neg_mul] using (neg_le_neg hp).trans hh

end RiemannGaussian.ZetaRieszSmallCofactorCancellation
