/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCubicCutoffRows
import RiemannGaussian.ZetaRieszTangentCubicCredit

/-!
# Remove independently paid incidences before pricing the whole floor

The counted row is a literal collection of marked divisor incidences,
not a collection of complete product labels. Its signed cutoff increment
is retained exactly. Subtract it before measuring complete cutoff periods;
pay only its already proved signed total. In particular, a source-small
packet need not have small absolute cutoff variation.

The partial-incidence majorant below also justifies the native count crop.
It does not infer decay of a partial packet from decay of a complete one.
No numerical whole-floor bound is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszPaidIncidenceFloor
open ZetaRieszSignedConvolution ZetaRieszCutoffPeriodFloor
open ZetaRieszUnsignedDivisorError ZetaRieszJointAllocation
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeEndpoint

/-- A selected divisor response retains its signs. The original weight
and phase are inserted after this exact finite coefficient. -/
def partialHinge (L : ℝ) (p : ℕ) (D : Finset (ℕ×ℕ)) : ℝ :=
  ∑ db ∈ D,(μ db.2 : ℝ)*pairHinge L p db.2

/-- Arbitrary partial selections have a genuine original majorant. This
is used ONLY for the independently paid high-count difference. -/
theorem partialHinge_majorant {p a : ℕ} (hp : p.Prime) (ha : 0<a)
    (L : ℝ) (D : Finset (ℕ×ℕ))
    (hD : D ⊆ a.divisorsAntidiagonal) :
    |partialHinge L p D| ≤ zetaMoebiusLogMajorant (p*a) := by
  exact partial_hinge_majorant hp.pos ha D hD L

/-- The full original allocation, derivative factor and partial Möbius
response satisfy the factor-two count-payment hypothesis. -/
theorem partialCoefficient_majorant {p a : ℕ} (hp : p.Prime) (ha : 0<a)
    {L : ℝ} (hL : 0<L) (hlog : log (p*a : ℕ)≤2*L)
    (A : Finset ℕ) (N : ℕ) (D : Finset (ℕ×ℕ))
    (hD : D ⊆ a.divisorsAntidiagonal) :
    ‖(((1-boundedShare A N (p*a))*log (p*a : ℕ)/L*
      partialHinge L p D : ℝ) : ℂ)‖ ≤ 2*zetaMoebiusLogMajorant (p*a) := by
  have ht := boundedShare_bounds A N (p*a)
  have hb : 0≤(1-boundedShare A N (p*a))*log (p*a : ℕ)/L := by
    exact div_nonneg (mul_nonneg (by linarith) (log_natCast_nonneg _)) hL.le
  have hb2 : (1-boundedShare A N (p*a))*log (p*a : ℕ)/L≤2 := by
    apply (div_le_iff₀ hL).mpr
    have hm := mul_le_mul_of_nonneg_right
      (show 1-boundedShare A N (p*a)≤1 by linarith) (log_natCast_nonneg (p*a))
    linarith
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hb]
  exact mul_le_mul hb2 (partialHinge_majorant hp ha L D hD)
    (abs_nonneg _) (by norm_num)

/-- The two reflected hinges are an EXACT corrected-profile difference.
Thus the paid row can be removed on the original cutoff axis. -/
theorem pairHinge_eq_profile_diff {p b X : ℕ} (hp : 0<p) (hb : 0<b)
    (hpb : p*b≤X) (L : ℝ) :
    pairHinge L p b=correctedProfile X L 1 0 (p*b)-correctedProfile X L 1 0 b := by
  have hbX : b≤X := (by nlinarith : b≤p*b).trans hpb
  have hl : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
  simp only [pairHinge,correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile,
    if_pos hpb,if_pos hbX,zero_mul,add_zero,one_mul,hl]
  have hf x : max 0 (x-L)=max 0 (L-x)+x-L := by
    rcases le_total L x with h | h
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith),max_eq_right (by linarith)]
      ring
  rw [hf (log p+log b),hf (log b)]
  ring

/-- A literal two-endpoint prefix on the common cutoff axis. -/
def hingeIncrement (X p b : ℕ) (L : ℝ) (k : ℕ) : ℝ :=
  ((if p*b≤k then (1 : ℝ) else 0)-(if b≤k then 1 else 0))*
    (correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1))

private theorem prefix_delta (X d : ℕ) (f : ℕ→ℝ) (hd : d∈Finset.Icc 1 X)
    (hend : f (X+1)=0) :
    (∑ k ∈ Finset.Icc 1 X,(if d≤k then (1 : ℝ) else 0)*(f k-f (k+1)))=f d := by
  have he := ZetaRieszSignedCutoffEnergy.abel_profile X f
    (fun i => if i=d then (1 : ℝ) else 0) hend
  have hs k : (∑ i ∈ Finset.Icc 1 k,if i=d then (1 : ℝ) else 0)=
      if d≤k then 1 else 0 := by
    have hd0 := (Finset.mem_Icc.mp hd).1
    by_cases h : d≤k
    · simp [h,Finset.mem_Icc,hd0]
    · simp [h,Finset.mem_Icc]
  simp only [hs] at he
  simpa only [mul_ite,ite_mul,mul_one,one_mul,mul_zero,zero_mul,
    Finset.sum_ite_eq',if_pos hd] using he.symm

theorem sum_hingeIncrement {p b X : ℕ} (hp : 0<p) (hb : 0<b)
    (hpb : p*b≤X) (L : ℝ) :
    (∑ k ∈ Finset.Icc 1 X,hingeIncrement X p b L k)=pairHinge L p b := by
  have hbX : b≤X := (by nlinarith : b≤p*b).trans hpb
  have hf : correctedProfile X L 1 0 (X+1)=0 := by
    simp [correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile]
  simp only [hingeIncrement,sub_mul,Finset.sum_sub_distrib]
  rw [prefix_delta X (p*b) _ (Finset.mem_Icc.mpr ⟨by nlinarith,hpb⟩) hf,
    prefix_delta X b _ (Finset.mem_Icc.mpr ⟨hb,hbX⟩) hf,
    ← pairHinge_eq_profile_diff hp hb hpb]

/-- Remove a signed paid response before period clipping. This pays its
signed TOTAL, not its possibly large absolute cutoff variation. -/
theorem pruned_block_floor (K : Finset ℕ) (g : ℕ→ℕ) (t paid : ℕ→ℝ)
    {E : ℝ} (hpaid : |∑ k ∈ K,paid k|≤E) :
    -blockCost K g (fun k=>t k-paid k)-E≤∑ k ∈ K,t k := by
  have hf := block_floor K g (fun k=>t k-paid k)
  rw [Finset.sum_sub_distrib] at hf
  have hp := (abs_le.mp hpaid).1
  linarith

/-- Choose the better of the old price and the pruned price, funding
the paid signed total once. No monotonicity under deletion is assumed. -/
theorem pruned_block_floor_min (K : Finset ℕ) (g : ℕ→ℕ) (t paid : ℕ→ℝ)
    {E : ℝ} (hpaid : |∑ k ∈ K,paid k|≤E) :
    -min (blockCost K g t) (blockCost K g (fun k=>t k-paid k)+E)≤∑ k ∈ K,t k := by
  have hold := block_floor K g t
  have hnew := pruned_block_floor K g t paid hpaid
  rcases le_total (blockCost K g t) (blockCost K g (fun k=>t k-paid k)+E) with h | h
  · rwa [min_eq_left h]
  · rw [min_eq_right h]
    linarith

open ZetaRieszParityPacket (coreBand coreResponse)
open ZetaRieszFineDivisorRows (lower upper)

/-- Original row indices, with every nonzero physical/core condition.
The product and divisor incidence map is checked injective below. -/
def rowIndices (u : ℝ) (j : ℕ) : Finset (Σ _pb : ℕ×ℕ, ℕ×ℕ) :=
  let N := dyadicMomentOrder j
  ((ZetaRieszCubicCutoffRows.cutoffRows u N).sigma (fun pb =>
    (Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2)).product
      (ZetaRieszRoughCutoffRows.cutoffDivisors N pb.1 pb.2))).filter (fun i =>
    i.1.1*(i.1.2*i.2.1) ∈ coreBand u N (dyadicPrimeCount j) ∧
      sieve (ZetaRieszRoughCutoffRows.forbidden i.1.1 i.1.2) i.2.1 ≠ 0)

/-- Map a frozen row, extension and divisor to its original product/divisor incidence. -/
def incidence (i : Σ _pb : ℕ×ℕ, ℕ×ℕ) : ℕ×(ℕ×ℕ) :=
  (i.1.1*(i.1.2*i.2.1),(i.2.1*i.2.2,i.1.2/i.2.2))

private theorem moment_ge_32 (j : ℕ) : 32≤dyadicMomentOrder j := by
  have hk := four_le_dyadicPrimeCount j
  unfold dyadicMomentOrder
  nlinarith

theorem rowIndices_incidence_injective (u : ℝ) (j : ℕ) :
    Set.InjOn incidence (rowIndices u j : Set (Σ _pb : ℕ×ℕ, ℕ×ℕ)) := by
  intro i hi k hk heq
  obtain ⟨hi,hs⟩ := Finset.mem_filter.mp hi
  obtain ⟨hk,ht⟩ := Finset.mem_filter.mp hk
  obtain ⟨hi,hei⟩ := Finset.mem_sigma.mp hi
  obtain ⟨hk,hek⟩ := Finset.mem_sigma.mp hk
  obtain ⟨hp,he,hd⟩ := ZetaRieszCubicCutoffRows.cutoff_incidence_injective
    (moment_ge_32 j) hi hk (Finset.mem_product.mp hei).1
      (Finset.mem_product.mp hek).1 hs.2 ht.2
      (Finset.mem_product.mp hei).2 (Finset.mem_product.mp hek).2 heq
  cases i with | mk i v =>
    cases k with | mk k w =>
      simp only at hp he hd
      subst k
      exact congrArg (Sigma.mk i) (Prod.ext he hd)

/-- The exact paid ORIGINAL product/divisor incidences, without any
new support completion. -/
def paidIncidences (u : ℝ) (j : ℕ) : Finset (ℕ×(ℕ×ℕ)) :=
  (rowIndices u j).image incidence

theorem paidIncidences_data {u : ℝ} {j n : ℕ} {db : ℕ×ℕ}
    (h : (n,db)∈paidIncidences u j) :
    n∈coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧ Squarefree n ∧
      db∈(n/largestPrime n).divisorsAntidiagonal := by
  obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp h
  obtain ⟨hi,hs⟩ := Finset.mem_filter.mp hi
  obtain ⟨hi,he⟩ := Finset.mem_sigma.mp hi
  have hd := ZetaRieszCubicCutoffRows.cutoff_original_incidence (moment_ge_32 j)
    hi (Finset.mem_product.mp he).1 hs.2 (Finset.mem_product.mp he).2
  have hn := congrArg Prod.fst heq
  have hdb := congrArg Prod.snd heq
  change i.1.1*(i.1.2*i.2.1)=n at hn
  change (i.2.1*i.2.2,i.1.2/i.2.2)=db at hdb
  exact ⟨hn ▸ hs.1,hn ▸ hd.1,by simpa only [hn,hdb] using hd.2.2.1⟩

/-- The selected original divisor incidences at one product label. -/
def paidDivisors (u : ℝ) (j n : ℕ) : Finset (ℕ×ℕ) :=
  ((paidIncidences u j).filter (fun v=>v.1=n)).image Prod.snd

theorem mem_paidDivisors (u : ℝ) (j n : ℕ) (db : ℕ×ℕ) :
    db∈paidDivisors u j n ↔ (n,db)∈paidIncidences u j := by
  simp only [paidDivisors,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨m,dc⟩,⟨hm,hmn⟩,hdc⟩
    simp only at hmn hdc
    simpa only [hmn,hdc] using hm
  · intro h
    exact ⟨(n,db),⟨h,rfl⟩,rfl⟩

theorem paidDivisors_subset (u : ℝ) (j n : ℕ) :
    paidDivisors u j n ⊆ (n/largestPrime n).divisorsAntidiagonal := by
  intro db hdb
  exact (paidIncidences_data ((mem_paidDivisors u j n db).mp hdb)).2.2

private theorem sum_incidence_fibres {α : Type*} [AddCommMonoid α]
    (T : Finset (ℕ×(ℕ×ℕ))) (f : ℕ→(ℕ×ℕ)→α) :
    (∑ v∈T,f v.1 v.2)=
      ∑ n∈T.image Prod.fst,∑ db∈(T.filter (fun v=>v.1=n)).image Prod.snd,f n db := by
  have he := Finset.sum_fiberwise_of_maps_to (s:=T) (t:=T.image Prod.fst)
    (g:=Prod.fst) (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) (fun v=>f v.1 v.2)
  rw [← he]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_image (by
    intro v hv w hw he
    exact Prod.ext ((Finset.mem_filter.mp hv).2.trans
      (Finset.mem_filter.mp hw).2.symm) he)]
  exact Finset.sum_congr rfl (fun v hv=>by rw [(Finset.mem_filter.mp hv).2])

/-- The literal canonical-owner allocation, factorial weight and full phase. -/
def incidenceWeight (u y : ℝ) (j n : ℕ) : ℂ :=
  let N := dyadicMomentOrder j
  phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
    (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)

/-- The checked injective map reconnects the paid packet to the original
cutoff coordinates. No atom or repeated incidence is inserted. -/
theorem literalCutoffPacket_eq_incidences (u y : ℝ) (j : ℕ) :
    ZetaRieszCubicCutoffRows.literalCutoffPacket u y j=
      ∑ v∈paidIncidences u j,(incidenceWeight u y j v.1).re*(μ v.2.2 : ℝ)*
        pairHinge (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          (largestPrime v.1) v.2.2 := by
  rw [paidIncidences,Finset.sum_image (rowIndices_incidence_injective u j),rowIndices,
    Finset.sum_filter,Finset.sum_sigma]
  unfold ZetaRieszCubicCutoffRows.literalCutoffPacket
  dsimp only
  apply Finset.sum_congr rfl
  intro pb hpb
  rw [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hcore : pb.1*(pb.2*e)∈coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)
  · simp only [if_pos hcore]
    apply Finset.sum_congr rfl
    intro δ hδ
    by_cases hs : sieve (ZetaRieszRoughCutoffRows.forbidden pb.1 pb.2) e=0
    · simp only [hs,ne_eq,not_true_eq_false,and_false,if_false,mul_zero]
    · have hd := ZetaRieszCubicCutoffRows.cutoff_original_incidence (moment_ge_32 j)
        hpb he hs hδ
      have hg := ZetaRieszCubicCutoffRows.cutoff_row_geometry hpb
      have heq : sieve (ZetaRieszRoughCutoffRows.forbidden pb.1 pb.2) e=1 := by
        unfold sieve at *
        split_ifs at * <;> simp_all
      simp [incidence,incidenceWeight,hd.2.1,
        Nat.mul_div_cancel_left _ hg.1.pos,heq,hcore]
  · simp [hcore]

theorem literalCutoffPacket_eq_divisors (u y : ℝ) (j : ℕ) :
    ZetaRieszCubicCutoffRows.literalCutoffPacket u y j=
      ∑ n∈(paidIncidences u j).image Prod.fst,
        (incidenceWeight u y j n).re*
          partialHinge (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
            (largestPrime n) (paidDivisors u j n) := by
  rw [literalCutoffPacket_eq_incidences,
    sum_incidence_fibres (paidIncidences u j) (fun n db=>
      (incidenceWeight u y j n).re*(μ db.2 : ℝ)*
        pairHinge (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          (largestPrime n) db.2)]
  simp only [paidDivisors,partialHinge,Finset.mul_sum,mul_assoc]

/-- Original product labels carrying at least one selected paid incidence. -/
def paidLabels (u : ℝ) (j : ℕ) : Finset ℕ :=
  (paidIncidences u j).image Prod.fst

theorem paidLabels_data {u : ℝ} {j n : ℕ} (hn : n∈paidLabels u j) :
    n∈coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧ Squarefree n := by
  obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hn
  obtain ⟨hc,hs,_⟩ := paidIncidences_data hv
  simpa only [heq] using And.intro hc hs

private theorem owner_product {u : ℝ} {j n : ℕ} (hn : n∈paidLabels u j) :
    largestPrime n*(n/largestPrime n)=n := by
  have hc := ZetaRieszJointPrimeEnergy.core_count (paidLabels_data hn).1
  exact Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors
    (ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2≤n.primeFactors.card)))

/-- The signed partial hinge coefficient with the original owner allocation. -/
def paidCoefficient (u : ℝ) (j n : ℕ) : ℂ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n}
  (((1-boundedShare A N n)*log n/L*
    partialHinge L (largestPrime n) (paidDivisors u j n) : ℝ) : ℂ)

theorem paidCoefficient_kernel {u : ℝ} (y : ℝ) {j n : ℕ}
    (hn : n∈paidLabels u j) :
    paidCoefficient u j n*zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n=
      incidenceWeight u y j n*
        (partialHinge (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          (largestPrime n) (paidDivisors u j n) : ℂ) := by
  simp only [paidCoefficient,incidenceWeight,phaseWeight,owner_product hn]
  push_cast
  ring

theorem paidCoefficient_bound {u : ℝ} {j n : ℕ} (hn : n∈paidLabels u j)
    (hlog : log n≤2*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    ‖paidCoefficient u j n‖≤2*zetaMoebiusLogMajorant n := by
  have hd := ZetaRieszShortDivisorOrbits.core_data (paidLabels_data hn).1
    (paidLabels_data hn).2
  have hp := owner_product hn
  have h := partialCoefficient_majorant hd.1 (Nat.pos_of_ne_zero hd.2.1.ne_zero)
    (SquarefreeVaughanLogSource.length_pos u (dyadicMomentOrder j))
    (hp.symm ▸ hlog) (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
      {largestPrime n}) (dyadicMomentOrder j) (paidDivisors u j n)
      (paidDivisors_subset u j n)
  simpa only [paidCoefficient,hp] using h

theorem literalCutoffPacket_eq_coefficients (u y : ℝ) (j : ℕ) :
    ZetaRieszCubicCutoffRows.literalCutoffPacket u y j=
      (∑ n∈paidLabels u j,paidCoefficient u j n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  rw [literalCutoffPacket_eq_divisors,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [paidCoefficient_kernel y hn]
  simp [Complex.mul_re]

/-- Restrict the same original incidence packet to the CURRENT native
count crop. This deletes no cofactor or phase information. -/
def nativePaidPacket (u y : ℝ) (j : ℕ) : ℝ :=
  (∑ n∈(paidLabels u j).filter (fun n=>
      n.primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j),
    paidCoefficient u j n*zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

theorem nativePaid_support {u : ℝ} {j n : ℕ}
    (hn : n∈(paidLabels u j).filter (fun n=>
      n.primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j)) :
    n∈coreBand u (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j) ∧
      Squarefree n := by
  obtain ⟨hn,hcount⟩ := Finset.mem_filter.mp hn
  have hd := paidLabels_data hn
  rw [ZetaRieszJointCountFloor.coreBand_count_filter u (dyadicMomentOrder j)
    (dyadicPrimeCount j) _ (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).2]
  exact ⟨Finset.mem_filter.mpr ⟨hd.1,hcount⟩,hd.2⟩

theorem eventually_nativePaid_count_error {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*
        (ZetaRieszCubicCutoffRows.literalCutoffPacket u y j-nativePaidPacket u y j)|≤
          ZetaRieszNearCriticalCountPayment.allowance j := by
  filter_upwards [ZetaRieszNearCriticalCountPayment.eventually_nearCritical_count_sum_bound,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent (by linarith : 0<u)
        (by norm_num : (0 : ℝ)≤11/16)
        (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source))] with j hj hL
  let S := (paidLabels u j).filter (fun n=>
    ZetaRieszNearCriticalCountPayment.countCeiling j≤n.primeFactors.card)
  have hb := hj S (paidCoefficient u j) y u (by linarith) hU
    (fun n hn=>by
      have hc := (paidLabels_data (Finset.mem_filter.mp hn).1).1
      have ht := (Finset.mem_filter.mp hc).2.2
      have hl : log n≤2*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
        nlinarith [ht,hL]
      exact paidCoefficient_bound (Finset.mem_filter.mp hn).1 hl)
    (fun n hn=>(paidLabels_data (Finset.mem_filter.mp hn).1).2)
    (fun n hn=>(Finset.mem_filter.mp
      (paidLabels_data (Finset.mem_filter.mp hn).1).1).2.2)
    (fun n hn=>by
      have hc := (Finset.mem_filter.mp hn).2
      unfold ZetaRieszNearCriticalCountPayment.countCeiling at hc
      omega)
  have he : ZetaRieszCubicCutoffRows.literalCutoffPacket u y j-nativePaidPacket u y j=
      (∑ n∈S,paidCoefficient u j n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
    rw [literalCutoffPacket_eq_coefficients,nativePaidPacket,
      ← Complex.sub_re,← Finset.sum_filter_add_sum_filter_not (paidLabels u j)
        (fun n=>ZetaRieszNearCriticalCountPayment.countCeiling j≤n.primeFactors.card)]
    simp only [not_le,add_sub_cancel_right,S]
  rw [he]
  have h := (Complex.abs_re_le_norm ((u : ℂ)^(dyadicMomentOrder j+1)*
    ∑ n∈S,paidCoefficient u j n*zetaPrimeLogKernel (dyadicMomentOrder j)
      (3/2+Complex.I*y) n)).trans hb
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,ZetaRieszNearCriticalCountPayment.allowance] using h

/-- One source-small price for the independently paid row and its
native count boundary; none of its cutoff variation is charged. -/
def nativePaidBudget (y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszCubicCutoffRows.cubicRowBudget y (dyadicMomentOrder j)+
    ZetaRieszRoughCutoffRows.cutoffEndpointBudget (dyadicMomentOrder j)+
      ZetaRieszNearCriticalCountPayment.allowance j

theorem tendsto_nativePaidBudget (y : ℝ) :
    Tendsto (nativePaidBudget y) atTop (𝓝 0) := by
  have h := ((ZetaRieszCubicCutoffRows.tendsto_cubicRowBudget y).comp
    tendsto_dyadicMomentOrder).add
      (ZetaRieszRoughCutoffRows.tendsto_cutoffEndpointBudget.comp tendsto_dyadicMomentOrder)
  change Tendsto (fun j=>ZetaRieszCubicCutoffRows.cubicRowBudget y (dyadicMomentOrder j)+
    ZetaRieszRoughCutoffRows.cutoffEndpointBudget (dyadicMomentOrder j)+
      ZetaRieszNearCriticalCountPayment.allowance j) atTop (𝓝 0)
  simpa only [Function.comp_def,add_zero] using h.add
    ZetaRieszNearCriticalCountPayment.tendsto_allowance

theorem eventually_nativePaidPacket_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*nativePaidPacket u y j|≤nativePaidBudget y j := by
  filter_upwards [eventually_nativePaid_count_error hu hU y,
    ZetaRieszCubicCutoffRows.eventually_literalCutoffPacket_bound hu hU hy] with j he hp
  have hs := abs_add_le
    (u^(dyadicMomentOrder j+1)*ZetaRieszCubicCutoffRows.literalCutoffPacket u y j)
    (-(u^(dyadicMomentOrder j+1)*(ZetaRieszCubicCutoffRows.literalCutoffPacket u y j-
      nativePaidPacket u y j)))
  have hf : u^(dyadicMomentOrder j+1)*ZetaRieszCubicCutoffRows.literalCutoffPacket u y j-
      u^(dyadicMomentOrder j+1)*(ZetaRieszCubicCutoffRows.literalCutoffPacket u y j-
        nativePaidPacket u y j)=u^(dyadicMomentOrder j+1)*nativePaidPacket u y j := by ring
  simp only [← sub_eq_add_neg,hf,abs_neg] at hs
  exact hs.trans (add_le_add hp he)

theorem tendsto_nativePaidPacket {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j=>u^(dyadicMomentOrder j+1)*nativePaidPacket u y j) atTop (𝓝 0) := by
  exact squeeze_zero_norm' (by
    simpa only [Real.norm_eq_abs] using eventually_nativePaidPacket_bound hu hU hy)
      (tendsto_nativePaidBudget y)

/-- The current whole-floor core with its literal near-critical count crop. -/
def nativeLabels (u : ℝ) (j : ℕ) : Finset ℕ :=
  coreBand u (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)

/-- The original finite cutoff axis endpoint for the current whole-floor labels. -/
def nativeEndpoint (u : ℝ) (j : ℕ) : ℕ := max 1 ((nativeLabels u j).sup id)

/-- The exact paid increment on the SAME cutoff axis as the whole native
floor, not a scalar debit appended to a sector inequality. -/
def nativePaidIncrement (u y : ℝ) (j k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let X := nativeEndpoint u j
  let L := SquarefreeVaughanLogSource.length u N
  ∑ n∈(paidLabels u j).filter (fun n=>
      n.primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j),
    ∑ db∈paidDivisors u j n,
      u^(N+1)*(incidenceWeight u y j n).re*(μ db.2 : ℝ)*
        hingeIncrement X (largestPrime n) db.2 L k

theorem sum_nativePaidIncrement (u y : ℝ) (j : ℕ) :
    (∑ k∈Finset.Icc 1 (nativeEndpoint u j),nativePaidIncrement u y j k)=
      u^(dyadicMomentOrder j+1)*nativePaidPacket u y j := by
  unfold nativePaidIncrement
  dsimp only
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (s:=Finset.Icc 1 (nativeEndpoint u j))]
  unfold nativePaidPacket
  rw [Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 := (paidLabels_data (Finset.mem_filter.mp hn).1).2.ne_zero
  have hnX : n≤nativeEndpoint u j :=
    (Finset.le_sup (f:=id) (nativePaid_support hn).1).trans (le_max_right _ _)
  have hd := ZetaRieszShortDivisorOrbits.core_data (paidLabels_data
    (Finset.mem_filter.mp hn).1).1 (paidLabels_data (Finset.mem_filter.mp hn).1).2
  rw [paidCoefficient_kernel y (Finset.mem_filter.mp hn).1]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    partialHinge,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro db hdb
  have hc := paidDivisors_subset u j n hdb
  have hb : 0<db.2 := Nat.pos_of_mem_divisors
    (Nat.snd_mem_divisors_of_mem_antidiagonal hc)
  have hdvd := Nat.mul_dvd_mul_left (largestPrime n) (Nat.dvd_of_mem_divisors
    (Nat.snd_mem_divisors_of_mem_antidiagonal hc))
  rw [owner_product (Finset.mem_filter.mp hn).1] at hdvd
  have hpb : largestPrime n*db.2≤nativeEndpoint u j :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd).trans hnX
  rw [← Finset.mul_sum,sum_hingeIncrement hd.1.pos hb hpb]
  ring

/-- The paid correction creates no early/empty-prefix debit. Its exact
two-hinge profile has the same flat pre-hinge region as the native floor. -/
theorem nativePaidIncrement_zero_early {u y : ℝ} {j k : ℕ}
    (hk : k∈Finset.Icc 1 (nativeEndpoint u j))
    (hL : log (k+1 : ℕ)≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    nativePaidIncrement u y j k=0 := by
  have hz : correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0 k=
    correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0 (k+1) := by
    by_contra h
    exact (low_cutoff_inactive (nativeEndpoint u j) k hL)
      (Finset.mem_filter.mpr ⟨hk,h⟩)
  simp only [nativePaidIncrement,hingeIncrement,hz,sub_self,mul_zero,
    Finset.sum_const_zero]

/-- The old whole null-corrected increment is retained, with the same
bounded imaginary tilt and every previous joined correction. -/
def nativeStep (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := (nativeLabels u j).filter Squarefree
  let X := nativeEndpoint u j
  let W := ZetaRieszComplexProjection.sourceWeight A L u y N
  ZetaRieszComplexNullFloor.increment X N S W L
    (ZetaRieszComplexNullFloor.bestParameters X N S W L (cutoffPeriod y) 4) k+
      ZetaRieszTangentCubicCredit.extendedIncrement X N S W L q a k

/-- The same bounded imaginary tilt used by the previous native floor. -/
def nativeTilt (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  ZetaRieszComplexNullFloor.bestParameters (nativeEndpoint u j) N
    ((nativeLabels u j).filter Squarefree)
    (ZetaRieszComplexProjection.sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      L u y N) L (cutoffPeriod y) 4 0

theorem nativeTilt_bound (u y : ℝ) (j : ℕ) : |nativeTilt u y j|≤4 := by
  unfold nativeTilt
  simpa only [abs_of_nonneg (by norm_num : (0 : ℝ)≤4)] using
    ZetaRieszComplexNullFloor.bestParameters_bound _ _ _ _ _ _ (4 : ℝ) 0

theorem sum_nativeStep (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) :
    let Q := (u : ℂ)^(dyadicMomentOrder j+1)*
      coreResponse u y (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
    (∑ k∈Finset.Icc 1 (nativeEndpoint u j),nativeStep u y j q a k)=
      Q.re-nativeTilt u y j*Q.im := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := (nativeLabels u j).filter Squarefree
  have hs : ∀ n∈S,Squarefree n := fun _ hn=>(Finset.mem_filter.mp hn).2
  have hc : ∀ n∈S,3≤n.primeFactors.card := fun _ hn=>
    ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp hn).1
  have hX : ∀ n∈S,n≤nativeEndpoint u j := fun _ hn=>
    (Finset.le_sup (f:=id) (Finset.mem_filter.mp hn).1).trans (le_max_right _ _)
  unfold nativeStep
  dsimp only
  rw [Finset.sum_add_distrib,
    ZetaRieszComplexNullFloor.sum_increment_eq _ _ _ _ _ hs hc hX,
    ZetaRieszTangentCubicCredit.sum_extendedIncrement_zero _ _ _ _ _ q a hs hc hX,add_zero]
  have he := ZetaRieszComplexProjection.native_prefix_eq
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) (nativeLabels u j) L u y N
      (fun _ hn=>ZetaRieszJointPrimeEnergy.core_count hn)
  dsimp only at he
  change ZetaRieszComplexProjection.complexPrefix (nativeEndpoint u j) S
    (ZetaRieszComplexProjection.sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      L u y N) (correctedProfile (nativeEndpoint u j) L 1 0)=
    (u : ℂ)^(N+1)*coreResponse u y N
      (ZetaRieszNearCriticalCountPayment.countCeiling j) at he
  rw [he]
  rfl

/-- Price only the joined signed remainder AFTER literal paid rows have
been removed. The full counts, phase and all boundary groups remain. -/
def nativePrunedCost (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
    (fun k=>nativeStep u y j q a k-nativePaidIncrement u y j k)

theorem eventually_joined_floor_pruned {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -nativePrunedCost u y j (q j) (a j)-nativePaidBudget y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_nativePaidPacket_bound hu hU hy] with j hp
  have hf := pruned_block_floor (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
    (nativeStep u y j (q j) (a j)) (nativePaidIncrement u y j)
      (E:=nativePaidBudget y j)
      (by rw [sum_nativePaidIncrement]; exact hp)
  rw [sum_nativeStep] at hf
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have ht := nativeTilt_bound u y j
  have him := abs_mul (nativeTilt u y j) Q.im
  have hscale := mul_le_mul_of_nonneg_right ht (abs_nonneg Q.im)
  have hneg := neg_abs_le (nativeTilt u y j*Q.im)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have hi : |Q.im|≤|P.im|+‖Q-P‖ := by
    have htri := abs_sub_le Q.im P.im 0
    have hd : |Q.im-P.im|≤‖Q-P‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (Q-P)
    simp only [sub_zero] at htri
    linarith only [htri,hd]
  change -nativePrunedCost u y j (q j) (a j)-nativePaidBudget y j≤
    Q.re-nativeTilt u y j*Q.im at hf
  change -nativePrunedCost u y j (q j) (a j)-nativePaidBudget y j-
    (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,hscale,him,hneg,hr,hi]

/-- Alternative prices against the SAME whole carrier. Paid signed
rows are funded once; previous null credits are not added twice. -/
def nativePrunedPrice (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszComplexNullFloor.nativeCost u y j-
    ZetaRieszTangentCubicCredit.nativeTangentCredit u y j q a)
      (nativePrunedCost u y j q a+nativePaidBudget y j)

theorem nativePrunedPrice_le_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) :
    nativePrunedPrice u y j q a≤ZetaRieszComplexNullFloor.nativeCost u y j-
      ZetaRieszTangentCubicCredit.nativeTangentCredit u y j q a := min_le_left _ _

theorem nativePrunedPrice_le_pruned (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) :
    nativePrunedPrice u y j q a≤nativePrunedCost u y j q a+nativePaidBudget y j :=
  min_le_right _ _

/-- A nonnegative exact additional credit on the SAME previous
cost-minus-credit quantity; it is not independently added to two baselines. -/
def nativePrunedGain (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  ZetaRieszComplexNullFloor.nativeCost u y j-
    ZetaRieszTangentCubicCredit.nativeTangentCredit u y j q a-nativePrunedPrice u y j q a

theorem nativePrunedGain_nonneg (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) :
    0≤nativePrunedGain u y j q a :=
  sub_nonneg.mpr (nativePrunedPrice_le_previous u y j q a)

theorem eventually_joined_floor_with_pruned_price {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -nativePrunedPrice u y j (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_pruned hu hU hy q a] with j hnew
  have hold := ZetaRieszTangentCubicCredit.native_floor_with_tangent_credit u y j (q j) (a j)
  unfold nativePrunedPrice
  rcases le_total (ZetaRieszComplexNullFloor.nativeCost u y j-
    ZetaRieszTangentCubicCredit.nativeTangentCredit u y j (q j) (a j))
      (nativePrunedCost u y j (q j) (a j)+nativePaidBudget y j) with h | h
  · rw [min_eq_left h]
    linarith only [hold]
  · rw [min_eq_right h]
    linarith only [hnew]

theorem eventually_joined_floor_with_pruned_gain {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -ZetaRieszComplexNullFloor.nativeCost u y j+
        ZetaRieszTangentCubicCredit.nativeTangentCredit u y j (q j) (a j)+
        nativePrunedGain u y j (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_with_pruned_price hu hU hy q a] with j hj
  unfold nativePrunedGain
  linarith only [hj]

/-- This numerical cofinal price is the remaining open premise. The
pruning estimate above is independent; the contradiction here is conditional. -/
theorem false_of_cofinal_pruned_price (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) (hsimple : analyticZetaZeroMultiplicity rho=1)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ)
    (hcost : ∃ᶠ j in atTop,
      nativePrunedPrice (3/2-rho.1.re) rho.1.im j (q j) (a j)≤399/5000) : False := by
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
      (ZetaRieszComplexProjection.tendsto_nativeError rho hrho hexposed hU)
  have hf := eventually_joined_floor_with_pruned_price hu hU hy q a
  exact (hcost.and_eventually hf).mono (fun j hj=>by
    obtain ⟨hc,hf⟩ := hj
    linarith only [hc,hf])

end RiemannGaussian.ZetaRieszPaidIncidenceFloor
