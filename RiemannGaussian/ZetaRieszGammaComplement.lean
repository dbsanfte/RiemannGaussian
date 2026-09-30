/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGammaCollapse
import RiemannGaussian.ZetaRieszAllCountBoundary
import RiemannGaussian.ZetaRieszMarkedSaturation

/-!
# The literal complement in the translated Riesz coordinates

On a saturated composite cofactor, the entire unshifted term is exactly
zero, including its complementary allocation. Both literal fractions then
use the same translated response and recombine before real parts are taken.
This does not replace the actual marked prime by the selected zero measure.
-/

namespace RiemannGaussian.ZetaRieszGammaComplement
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszGammaCollapse ZetaRieszSelectedCofactor

/-- The continuous three-slot mass is the literal marked allocation,
not a limiting share indicator. All other prime orders have been summed. -/
theorem markedWeight_eq_continuous {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (hpr : p ≠ n.minFac)
    (hlog : Real.log p < Real.log n) (N : ℕ) :
    ZetaRieszJointOwnerTransfer.markedWeight N n p =
      continuousRectangleMass N (Real.log p) (Real.log n.minFac)
        (Real.log n-Real.log p-Real.log n.minFac) := by
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hr : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  have hx : Real.log p/Real.log n ≠ 1 :=
    ne_of_lt ((div_lt_one hl).mpr hlog)
  have he := ZetaRieszParityOrderTail.rectangleMass_eq_allocations n.primeFactors
    hp hr hpr.symm (fun q => Real.log q/Real.log n)
    (ZetaRieszJointBoundary.shares_sum hn hn1) hx N
  have hc : (Real.log n.minFac/Real.log n)/(1-Real.log p/Real.log n) =
      Real.log n.minFac/(Real.log n-Real.log p) := by field_simp
  rw [hc] at he
  unfold ZetaRieszJointOwnerTransfer.markedWeight ZetaRieszJointOwnerTransfer.markedAllocations
  rw [← he]
  unfold continuousRectangleMass
  rw [show Real.log n.minFac+(Real.log n-Real.log p-Real.log n.minFac) =
    Real.log n-Real.log p by ring,
    show Real.log p+(Real.log n-Real.log p) = Real.log n by ring]
  congr 1
  field_simp

/-- Exact physical coordinates for the CURRENT selection, throughout
its literal full band rather than only the older least-share box. -/
theorem selection_eq_continuous {u : ℝ} {N K n : ℕ}
    (hn : n ∈ ZetaRieszLeastBoundary.fullBand u N K) :
    ZetaRieszLeastBoundary.selection u N K n =
      continuousRectangleMass N (Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
        (Real.log n.minFac)
        (Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-Real.log n.minFac) := by
  obtain ⟨_,hs,hn1,hc,hp,_⟩ := Finset.mem_filter.mp hn
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpr : ZetaRieszPrimeEndpoint.largestPrime n ≠ n.minFac := by
    intro he
    have hsub : n.primeFactors ⊆ {ZetaRieszPrimeEndpoint.largestPrime n} := by
      intro q hq
      have hlo := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le
        (Nat.dvd_of_mem_primeFactors hq)
      have hhi : q ≤ ZetaRieszPrimeEndpoint.largestPrime n := by
        rw [ZetaRieszPrimeEndpoint.largestPrime,dif_pos ⟨q,hq⟩]
        exact Finset.le_max' _ _ hq
      rw [← he] at hlo
      exact Finset.mem_singleton.mpr (le_antisymm hhi hlo)
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  have hlt : ZetaRieszPrimeEndpoint.largestPrime n < n := by
    apply lt_of_le_of_ne (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))
    intro he
    rw [he] at hprime
    rw [hprime.primeFactors,Finset.card_singleton] at hc
    omega
  rw [ZetaRieszLeastBoundary.selection,if_pos hn,
    ← ZetaRieszJointOwnerTransfer.markedWeight_largest]
  exact markedWeight_eq_continuous hs hn1 hp hpr
    (Real.log_lt_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hlt)) N

/-- No allocation error remains when the literal complement is placed
at the SAME marked and least-prime coordinates. -/
theorem selection_complement_eq {u : ℝ} {N K n : ℕ}
    (hn : n ∈ ZetaRieszLeastBoundary.fullBand u N K) :
    1-ZetaRieszLeastBoundary.selection u N K n =
      continuousRectangleComplement N (Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
        (Real.log n.minFac)
        (Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-Real.log n.minFac) := by
  have hn1 := (Finset.mem_filter.mp hn).2.2.1
  have hT : Real.log (ZetaRieszPrimeEndpoint.largestPrime n)+
      (Real.log n.minFac+(Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-
        Real.log n.minFac)) ≠ 0 := by
    convert (Real.log_pos (by exact_mod_cast hn1 : (1 : ℝ) < n)).ne' using 1
    ring
  have h := rectangle_add_complement N (Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
    (Real.log n.minFac)
    (Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-Real.log n.minFac) hT
  rw [selection_eq_continuous hn]
  linarith

/-- The reflection condition is exactly saturation of the unmarked
cofactor, with no limiting share approximation. -/
theorem cofactor_saturated_of_reflected {p a : ℕ} (hp : 0 < p) (ha : 0 < a)
    {L : ℝ} (h : Real.log (p*a : ℕ)-L ≤ Real.log p) : Real.log a ≤ L := by
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast ha.ne')] at h
  linarith

/-- On the actual core radial window, a marked share at least one third
already saturates its composite cofactor. This includes the rectangle. -/
theorem cofactor_saturated_on_core {n p N : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hd : p ∣ n) {L : ℝ} (hL : (11/8 : ℝ)*N ≤ L)
    (hwindow : Real.log n ≤ (203/100 : ℝ)*N)
    (hshare : Real.log n/3 ≤ Real.log p) : Real.log (n/p : ℕ) ≤ L := by
  rw [Nat.cast_div hd (by exact_mod_cast hp.ne_zero),
    Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hp.ne_zero)]
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The missing marked order zero is geometrically paid on matched
shares at least one third, with all literal signed coefficients and
arbitrary finite support kept. This does NOT delete small middle orders
or estimate the corresponding virtual-prime boundary. -/
theorem zeroOrder_literal_bound (A D : Finset ℕ) (p : ℕ → ℕ)
    (N : ℕ) (y : ℝ) {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hshare : ∀ n ∈ D, (1/3 : ℝ) ≤ Real.log (p n)/Real.log n ∧
      Real.log (p n)/Real.log n ≤ 1) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D,
      (mass (N+1) 0 (Real.log (p n)/Real.log n) : ℂ)*
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
      (9/10 : ℝ)^N*zetaMoebiusLogMajorantMass (9/8) := by
  have hr : u*(2/3 : ℝ)*(8/3) ≤ 9/10 := by
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith
  have hb : u*(2/3 : ℝ) ≤ 1 := by linarith
  have hscalar : u^(N+1)*(2/3 : ℝ)^(N+1)*(8/3 : ℝ)^N ≤ (9/10 : ℝ)^N := by
    calc
      _ = (u*(2/3))*((u*(2/3))*(8/3))^N := by rw [mul_pow,mul_pow,pow_succ,pow_succ]; ring
      _ ≤ 1*(9/10 : ℝ)^N := mul_le_mul hb (pow_le_pow_left₀ (by positivity) hr N)
        (by positivity) (by norm_num)
      _ = _ := one_mul _
  have ha (n : ℕ) (hn : n ∈ D) :
      ‖(u : ℂ)^(N+1)*((mass (N+1) 0 (Real.log (p n)/Real.log n) : ℂ)*
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
      (9/10 : ℝ)^N*(zetaMoebiusLogMajorant n*zetaPrimeExpWeight (9/8) n) := by
    have hz0 : 0 ≤ mass (N+1) 0 (Real.log (p n)/Real.log n) := by
      simp only [mass,pow_zero,one_mul,Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,mul_one]
      exact pow_nonneg (by linarith [(hshare n hn).2]) _
    have hz : mass (N+1) 0 (Real.log (p n)/Real.log n) ≤ (2/3 : ℝ)^(N+1) := by
      simp only [mass,pow_zero,one_mul,Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,mul_one]
      exact pow_le_pow_left₀ (by linarith [(hshare n hn).2])
        (by linarith [(hshare n hn).1]) _
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (8/3 : ℝ)^N*zetaPrimeExpWeight (9/8) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 3/8) using 1
      norm_num
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu,
      norm_mul,Complex.norm_real,Real.norm_of_nonneg hz0,norm_mul]
    calc
      _ ≤ u^(N+1)*((2/3 : ℝ)^(N+1)*(zetaMoebiusLogMajorant n*
          ((8/3 : ℝ)^N*zetaPrimeExpWeight (9/8) n))) := by
        gcongr
        · exact zetaMoebiusLogMajorant_nonneg n
        · exact norm_residualCoefficient_le A hL N n
      _ = (u^(N+1)*(2/3 : ℝ)^(N+1)*(8/3 : ℝ)^N)*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (9/8) n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscalar
        (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, (9/10 : ℝ)^N*(zetaMoebiusLogMajorant n*zetaPrimeExpWeight (9/8) n) :=
      Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (by positivity)

/-- In particular the exact zero-order literal boundary is source-o(1)
for arbitrary moving masks and heights satisfying the matched geometry. -/
theorem tendsto_zeroOrder_literal (A D : ℕ → Finset ℕ) (p : ℕ → ℕ → ℕ)
    (y L : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : ∀ N, 0 < L N)
    (hshare : ∀ N n, n ∈ D N → (1/3 : ℝ) ≤ Real.log (p N n)/Real.log n ∧
      Real.log (p N n)/Real.log n ≤ 1) :
    Tendsto (fun N => (u : ℂ)^(N+1)*∑ n ∈ D N,
      (mass (N+1) 0 (Real.log (p N n)/Real.log n) : ℂ)*
        (residualCoefficient (A N) (L N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y N) n)) atTop (𝓝 0) := by
  have hb := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9/10)
    (by norm_num : (9/10 : ℝ) < 1)).mul_const (zetaMoebiusLogMajorantMass (9/8))
  rw [zero_mul] at hb
  exact squeeze_zero_norm (fun N => zeroOrder_literal_bound (A N) (D N) (p N) N
    (y N) (hL N) hu hU (hshare N)) hb

/-- Saturation removes the UNshifted cofactor response exactly, even
with an arbitrary signed complex complementary weight. -/
theorem unshifted_complement_eq_zero {a : ℕ} (ha : Squarefree a)
    (ha1 : a ≠ 1) (hanp : ¬a.Prime) {L : ℝ} (hL : Real.log a ≤ L) (W : ℂ) :
    W*(VaughanLogAverage.riesz L a : ℂ) = 0 := by
  rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hanp hL]
  simp

/-- The original signed arithmetic atom, not a completed surrogate,
has only the translated hinge on a saturated composite cofactor. -/
theorem original_atom_translated {p a : ℕ} (hp : p.Prime)
    (hsf : Squarefree (p*a)) (ha1 : a ≠ 1) (hanp : ¬a.Prime)
    {L : ℝ} (hL : 0 < L) (hsat : Real.log a ≤ L) (y : ℝ) (N : ℕ) :
    SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a) =
    ((N+1 : ℕ) : ℂ)/(L : ℂ)*(VaughanLogAverage.riesz (L-Real.log p) a : ℂ)*
      ((Real.log (p*a : ℕ)^(N+1)/((N+1).factorial : ℝ) : ℝ) : ℂ)*
        zetaPrimeFeature (3/2+Complex.I*y) (p*a) := by
  have hpa := Nat.squarefree_mul_iff.mp hsf
  have hpn : ¬p ∣ a := hp.coprime_iff_not_dvd.mp hpa.1
  rw [originalAtom_eq_phase hL y N hsf (Nat.not_prime_mul hp.ne_one ha1),
    ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpn,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hpa.2.2 ha1 hanp hsat]
  push_cast
  ring

/-- The exact complementary fraction of the CURRENT literal rest,
with all its support selection and old allocation unchanged. -/
theorem literal_complement_atom_translated {p a : ℕ} (hp : p.Prime)
    (hsf : Squarefree (p*a)) (ha1 : a ≠ 1) (hanp : ¬a.Prime)
    (u y : ℝ) (N K : ℕ)
    (hsat : Real.log a ≤ SquarefreeVaughanLogSource.length u N) :
    ((1-ZetaRieszLeastBoundary.selection u N K (p*a) : ℝ) : ℂ)*
      (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)) =
    ((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
      ((1-ZetaRieszLeastBoundary.selection u N K (p*a) : ℝ) : ℂ)*
      ((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N (p*a) : ℝ) : ℂ)*
      (VaughanLogAverage.riesz
        (SquarefreeVaughanLogSource.length u N-Real.log p) a : ℂ)*
      ((Real.log (p*a : ℕ)^(N+1)/((N+1).factorial : ℝ) : ℝ) : ℂ)*
        zetaPrimeFeature (3/2+Complex.I*y) (p*a) := by
  rw [residualCoefficient,mul_assoc,
    original_atom_translated hp hsf ha1 hanp
      (SquarefreeVaughanLogSource.length_pos u N) hsat y N]
  ring

/-- Literal selected and complementary fractions recombine in the SAME
translated physical atom. The real prime phase and old allocation survive.
This is not a virtual-prime transfer theorem. -/
theorem literal_joint_atom_translated {p a : ℕ} (hp : p.Prime)
    (hsf : Squarefree (p*a)) (ha1 : a ≠ 1) (hanp : ¬a.Prime)
    (u y : ℝ) (N K : ℕ)
    (hsat : Real.log a ≤ SquarefreeVaughanLogSource.length u N) :
    (ZetaRieszLeastBoundary.selection u N K (p*a) : ℂ)*
      (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a))+
    ((1-ZetaRieszLeastBoundary.selection u N K (p*a) : ℝ) : ℂ)*
      (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)) =
    ((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
      ((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N (p*a) : ℝ) : ℂ)*
      (VaughanLogAverage.riesz
        (SquarefreeVaughanLogSource.length u N-Real.log p) a : ℂ)*
      ((Real.log (p*a : ℕ)^(N+1)/((N+1).factorial : ℝ) : ℝ) : ℂ)*
        zetaPrimeFeature (3/2+Complex.I*y) (p*a) := by
  rw [← add_mul,← Complex.ofReal_add]
  simp only [add_sub_cancel,Complex.ofReal_one,one_mul]
  rw [residualCoefficient,mul_assoc,
    original_atom_translated hp hsf ha1 hanp
      (SquarefreeVaughanLogSource.length_pos u N) hsat y N]
  ring

/-- The actual signed rest in the same translated physical coordinates.
The first sum has the exact complementary factorial mass. The second
sum is the precise unchanged boundary: labels outside the original full
band or with an unsaturated canonical cofactor. No error estimate is
asserted for that boundary and no marked-prime measure is replaced. -/
theorem rest_physical_ledger (u y : ℝ) (N K : ℕ) :
    let L := SquarefreeVaughanLogSource.length u N
    let D := (ZetaRieszLeastBoundary.fullBand u N K).filter (fun n =>
      Real.log (n/ZetaRieszPrimeEndpoint.largestPrime n : ℕ) ≤ L)
    ZetaRieszLeastBoundary.rest u y N K =
      ((N+1 : ℕ) : ℂ)/(L : ℂ)*∑ n ∈ D,
        (continuousRectangleComplement N (Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
          (Real.log n.minFac)
          (Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-Real.log n.minFac) : ℂ)*
        ((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n : ℝ) : ℂ)*
        (VaughanLogAverage.riesz (L-Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
          (n/ZetaRieszPrimeEndpoint.largestPrime n) : ℂ)*
        zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n+
      ∑ n ∈ ZetaRieszParityPacket.coreBand u N K \ D,
        ((1-ZetaRieszLeastBoundary.selection u N K n : ℝ) : ℂ)*
          (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N) L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
  dsimp only
  let D := (ZetaRieszLeastBoundary.fullBand u N K).filter (fun n =>
    Real.log (n/ZetaRieszPrimeEndpoint.largestPrime n : ℕ) ≤
      SquarefreeVaughanLogSource.length u N)
  have hD : D ⊆ ZetaRieszParityPacket.coreBand u N K :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  unfold ZetaRieszLeastBoundary.rest
  rw [← Finset.sum_sdiff hD,add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hfull,hsat⟩ := Finset.mem_filter.mp hn
  obtain ⟨_,hs,_hn1,hc,hp,_⟩ := Finset.mem_filter.mp hfull
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hm := Nat.mul_div_cancel' hd
  obtain ⟨_ha,ha1,hanp,_hpa⟩ := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have he := literal_complement_atom_translated hprime (by rwa [hm]) ha1 hanp
    u y N K hsat
  rw [hm,selection_complement_eq hfull] at he
  rw [selection_complement_eq hfull,he]
  unfold zetaPrimeLogKernel
  push_cast
  ring

/-- Exact go/no-go ledger for joining the virtual selected response to
the actual rest. The full physical mass appears with TWO explicit signed
remainders: the old unmatched masks, and the selected response minus the
matched literal rectangle. Neither remainder is asserted small. -/
theorem joint_matched_ledger (u y : ℝ) (N K m : ℕ) (A : Finset ℕ) :
    let L := SquarefreeVaughanLogSource.length u N
    let D := (ZetaRieszLeastBoundary.fullBand u N K).filter (fun n =>
      Real.log (n/ZetaRieszPrimeEndpoint.largestPrime n : ℕ) ≤ L)
    let theta := fun n => continuousRectangleMass N
      (Real.log (ZetaRieszPrimeEndpoint.largestPrime n)) (Real.log n.minFac)
      (Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-Real.log n.minFac)
    let F := fun n => ((N+1 : ℕ) : ℂ)/(L : ℂ)*
      ((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n : ℝ) : ℂ)*
      (VaughanLogAverage.riesz (L-Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
        (n/ZetaRieszPrimeEndpoint.largestPrime n) : ℂ)*
      zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n
    (m : ℂ)*selectedResponse A N u y L+ZetaRieszLeastBoundary.rest u y N K =
      (∑ n ∈ D, F n)+
      (∑ n ∈ ZetaRieszParityPacket.coreBand u N K \ D,
        ((1-ZetaRieszLeastBoundary.selection u N K n : ℝ) : ℂ)*
          (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N) L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n))+
      ((m : ℂ)*selectedResponse A N u y L-∑ n ∈ D, (theta n : ℂ)*F n) := by
  dsimp only
  rw [rest_physical_ledger]
  rw [Finset.mul_sum]
  let D := (ZetaRieszLeastBoundary.fullBand u N K).filter (fun n =>
    Real.log (n/ZetaRieszPrimeEndpoint.largestPrime n : ℕ) ≤
      SquarefreeVaughanLogSource.length u N)
  let theta := fun n => continuousRectangleMass N
    (Real.log (ZetaRieszPrimeEndpoint.largestPrime n)) (Real.log n.minFac)
    (Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-Real.log n.minFac)
  let F := fun n => ((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
    ((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n : ℝ) : ℂ)*
    (VaughanLogAverage.riesz
      (SquarefreeVaughanLogSource.length u N-Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
      (n/ZetaRieszPrimeEndpoint.largestPrime n) : ℂ)*
    zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n
  have he :
      (∑ n ∈ (ZetaRieszLeastBoundary.fullBand u N K).filter (fun n =>
          Real.log (n/ZetaRieszPrimeEndpoint.largestPrime n : ℕ) ≤
            SquarefreeVaughanLogSource.length u N),
        ((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
          ((continuousRectangleComplement N (Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
            (Real.log n.minFac)
            (Real.log n-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-Real.log n.minFac) : ℂ)*
            ((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n : ℝ) : ℂ)*
            (VaughanLogAverage.riesz
              (SquarefreeVaughanLogSource.length u N-Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
              (n/ZetaRieszPrimeEndpoint.largestPrime n) : ℂ)*
            zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n)) =
        (∑ n ∈ D, F n)-∑ n ∈ D, (theta n : ℂ)*F n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hfull := (Finset.mem_filter.mp hn).1
    have hc := selection_complement_eq hfull
    rw [selection_eq_continuous hfull] at hc
    rw [← hc]
    dsimp only [F,theta]
    push_cast
    ring
  dsimp only [F,theta,D] at he
  rw [he]
  ring

/-- Applying the all-count boundary inside the already proved selected
response removes every middle-subset/count index before any estimate.
The signed complement remains arbitrary and unchanged. -/
theorem selected_plus_complement_eq_all_count {u : ℝ} (hu : 0 < u)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N m : ℕ) (y L : ℝ) (C : ℂ) :
    (u : ℂ)^(N+1)*((m : ℂ)*selectedResponse A N u y L+C) =
    (u : ℂ)^(N+1)*C-
      (m : ℂ)*((N+1 : ℕ) : ℂ)/(L : ℂ)*(u : ℂ)^(N+1)*
        ∫ t : ℝ in Ioi 0, (Real.exp (-u*t) : ℂ)*
          ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
            ((t : ℂ)^(j-1)/(j.factorial : ℂ))*
              ∑ r ∈ A, zetaPrimeLogKernel h (3/2+Complex.I*y) r*
                signedTaylorMoment (N+1-j-h)
                  (fun z => ZetaRieszAllCountBoundary.eulerBoundary r
                    (ZetaRieszMarkedSeparation.tailPrimes A r) z (L-t))
                  (3/2+Complex.I*y) := by
  have hs : (1/2 : ℝ) < (3/2+Complex.I*(y : ℂ)).re := by norm_num
  have he := selectedResponse_eq_collapsed_integral hu A hA h16 N y L
  simp_rw [ZetaRieszAllCountBoundary.physicalCofactor_eq_eulerBoundary A hA h16 hs] at he
  calc
    _ = (m : ℂ)*((u : ℂ)^(N+1)*selectedResponse A N u y L)+(u : ℂ)^(N+1)*C := by ring
    _ = _ := by rw [he]; ring

end
end RiemannGaussian.ZetaRieszGammaComplement
