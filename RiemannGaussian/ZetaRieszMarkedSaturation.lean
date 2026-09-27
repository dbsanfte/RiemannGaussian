/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMatchedSlope

/-!
# Paying the unshifted Riesz cofactor at the literal marked rectangle

Deleting the marked prime gives two signed Riesz cutoffs. The unshifted
cutoff is zero on saturated composite cofactors. Its remaining factorial
mass has a geometric upper tail. The reflected cutoff is retained, with
its phase, least-prime slot and every original allocation.
-/

namespace RiemannGaussian.ZetaRieszMarkedSaturation
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Complex Filter Topology
open ZetaRieszJointAllocation ZetaRieszJointOwnerTransfer ZetaRieszParityOrderTail
open ZetaRieszMarkedCompletion ZetaRieszOrderedEulerBound ZetaRieszFixedCofactor
open ZetaRieszWideOwnerAudit

/-- A tilt on the actual marked coordinate retains the whole correlated
rectangle. Only this positive error estimate enlarges its allocation set. -/
theorem markedWeight_tilt {n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactors) (N : ℕ) :
    markedWeight N n p ≤ Real.exp (-(21/40 : ℝ)*N*Real.log (5/4))*
      ((5/4 : ℝ)*(Real.log p/Real.log n)+
        Real.log (n/p : ℕ)/Real.log n)^(N+1) := by
  let x : ℕ → ℝ := fun q => Real.log q/Real.log n
  let B := Real.exp (-(21/40 : ℝ)*N*Real.log (5/4))
  have hx (q : ℕ) (_hq : q ∈ n.primeFactors) : 0 ≤ x q := by
    dsimp [x]
    positivity
  have hw := allocationWeight_nonneg n.primeFactors x hx
  have ht (d : ℕ → ℕ) (hd : d ∈ markedAllocations N n p) :
      1 ≤ B*(5/4 : ℝ)^(d p) := by
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).2).2.2.1
    have hhR : 21*(N : ℝ) ≤ 40*(d p : ℝ) := by exact_mod_cast hh
    have he : (5/4 : ℝ)^(d p) = Real.exp ((d p : ℝ)*Real.log (5/4)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
    rw [he,show B = Real.exp (-(21/40 : ℝ)*N*Real.log (5/4)) from rfl,
      ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_nonneg (show 0 ≤ (d p : ℝ)-(21/40 : ℝ)*N by linarith)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5/4))]
  have hs : (∑ q ∈ n.primeFactors.erase p, x q) = Real.log (n/p : ℕ)/Real.log n := by
    rw [← Finset.sum_div,sum_log_erase_eq_log_cofactor hn hp]
  calc
    _ ≤ ∑ d ∈ markedAllocations N n p, B*((5/4 : ℝ)^(d p)*allocationWeight n.primeFactors x d) := by
      apply Finset.sum_le_sum
      intro d hd
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right (ht d hd) (hw d)
    _ ≤ ∑ d ∈ Finset.piAntidiag n.primeFactors (N+1),
        B*((5/4 : ℝ)^(d p)*allocationWeight n.primeFactors x d) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) (hw d)))
    _ = _ := by rw [← Finset.mul_sum,allocation_tilt _ x hp,hs]

/-- The product log is split at the actual marked prime, not at an
independent continuum variable. -/
theorem log_split {n p : ℕ} (hn : Squarefree n) (hp : p ∈ n.primeFactors) :
    Real.log n = Real.log p+Real.log (n/p : ℕ) := by
  have hs := Finset.sum_erase_add n.primeFactors (fun q : ℕ => Real.log q) hp
  rw [sum_log_erase_eq_log_cofactor hn hp,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at hs
  linarith

/-- The exact rectangle and cofactor threshold beat the source rate.
The numerical search only selected this rational tilt; this is its proof. -/
theorem saturation_tilt (N : ℕ) {L : ℝ} (hL : (11/8 : ℝ)*N ≤ L) :
    Real.exp (-(21/40 : ℝ)*N*Real.log (5/4))*
      ((4/5 : ℝ)*safeRadius)⁻¹^(N+1)*Real.exp (-(safeRadius/5)*L) ≤
        (5/4 : ℝ)*safeRadius⁻¹^(N+1)*Real.exp (-(N : ℝ)/100) := by
  have hR := safeRadius_pos
  have hp : ((4/5 : ℝ)*safeRadius)⁻¹^(N+1) =
      (5/4 : ℝ)^(N+1)*safeRadius⁻¹^(N+1) := by
    rw [mul_inv_rev,mul_pow]
    norm_num
    ring
  have hpow : (5/4 : ℝ)^(N+1) = (5/4 : ℝ)*Real.exp ((N : ℝ)*Real.log (5/4)) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num),pow_succ]
    ring
  rw [hp,hpow]
  have hlog : Real.log (5/4 : ℝ) ≤ 1/4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5/4)
    linarith
  have he : -(21/40 : ℝ)*N*Real.log (5/4)+(N : ℝ)*Real.log (5/4)-
      (safeRadius/5)*L ≤ -(N : ℝ)/100 := by
    have ht := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ safeRadius/5)
    have hl := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (19/40 : ℝ)*N by positivity)
    norm_num [safeRadius] at ht ⊢
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ = ((5/4 : ℝ)*safeRadius⁻¹^(N+1))*
        Real.exp (-(21/40 : ℝ)*N*Real.log (5/4)+(N : ℝ)*Real.log (5/4)-
          (safeRadius/5)*L) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_add]
      simp only [neg_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

/-- The exact marked factorial mass on a cofactor beyond the Riesz
cutoff is exponentially small, uniformly in the phase height. -/
theorem marked_kernel_cofactor_tail {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (N : ℕ) (y : ℝ) {L : ℝ}
    (hL : (11/8 : ℝ)*N ≤ L) (ha : L ≤ Real.log (n/p : ℕ)) :
    markedWeight N n p*‖zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n‖ ≤
      ((5/4 : ℝ)*safeRadius⁻¹^(N+1)*Real.exp (-(N : ℝ)/100))*
        zetaPrimeExpWeight (3/2-safeRadius) n := by
  let B := Real.exp (-(21/40 : ℝ)*N*Real.log (5/4))
  let t := (5/4 : ℝ)*Real.log p+Real.log (n/p : ℕ)
  let v := (4/5 : ℝ)*safeRadius
  have hR := safeRadius_pos
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hn1)).ne'
  have hm : markedWeight N n p ≤ B*(t/Real.log n)^(N+1) := by
    simpa only [B,t,add_div,mul_div_assoc] using markedWeight_tilt hn hp N
  have he := logMoment_exp_envelope (N+1) ht hv 0
  simp only [zero_mul,neg_zero,Real.exp_zero,mul_one,zero_sub,neg_neg] at he
  have hw : Real.exp (v*t)*zetaPrimeExpWeight (3/2) n =
      Real.exp (-(safeRadius/5)*Real.log (n/p : ℕ))*
        zetaPrimeExpWeight (3/2-safeRadius) n := by
    unfold zetaPrimeExpWeight
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    rw [log_split hn hp]
    dsimp [v,t]
    ring
  rw [norm_zetaPrimeLogKernel]
  rw [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num]
  calc
    _ ≤ (B*(t/Real.log n)^(N+1))*(Real.log n^(N+1)/((N+1).factorial : ℝ)*
        zetaPrimeExpWeight (3/2) n) := mul_le_mul_of_nonneg_right hm
          (mul_nonneg (by positivity) (Real.exp_pos _).le)
    _ = B*(t^(N+1)/((N+1).factorial : ℝ))*zetaPrimeExpWeight (3/2) n := by
      rw [div_pow]
      field_simp
    _ ≤ B*(v⁻¹^(N+1)*Real.exp (v*t))*zetaPrimeExpWeight (3/2) n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = (B*v⁻¹^(N+1))*Real.exp (-(safeRadius/5)*Real.log (n/p : ℕ))*
        zetaPrimeExpWeight (3/2-safeRadius) n := by
      calc
        _ = (B*v⁻¹^(N+1))*(Real.exp (v*t)*zetaPrimeExpWeight (3/2) n) := by ring
        _ = _ := by rw [hw]; ring
    _ ≤ (B*v⁻¹^(N+1))*Real.exp (-(safeRadius/5)*L)*
        zetaPrimeExpWeight (3/2-safeRadius) n := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (by dsimp [B]; positivity)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ha (by linarith : -(safeRadius/5) ≤ 0))
    _ ≤ _ := mul_le_mul_of_nonneg_right (saturation_tilt N hL) (Real.exp_pos _).le

/-- Deleting one prime leaves a genuine squarefree composite on every
label of the original at-least-three-prime packet. -/
theorem cofactor_data {n p : ℕ} (hn : Squarefree n) (hc : 3 ≤ n.primeFactors.card)
    (hp : p ∈ n.primeFactors) :
    Squarefree (n/p) ∧ n/p ≠ 1 ∧ ¬(n/p).Prime ∧ ¬p ∣ n/p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hm : p*(n/p) = n := Nat.mul_div_cancel' hd
  have ha : Squarefree (n/p) := hn.squarefree_of_dvd (Nat.div_dvd_of_dvd hd)
  have hcop : p.Coprime (n/p) := Nat.coprime_of_squarefree_mul (by rwa [hm])
  have hpf : n.primeFactors = {p} ∪ (n/p).primeFactors := by
    calc
      _ = (p*(n/p)).primeFactors := congrArg Nat.primeFactors hm.symm
      _ = _ := by rw [Nat.primeFactors_mul hprime.ne_zero ha.ne_zero,hprime.primeFactors]
  have hnot : ¬p ∣ n/p := hprime.coprime_iff_not_dvd.mp hcop
  refine ⟨ha,?_,?_,hnot⟩
  · intro he
    rw [hpf,he,Nat.primeFactors_one,Finset.union_empty,Finset.card_singleton] at hc
    omega
  · intro hap
    rw [hpf,hap.primeFactors] at hc
    have hh : ({p} ∪ {n/p} : Finset ℕ).card ≤ 2 := by
      exact (Finset.card_union_le _ _).trans (by simp)
    omega

/-- The unshifted cofactor response vanishes exactly below its full
saturation threshold; no sign or phase assumption enters. -/
theorem riesz_cofactor_eq_zero {n p : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (hp : p ∈ n.primeFactors)
    {L : ℝ} (hL : Real.log (n/p : ℕ) ≤ L) :
    VaughanLogAverage.riesz L (n/p) = 0 := by
  obtain ⟨ha,ha1,hap,_⟩ := cofactor_data hn hc hp
  rw [ZetaRieszTypeII.riesz_eq_vonMangoldt_of_saturated ha.ne_zero ha1 hL]
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    (fun h => hap (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨ha,h⟩))

/-- The fixed-cofactor logarithmic cost embeds in the existing complete
divisor majorant of the original observed integer. -/
theorem divisorLogMass_le_original {n a : ℕ} (hn : n ≠ 0) (hd : a ∣ n) :
    divisorLogMass a ≤ zetaMoebiusLogMajorant n := by
  rw [divisorLogMass,zetaMoebiusLogMajorant,Nat.sum_divisorsAntidiagonal' (fun _ d => Real.log d)]
  apply (Finset.sum_le_sum (fun d _ => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hn hd)
      (fun d _ _ => Real.log_natCast_nonneg d))
  have hh : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (Real.log_natCast_nonneg d)

/-- The unshifted cofactor part of the literal marked atom. Its original
factorial rectangle and full phase remain inside the prime-incidence sum. -/
def unshiftedAtom (L y : ℝ) (N n : ℕ) : ℂ :=
  if ZetaRieszPhysicalCompletion.validLabel n then
    -((N+1 : ℕ) : ℂ)/(L : ℂ)*
      ∑ p ∈ n.primeFactors, (VaughanLogAverage.riesz L (n/p) : ℂ)*
        (markedWeight N n p : ℂ)*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n
  else 0

/-- The retained reflected cofactor has the actual moving cutoff
L-log(p). This term is not estimated by the saturation theorem. -/
def reflectedAtom (L y : ℝ) (N n : ℕ) : ℂ :=
  if ZetaRieszPhysicalCompletion.validLabel n then
    ((N+1 : ℕ) : ℂ)/(L : ℂ)*
      ∑ p ∈ n.primeFactors, (VaughanLogAverage.riesz (L-Real.log p) (n/p) : ℂ)*
        (markedWeight N n p : ℂ)*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n
  else 0

/-- Exact deletion of the marked prime, before either branch is bounded.
All original factorial allocations and the complex phase are retained. -/
theorem atom_split (u y : ℝ) (N n : ℕ) :
    ZetaRieszPhysicalCompletion.atom u y N n =
      unshiftedAtom (SquarefreeVaughanLogSource.length u N) y N n+
        reflectedAtom (SquarefreeVaughanLogSource.length u N) y N n := by
  by_cases hn : ZetaRieszPhysicalCompletion.validLabel n
  · have hnp : ¬n.Prime := by
      intro hp
      have hc := hn.2
      rw [hp.primeFactors,Finset.card_singleton] at hc
      omega
    have he (p : ℕ) (hp : p ∈ n.primeFactors) :
        VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n =
          VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) (n/p)-
            VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N-Real.log p) (n/p) := by
      have h := ZetaSquarefreeRieszWindows.riesz_prime_mul
        (SquarefreeVaughanLogSource.length u N) (Nat.prime_of_mem_primeFactors hp)
        (cofactor_data hn.1 hn.2 hp).2.2.2
      simpa only [Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)] using h
    rw [ZetaRieszPhysicalCompletion.atom,ZetaRieszPhysicalCompletion.markedCoefficient,
      if_pos hn,unshiftedAtom,reflectedAtom,if_pos hn,if_pos hn,
      SquarefreeVaughanLogSource.coefficient,if_pos ⟨hn.1,hnp⟩,markedMass]
    simp only [Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,
      Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hk := ZetaRieszHeadOrders.log_mul_kernel N n (3/2+Complex.I*y)
    rw [he p hp,Complex.ofReal_sub]
    calc
      _ = (-(markedWeight N n p : ℂ)*
          ((VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) (n/p) : ℂ)-
            (VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N-Real.log p) (n/p) : ℂ))/
              (SquarefreeVaughanLogSource.length u N : ℂ))*
                ((Real.log n : ℂ)*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by ring
      _ = _ := by rw [hk]; ring
  · simp [ZetaRieszPhysicalCompletion.atom,ZetaRieszPhysicalCompletion.markedCoefficient,
      unshiftedAtom,reflectedAtom,hn]

/-- Each prime incidence is either exactly saturated or has the proved
large-cofactor factorial saving. No prime-count truncation is used. -/
theorem unshifted_incidence_bound {n p : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (hp : p ∈ n.primeFactors)
    (N : ℕ) (y : ℝ) {L : ℝ} (hL : (11/8 : ℝ)*N ≤ L) :
    ‖(VaughanLogAverage.riesz L (n/p) : ℂ)*(markedWeight N n p : ℂ)*
      zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n‖ ≤
      ((5/4 : ℝ)*safeRadius⁻¹^(N+1)*Real.exp (-(N : ℝ)/100))*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (3/2-safeRadius) n) := by
  by_cases ha : Real.log (n/p : ℕ) ≤ L
  · rw [riesz_cofactor_eq_zero hn hc hp ha,Complex.ofReal_zero,zero_mul,zero_mul,norm_zero]
    have := safeRadius_pos
    exact mul_nonneg (by positivity) (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
  · have hn1 := ZetaRieszPhysicalCompletion.validLabel_one_lt ⟨hn,hc⟩
    have hr := (abs_riesz_le_divisorLogMass L (cofactor_data hn hc hp).2.1).trans
      (divisorLogMass_le_original hn.ne_zero (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)))
    have ht := marked_kernel_cofactor_tail hn hn1 hp N y hL (le_of_not_ge ha)
    rw [mul_assoc,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_of_nonneg (markedWeight_nonneg N n p)]
    exact (mul_le_mul hr ht (mul_nonneg (markedWeight_nonneg N n p) (norm_nonneg _))
      (zetaMoebiusLogMajorant_nonneg n)).trans_eq (by ring)

/-- Paying the factor count costs only a smaller Euler-half-plane
abscissa. Its constant is explicit and independent of the prime set. -/
theorem count_weight_bound {n : ℕ} (hn : Squarefree n) :
    (n.primeFactors.card : ℝ)*zetaPrimeExpWeight (3/2-safeRadius) n ≤
      1048576*zetaPrimeExpWeight (1+1/524288) n := by
  have hk := norm_zetaPrimeLogKernel_le 1 ((3/2-safeRadius : ℝ) : ℂ) n
    (by norm_num : (0 : ℝ) < 1/524288)
  rw [norm_zetaPrimeLogKernel] at hk
  norm_num [safeRadius] at hk ⊢
  have hc := mul_le_mul_of_nonneg_right (card_le_two_log hn) (Real.exp_pos
    (-(262145/262144 : ℝ)*Real.log n)).le
  change (n.primeFactors.card : ℝ)*zetaPrimeExpWeight (262145/262144) n ≤
    2*Real.log n*zetaPrimeExpWeight (262145/262144) n at hc
  nlinarith

/-- Summing all marked prime incidences still leaves a genuinely
summable arithmetic majorant. The entire phase height is unrestricted. -/
theorem unshiftedAtom_bound (N n : ℕ) (y : ℝ) {L : ℝ}
    (hL : 1 ≤ L) (hLN : (11/8 : ℝ)*N ≤ L) :
    ‖unshiftedAtom L y N n‖ ≤
      (1310720*((N : ℝ)+1)*safeRadius⁻¹^(N+1)*Real.exp (-(N : ℝ)/100))*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/524288) n) := by
  have hR := safeRadius_pos
  have hpref : ‖-((N+1 : ℕ) : ℂ)/(L : ℂ)‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_neg,Complex.norm_natCast,Complex.norm_real,Real.norm_of_nonneg (by linarith)]
    push_cast
    exact div_le_self (by positivity) hL
  by_cases hn : ZetaRieszPhysicalCompletion.validLabel n
  · rw [unshiftedAtom,if_pos hn,norm_mul]
    have hB : 0 ≤ (5/4 : ℝ)*safeRadius⁻¹^(N+1)*Real.exp (-(N : ℝ)/100) := by positivity
    have hi : ‖∑ p ∈ n.primeFactors, (VaughanLogAverage.riesz L (n/p) : ℂ)*
        (markedWeight N n p : ℂ)*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n‖ ≤
        (n.primeFactors.card : ℝ)*(((5/4 : ℝ)*safeRadius⁻¹^(N+1)*Real.exp (-(N : ℝ)/100))*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (3/2-safeRadius) n)) := by
      apply (norm_sum_le _ _).trans
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum
        (fun p hp => unshifted_incidence_bound hn.1 hn.2 hp N y hLN)
    apply (mul_le_mul hpref hi (norm_nonneg _) (by positivity)).trans
    have hc := mul_le_mul_of_nonneg_left (count_weight_bound hn.1)
      (mul_nonneg (mul_nonneg (by positivity : 0 ≤ (N : ℝ)+1) hB)
        (zetaMoebiusLogMajorant_nonneg n))
    convert hc using 1 <;> ring
  · rw [unshiftedAtom,if_neg hn,norm_zero]
    exact mul_nonneg (by positivity)
      (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)

/-- The original unshifted branch on any finite label mask. -/
def unshiftedPacket (T : Finset ℕ) (L y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ T, unshiftedAtom L y N n

/-- The same finite labels and allocations, with only the reflected
Riesz cutoff retained. Its signed bound remains the arithmetic target. -/
def reflectedPacket (T : Finset ℕ) (L y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ T, reflectedAtom L y N n

theorem packet_split (T : Finset ℕ) (u y : ℝ) (N : ℕ) :
    (∑ n ∈ T, ZetaRieszPhysicalCompletion.atom u y N n) =
      unshiftedPacket T (SquarefreeVaughanLogSource.length u N) y N+
        reflectedPacket T (SquarefreeVaughanLogSource.length u N) y N := by
  simp_rw [atom_split]
  exact Finset.sum_add_distrib

/-- The summed unshifted branch has a height-independent geometric
bound on every finite arithmetic selection, without changing its mask. -/
theorem unshiftedPacket_bound (T : Finset ℕ) (N : ℕ) (y : ℝ) {L : ℝ}
    (hL : 1 ≤ L) (hLN : (11/8 : ℝ)*N ≤ L) :
    ‖unshiftedPacket T L y N‖ ≤
      (1310720*((N : ℝ)+1)*safeRadius⁻¹^(N+1)*Real.exp (-(N : ℝ)/100))*
        zetaMoebiusLogMajorantMass (1+1/524288) := by
  have hR := safeRadius_pos
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun n _ => unshiftedAtom_bound N n y hL hLN)).trans
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    ((summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 1+1/524288)).sum_le_tsum T
      (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le))
    (by positivity)

/-- Explicit source rate for paying the unshifted cutoff branch. -/
def saturationRate : ℝ := radiusCeiling/safeRadius*Real.exp (-(1 : ℝ)/100)

/-- The rational upper bound is proved, rather than inferred from
the exploratory floating-point value. -/
theorem saturationRate_bounds : 0 ≤ saturationRate ∧ saturationRate < 991/1000 := by
  have hR := safeRadius_pos
  refine ⟨by unfold saturationRate radiusCeiling; positivity,?_⟩
  have he : (101/100 : ℝ) ≤ Real.exp (1/100) := by
    linarith [Real.add_one_le_exp (1/100 : ℝ)]
  rw [saturationRate,show -(1 : ℝ)/100 = -(1/100 : ℝ) by ring,Real.exp_neg,
    ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 991/1000)
  norm_num [radiusCeiling,safeRadius] at ⊢
  linarith

/-- The finite unshifted arithmetic sum is paid at the same source
normalization as the original carrier. The constant is not a small-N bound. -/
theorem norm_scaled_unshiftedPacket_le (T : Finset ℕ) (N : ℕ) (y : ℝ)
    {L u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hL : 1 ≤ L) (hLN : (11/8 : ℝ)*N ≤ L) :
    ‖(u : ℂ)^(N+1)*unshiftedPacket T L y N‖ ≤
      (1310720*(radiusCeiling/safeRadius)*zetaMoebiusLogMajorantMass (1+1/524288))*
        ((N : ℝ)+1)*saturationRate^N := by
  have hR := safeRadius_pos
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  apply (mul_le_mul (pow_le_pow_left₀ hu hU (N+1)) (unshiftedPacket_bound T N y hL hLN)
    (norm_nonneg _) (by unfold radiusCeiling; positivity)).trans_eq
  have he : Real.exp (-(N : ℝ)/100) = Real.exp (-(1 : ℝ)/100)^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he,saturationRate,mul_pow,div_pow,pow_succ radiusCeiling,pow_succ safeRadius⁻¹]
  simp only [div_eq_mul_inv,← inv_pow]
  ring

/-- The entire unshifted branch tends to zero for arbitrary moving
finite masks and heights, with the literal physical length unchanged. -/
theorem tendsto_unshiftedPacket {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (T : ℕ → Finset ℕ) (height : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      unshiftedPacket (T N) (SquarefreeVaughanLogSource.length u N) (height N) N)
      atTop (nhds 0) := by
  have he := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (by norm_num : (0 : ℝ) ≤ 11/16) (lt_of_le_of_lt hU radius_lt_source)
  have hr := saturationRate_bounds
  have hpoly := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr.1
    (lt_trans hr.2 (by norm_num : (991/1000 : ℝ) < 1))
  simp only [pow_one] at hpoly
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr.1
    (lt_trans hr.2 (by norm_num : (991/1000 : ℝ) < 1))
  have hb := (hpoly.add hpow).const_mul
    (1310720*(radiusCeiling/safeRadius)*zetaMoebiusLogMajorantMass (1+1/524288))
  simp only [add_zero,mul_zero] at hb
  apply squeeze_zero_norm' ?_ hb
  filter_upwards [he,eventually_ge_atTop 1] with N hLN hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by nlinarith
  convert norm_scaled_unshiftedPacket_le (T N) N (height N) hu.le hU (by linarith) hL using 1
  ring

/-- The retained reflected sum on the actual physical subset universe. -/
def reflectedMain (u y : ℝ) (N : ℕ) : ℂ :=
  reflectedPacket (completeBand (ZetaRieszAnnulusJoint.intermediatePrimes u N))
    (SquarefreeVaughanLogSource.length u N) y N

/-- Exact ledger inside the existing finite subset completion. No new
integer, prime, incidence or factorial order is added by this split. -/
theorem completePacket_split (u y : ℝ) (N : ℕ) :
    completePacket u y N =
      unshiftedPacket (completeBand (ZetaRieszAnnulusJoint.intermediatePrimes u N))
        (SquarefreeVaughanLogSource.length u N) y N+reflectedMain u y N := by
  rw [← ZetaRieszPhysicalCompletion.sum_atom_completeBand,packet_split]
  rfl

/-- The fixed signed counts 3..55 minus short overflow 3..13 now have
only the reflected cofactor cutoff left in their source-equivalent
prime sum. This theorem does not bound that retained signed term. -/
theorem tendsto_reflected_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (reflectedMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have h := (tendsto_complete_sub_current hu hU y).sub
    ((tendsto_unshiftedPacket (by linarith : 0 < u) hU
      (fun N => completeBand (ZetaRieszAnnulusJoint.intermediatePrimes u N)) (fun _ => y)).comp
        ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [sub_self] at h
  convert h using 1
  ext j
  simp only [Function.comp_def,completePacket_split]
  ring

/-- The logarithmic derivative of the matched ordered Euler tail and
the retained literal reflected cofactor describe the same source-scale
target. Their comparison does not assert a bound for either main term. -/
theorem tendsto_matched_sub_reflected {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (ZetaRieszMatchedSlope.matchedMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        reflectedMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))) atTop (nhds 0) := by
  have h := (ZetaRieszMatchedSlope.tendsto_matched_sub_current hu hU y).sub
    (tendsto_reflected_sub_current hu hU y)
  simp only [sub_self] at h
  convert h using 1
  ext j
  ring

end
end RiemannGaussian.ZetaRieszMarkedSaturation
