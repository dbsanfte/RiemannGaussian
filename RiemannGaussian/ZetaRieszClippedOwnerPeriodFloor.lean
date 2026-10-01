/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTinyOwnerPeriodFloor
import RiemannGaussian.ZetaRieszFiveSignCoverFloor

/-!
# The literal start of an owner period, at every prime count

The part clipped by largest-prime ownership is contained in the actual
close-owner boundary. Only the cofactor primes are placed in the shell;
the owner itself is allowed to cross its upper endpoint. Count symmetry
and the two close-prime reciprocal masses are retained before pricing.
The whole numerical floor remains open.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszClippedOwnerPeriodFloor
open ZetaRieszPrimeEndpoint ZetaRieszAllowancePrimeBoxes
open ZetaRieszMacroPrimeWindows ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod
open ZetaRieszLogShellPeriodFloor ZetaRieszTinyOwnerPeriodFloor
open ZetaRieszStaggeredFloor ZetaRieszOwnerCurvatureFloor ZetaRieszJointOwnerFibreFloor
open ZetaRieszParityPacket ZetaRieszSignedConvolution ZetaRieszShortDivisorOrbits
open ZetaRieszUnsignedDivisorError ZetaRieszCrossingOrbitCancellation ZetaRieszJointAllocation
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszMultiPeriodSix
open scoped ArithmeticFunction.Moebius

/-- Canonical owner facts at an arbitrary count, with the actual squarefree
cofactor and cardinality retained. -/
theorem canonical_owner_data {n : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) :
    (largestPrime n).Prime ∧ largestPrime n*(n/largestPrime n)=n ∧
      Squarefree (n/largestPrime n) ∧
      n.primeFactors.card=(n/largestPrime n).primeFactors.card+1 ∧
      (∀ q ∈ n.primeFactors, q ≤ largestPrime n) ∧ ¬largestPrime n ∣ n/largestPrime n := by
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have ha := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have he := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hcard : n.primeFactors.card=(n/largestPrime n).primeFactors.card+1 := by
    conv_lhs => rw [← he,Nat.primeFactors_mul hpp.ne_zero ha.1.ne_zero,
      hpp.primeFactors,Finset.singleton_union,Finset.card_insert_of_notMem
        (show largestPrime n ∉ (n/largestPrime n).primeFactors from
          fun h => ha.2.2.2 (Nat.dvd_of_mem_primeFactors h))]
  have hmax (q : ℕ) (hq : q ∈ n.primeFactors) : q ≤ largestPrime n := by
    have hne : n.primeFactors.Nonempty := ⟨q,hq⟩
    rw [largestPrime,dif_pos hne]
    exact Finset.le_max' _ q hq
  exact ⟨hpp,he,ha.1,hcard,hmax,ha.2.2.2⟩

/-- The close-owner witness may always use the SAME canonical owner as
the literal carrier; no pair-incidence averaging is introduced. -/
theorem close_owner_canonical {n : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (htie : ZetaRieszOwnerTieFloor.CloseOwners n) :
    ∃ q ∈ (n/largestPrime n).primeFactors,
      log (largestPrime n)-1/8 < log q := by
  have hd := canonical_owner_data hs hc
  obtain ⟨p,hp,q,hq,hpq,hmax,hgap⟩ := htie
  have hp0 := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have he : p=largestPrime n := le_antisymm (hd.2.2.2.2.1 p hp) (hmax _ hp0)
  subst p
  have hf : n.primeFactors=insert (largestPrime n) (n/largestPrime n).primeFactors := by
    conv_lhs => rw [← hd.2.1,Nat.primeFactors_mul hd.1.ne_zero hd.2.2.1.ne_zero,
      hd.1.primeFactors,Finset.singleton_union]
  rw [hf] at hq
  exact ⟨q,(Finset.mem_insert.mp hq).resolve_left (Ne.symm hpq),hgap⟩

/-- Without the close-owner boundary, all cofactor factors remain owned
through the ENTIRE period, regardless of their count. -/
theorem no_close_owner_gap {n : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (htie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    ∀ q ∈ (n/largestPrime n).primeFactors, log q ≤ log (largestPrime n)-1/8 := by
  have hd := canonical_owner_data hs hc
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  intro q hq
  by_contra hh
  have hqn := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)))
    hs.ne_zero
  apply htie
  refine ⟨_,hp,q,hqn,?_,hd.2.2.2.2.1,lt_of_not_ge hh⟩
  intro he
  have hdq := Nat.dvd_of_mem_primeFactors hq
  rw [← he] at hdq
  exact hd.2.2.2.2.2 hdq

/-- Failure of ownership at the lower prime-period endpoint is exactly
an already identified close-owner geometry. Original phases are untouched. -/
theorem owner_start_clipped_close {n : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) {v y : ℝ} (hy : 54 ≤ y)
    (hT : v-Real.pi/y < log n ∧ log n ≤ v+Real.pi/y)
    (hclip : ∃ q ∈ (n/largestPrime n).primeFactors,
      v-Real.pi/y-log (n/largestPrime n : ℕ) < log q) :
    ZetaRieszOwnerTieFloor.CloseOwners n := by
  have hd := canonical_owner_data hs hc
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hlog : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hd.2.1,Nat.cast_mul,log_mul
      (by exact_mod_cast hd.1.ne_zero) (by exact_mod_cast hd.2.2.1.ne_zero)]
  have hy0 : 0 < y := by linarith
  have hπ : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  obtain ⟨q,hq,hclip⟩ := hclip
  have hqn := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)))
    hs.ne_zero
  refine ⟨_,hp,q,hqn,?_,hd.2.2.2.2.1,?_⟩
  · intro he
    have hdq := Nat.dvd_of_mem_primeFactors hq
    rw [← he] at hdq
    exact hd.2.2.2.2.2 hdq
  · linarith only [hclip,hT.2,hlog,hπ]

/-- Actual unclipped owner gaps satisfy the cap-free period hypothesis.
This is a support theorem, not a new arithmetic cancellation premise. -/
theorem no_close_owner_period_gap {n : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) {v y : ℝ} (hy : 54 ≤ y)
    (hT : v-Real.pi/y < log n ∧ log n ≤ v+Real.pi/y)
    (htie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    ∀ q ∈ (n/largestPrime n).primeFactors,
      log q ≤ v-Real.pi/y-log (n/largestPrime n : ℕ) := by
  intro q hq
  by_contra hh
  exact htie (owner_start_clipped_close hs hc hy hT ⟨q,hq,lt_of_not_ge hh⟩)

/-- The original finite prime mask stays intact on a period whenever
its literal logarithmic endpoints stay inside that mask. -/
theorem whole_fibre_mem_intermediate {u : ℝ} {N : ℕ} (hN : 1 ≤ N) {v y b : ℝ}
    (hlo : 2*log N ≤ v-Real.pi/y-b)
    (hhi : v+Real.pi/y-b < SquarefreeVaughanLogSource.length u N) :
    ∀ p ∈ logPrimes (v-Real.pi/y-b) (2*Real.pi/y),
      p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  intro p hp
  have hb := logPrimes_bounds hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hb.1.pos
  have hlogN : log ((N^2 : ℕ) : ℝ)=2*log N := by
    rw [Nat.cast_pow,log_pow]
    norm_num
  have hlow : N^2 < p := by
    exact_mod_cast (log_lt_log_iff (by positivity : (0 : ℝ) < (N : ℝ)^2) hp0).mp
      (by simpa only [← Nat.cast_pow,hlogN] using hlo.trans_lt hb.2.1)
  have hupper : log p < SquarefreeVaughanLogSource.length u N := by
    have hh := hb.2.2
    simp only [mul_div_assoc] at hh
    linarith only [hh,hhi]
  unfold SquarefreeVaughanLogSource.length at hupper
  have hupper' := (log_lt_log_iff hp0
    (by positivity : (0 : ℝ) < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2 : ℝ)^2)).mp hupper
  exact (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mpr
    ⟨hb.1,hlow,by exact_mod_cast hupper'⟩

/-- The close pair is covered with only the COFACTOR in the shell.
The owner may cross the shell endpoint and all original labels remain. -/
theorem close_owner_cofactor_shell_cover {k n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card=k+2) (hk : 0 < k) {v H : ℝ}
    (htie : ZetaRieszOwnerTieFloor.CloseOwners n)
    (hT : v-1/16 < log n ∧ log n ≤ v+1/16)
    (hshell : (n/largestPrime n).primeFactors ⊆ shellPrimes H) :
    ∃ b q : ℕ, n=largestPrime n*(q*b) ∧ Squarefree b ∧ b.primeFactors.card=k ∧
      b.primeFactors ⊆ shellPrimes H ∧ log b ≤ v-2*H+1/16 ∧
      largestPrime n ∈ ZetaRieszOwnerTieFloor.pairWindow v b ∧
      q ∈ ZetaRieszOwnerTieFloor.pairWindow v b := by
  have hc3 : 3 ≤ n.primeFactors.card := by omega
  have hd := canonical_owner_data hn hc3
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  obtain ⟨q,hq,hgap⟩ := close_owner_canonical hn hc3 htie
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqN := hqp.mem_primeFactors ((Nat.dvd_of_mem_primeFactors hq).trans
    (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp))) hn.ne_zero
  have hnot : largestPrime n ≠ q := by
    intro he
    have hdq := Nat.dvd_of_mem_primeFactors hq
    rw [← he] at hdq
    exact hd.2.2.2.2.2 hdq
  obtain ⟨b,he,hb,hbc⟩ := ZetaRieszOwnerTieFloor.two_prime_factorization hn hc hp hqN hnot
  have haeq : n/largestPrime n=q*b := by
    conv_lhs => lhs; rw [he]
    exact Nat.mul_div_cancel_left _ hd.1.pos
  have hbd : b ∣ n/largestPrime n := by rw [haeq]; exact dvd_mul_left b q
  have hbsub : b.primeFactors ⊆ shellPrimes H :=
    (Nat.primeFactors_mono hbd hd.2.2.1.ne_zero).trans hshell
  have hqle : log q ≤ log (largestPrime n) := log_le_log
    (by exact_mod_cast hqp.pos) (by exact_mod_cast hd.2.2.2.2.1 q hqN)
  have hqH := (shellPrimes_data (hshell hq)).2.1
  have hlog : log n=log (largestPrime n)+log q+log b := by
    conv_lhs => rw [he,Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hqp.ne_zero hb.ne_zero),Nat.cast_mul,
      log_mul (by exact_mod_cast hqp.ne_zero) (by exact_mod_cast hb.ne_zero)]
    ring
  refine ⟨b,q,he,hb,hbc,hbsub,by linarith [hT.2],?_,?_⟩
  · exact (mem_logPrimes_iff _ _ _).mpr ⟨hd.1,by linarith [hT.1],by linarith [hT.2]⟩
  · exact (mem_logPrimes_iff _ _ _).mpr ⟨hqp,by linarith [hT.1],by linarith [hT.2]⟩

/-- The count-independent logarithmic scale for the literal clipped
owner boundary, before summing counts or shells. -/
def boundaryCountCost (k : ℕ) : ℝ :=
  1536*(2*shellMass)^k/(k.factorial : ℝ)

private theorem responseConstant_le (k : ℕ) : responseConstant k ≤ 6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ) ≤ (2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    have ht : (2 : ℕ)^(k-2) ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hh.trans ht
  have h0 := hp 0
  have h1 := hp 1
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  unfold responseConstant
  nlinarith only [h0,h1,hpow]

/-- A literal clipped-owner population at ANY count, with the original
phase, physical/allocation masks, and only the cofactor shell assumed.
The count-to-radial conversion is avoided, preserving a summable 1/H
price even when the owner share tends to zero. -/
theorem close_owner_cofactor_shell_norm_bound {k N : ℕ} (hk : 0 < k)
    (A D : Finset ℕ) (y : ℝ) {v L H : ℝ} (hH : 10000 ≤ H)
    (hv : 0 < v) (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hD : ∀ n ∈ D, Squarefree n ∧ n.primeFactors.card=k+2 ∧
      (v-1/16 < log n ∧ log n ≤ v+1/16) ∧
      ZetaRieszOwnerTieFloor.CloseOwners n ∧
        (n/largestPrime n).primeFactors ⊆ shellPrimes H) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      (boundaryCountCost k/H)*(amplitude N v/v) := by
  have hH0 : 0 < H := by linarith
  let R := (ZetaRieszCofactorMass.products k (4*H)).filter (fun b : ℕ =>
    Squarefree b ∧ b.primeFactors.card=k ∧ b.primeFactors ⊆ shellPrimes H ∧
      log b ≤ v-2*H+1/16)
  let V := R.sigma (fun b => (ZetaRieszOwnerTieFloor.pairWindow v b).product
    (ZetaRieszOwnerTieFloor.pairWindow v b))
  let label := fun x : Σ _ : ℕ, ℕ×ℕ => x.2.1*(x.2.2*x.1)
  let f := fun n => if n ∈ D then
    ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ else 0
  let B := 2*amplitude N v*responseConstant (k+2)/L
  have hL0 : 0 < L := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity [amplitude_nonneg N hv.le,responseConstant_pos (k+2)]
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hcover : D ⊆ V.image label := by
    intro n hn
    obtain ⟨hs,hc,hT,htie,hshell⟩ := hD n hn
    obtain ⟨b,q,he,hb,hbc,hbsub,hcap,hpw,hqw⟩ :=
      close_owner_cofactor_shell_cover hs hc hk htie hT hshell
    have hbm : b ∈ ZetaRieszCofactorMass.products k (4*H) :=
      ZetaRieszCofactorMass.mem_products_of_squarefree hb hbc
        (fun r hr => (shellPrimes_data (hbsub hr)).2.2)
    exact Finset.mem_image.mpr ⟨⟨b,(largestPrime n,q)⟩,Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨hbm,hb,hbc,hbsub,hcap⟩,
        Finset.mem_product.mpr ⟨hpw,hqw⟩⟩,he.symm⟩
  have hfirst : (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤ ∑ x ∈ V, f (label x) := by
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => hf n)).trans
      (Finset.sum_image_le_of_nonneg (fun n _ => hf n))
    simpa only [f,ite_true,Finset.sum_congr rfl (fun n hn => if_pos hn)] using hh
  have hpoint (b : ℕ) (hb : b ∈ R) (p q : ℕ) :
      f (p*(q*b)) ≤ B*(4*H*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹ := by
    obtain ⟨_,hbs,hbc,hbsub,_⟩ := Finset.mem_filter.mp hb
    have hb1 : b ≠ 1 := by intro hh; simp [hh] at hbc; omega
    have hm : log b.minFac ≤ 4*H := (shellPrimes_data
      (hbsub ((Nat.minFac_prime hb1).mem_primeFactors (Nat.minFac_dvd b) hbs.ne_zero))).2.2
    by_cases hn : p*(q*b) ∈ D
    · have hd := hD _ hn
      have hT : |log (p*(q*b) : ℕ)-v| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hd.2.2.1.1],by linarith [hd.2.2.1.2]⟩
      have hh := ZetaRieszOwnerTieFloor.boundary_atom_norm A y hv hNv hL0 hd.1 hd.2.1
        hb1 (dvd_mul_of_dvd_right (dvd_mul_left b q) p) hT
      dsimp only [f]
      rw [if_pos hn]
      have hle := mul_le_mul_of_nonneg_left hm (by positivity :
        0 ≤ B*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)
      have heq : B*(log b.minFac/(p*(q*b) : ℕ)) =
          (B*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)*log b.minFac := by
        simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
        ring
      change _ ≤ B*(log b.minFac/(p*(q*b) : ℕ)) at hh
      rw [heq] at hh
      exact hh.trans (by convert hle using 1; ring)
    · dsimp only [f]
      rw [if_neg hn]
      positivity
  have hrec := shell_cofactor_mass_le R k (by linarith : 1 ≤ H) (by
    intro b hb
    have hh := (Finset.mem_filter.mp hb).2
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩)
  have hsum : (∑ x ∈ V, f (label x)) ≤
      B*(4*H)*(4/H^2)*(shellMass^k/(k.factorial : ℝ)) := by
    change (∑ x ∈ R.sigma _, f (label x)) ≤ _
    rw [Finset.sum_sigma]
    have hrow (b : ℕ) (hb : b ∈ R) :
        (∑ pq ∈ (ZetaRieszOwnerTieFloor.pairWindow v b).product
          (ZetaRieszOwnerTieFloor.pairWindow v b), f (pq.1*(pq.2*b))) ≤
        B*(4*H)*(4/H^2)*(b : ℝ)⁻¹ := by
      rw [Finset.product_eq_sprod,Finset.sum_product]
      have hh := Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
        (fun p _ => Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
          (fun q _ => hpoint b hb p q))
      have hm := shell_pairWindow_mass hH (Finset.mem_filter.mp hb).2.2.2.2
      have hsq := pow_le_pow_left₀ (by positivity) hm 2
      have heq : (∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b,
          ∑ q ∈ ZetaRieszOwnerTieFloor.pairWindow v b,
            B*(4*H*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹) =
          (B*(4*H*(b : ℝ)⁻¹))*(∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b,(p : ℝ)⁻¹)^2 := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul,← Finset.mul_sum,pow_two]
        ring
      rw [heq] at hh
      have hpay := mul_le_mul_of_nonneg_left hsq
        (by positivity : 0 ≤ B*(4*H*(b : ℝ)⁻¹))
      exact hh.trans (by convert hpay using 1; field_simp; ring)
    have hh := Finset.sum_le_sum hrow
    rw [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hrec (by positivity))
  have hpre : B ≤ 4*(amplitude N v/v)*responseConstant (k+2) := by
    have hh := div_le_div_of_nonneg_left
      (by positivity [amplitude_nonneg N hv.le,responseConstant_pos (k+2)] :
        0 ≤ 2*amplitude N v*responseConstant (k+2))
      (by positivity : 0 < v/2) hL
    convert hh using 1
    all_goals first | rfl | ring
  have hcost := mul_le_mul_of_nonneg_right hpre
    (by positivity [shellMass_pos] : 0 ≤ (4*H)*(4/H^2)*(shellMass^k/(k.factorial : ℝ)))
  have heq : (4*(amplitude N v/v)*responseConstant (k+2))*
      ((4*H)*(4/H^2)*(shellMass^k/(k.factorial : ℝ))) =
      (64*(amplitude N v/v)*responseConstant (k+2)*(shellMass^k/(k.factorial : ℝ)))*(1/H) := by
    field_simp
    ring
  rw [heq] at hcost
  have hr : responseConstant (k+2) ≤ 24*(2 : ℝ)^k := by
    have hh := responseConstant_le (k+2)
    norm_num [pow_add] at hh
    convert hh using 1
    ring
  have hpay := mul_le_mul_of_nonneg_left hr (by positivity [shellMass_pos,amplitude_nonneg N hv.le] :
    0 ≤ 64*(amplitude N v/v)*(shellMass^k/(k.factorial : ℝ))*(1/H))
  have hpaid : (64*(amplitude N v/v)*responseConstant (k+2)*
      (shellMass^k/(k.factorial : ℝ)))*(1/H) ≤
        (boundaryCountCost k/H)*(amplitude N v/v) := by
    unfold boundaryCountCost
    simp only [mul_pow,div_eq_mul_inv] at hpay ⊢
    nlinarith only [hpay]
  exact hfirst.trans (hsum.trans (by simpa only [mul_assoc] using hcost.trans hpaid))

/-- One constant pays the original owner-start boundary at every count. -/
def boundaryAllCountCost : ℝ := 1536*exp (2*shellMass)

theorem boundaryAllCountCost_pos : 0 < boundaryAllCountCost := by
  unfold boundaryAllCountCost
  positivity

theorem sum_boundaryCountCost_le (I : Finset ℕ) :
    (∑ k ∈ I, boundaryCountCost k) ≤ boundaryAllCountCost := by
  have he := NormedSpace.expSeries_div_hasSum_exp (2*shellMass)
  have hh := he.summable.sum_le_tsum I (by intro k _; positivity [shellMass_pos])
  rw [he.tsum_eq,← Real.exp_eq_exp_ℝ] at hh
  have hb := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1536)
  simpa only [boundaryCountCost,boundaryAllCountCost,← Finset.mul_sum,mul_div_assoc] using hb

/-- Actual close-owner boundary mass is summed across ALL counts with
no shell requirement on the owner and no count-dependent radial cost. -/
theorem all_count_cofactor_shell_norm_bound (A D : Finset ℕ) (y : ℝ) (N : ℕ)
    {v L H : ℝ} (hH : 10000 ≤ H) (hv : 0 < v)
    (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hD : ∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v-1/16 < log n ∧ log n ≤ v+1/16) ∧
      ZetaRieszOwnerTieFloor.CloseOwners n ∧
        (n/largestPrime n).primeFactors ⊆ shellPrimes H) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      (boundaryAllCountCost/H)*(amplitude N v/v) := by
  let I := D.image (fun n => n.primeFactors.card-2)
  let S := fun k => D.filter (fun n => n.primeFactors.card-2=k)
  let f := fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n‖
  have hI : ∀ k ∈ I, 0 < k := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have hh := (hD n hn).2.1
    omega
  have hrow (k : ℕ) (hk : k ∈ I) :
      (∑ n ∈ S k, f n) ≤ (boundaryCountCost k/H)*(amplitude N v/v) := by
    apply close_owner_cofactor_shell_norm_bound (hI k hk) A (S k) y hH hv hNv hL
    intro n hn
    obtain ⟨hn,hcount⟩ := Finset.mem_filter.mp hn
    have hh := hD n hn
    exact ⟨hh.1,by omega,hh.2.2⟩
  have heq : (∑ k ∈ I, ∑ n ∈ S k, f n)=∑ n ∈ D, f n :=
    Finset.sum_fiberwise_of_maps_to (f := f) (fun n hn =>
      Finset.mem_image_of_mem (fun n => n.primeFactors.card-2) hn)
  have hh := Finset.sum_le_sum hrow
  rw [heq,← Finset.sum_mul,← Finset.sum_div] at hh
  have hcost := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_boundaryCountCost_le I) (by linarith : 0 ≤ H))
    (div_nonneg (amplitude_nonneg N hv.le) hv.le)
  exact hh.trans hcost

/-- Literal owner-start clips are paid by the identified boundary norm
after retaining their original masks, allocation and full complex phase. -/
theorem clipped_start_shell_norm_bound (A D : Finset ℕ) (y : ℝ) (N : ℕ)
    {v L H : ℝ} (hH : 10000 ≤ H) (hv : 0 < v)
    (hNv : (N : ℝ)+1 ≤ v) (hy : 54 ≤ y) (hL : v/2 ≤ L)
    (hD : ∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v-Real.pi/y < log n ∧ log n ≤ v+Real.pi/y) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors, v-Real.pi/y-log (n/largestPrime n : ℕ) < log q) ∧
      (n/largestPrime n).primeFactors ⊆ shellPrimes H) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      (boundaryAllCountCost/H)*(amplitude N v/v) := by
  apply all_count_cofactor_shell_norm_bound A D y N hH hv hNv hL
  have hy0 : 0 < y := by linarith
  have hπ : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  intro n hn
  obtain ⟨hs,hc,hT,hclip,hshell⟩ := hD n hn
  exact ⟨hs,hc,⟨by linarith [hT.1],by linarith [hT.2]⟩,
    owner_start_clipped_close hs hc hy hT hclip,hshell⟩

/-- Every factorial order is retained after the independently paid
allocation replacement on genuine hinges. -/
theorem selectedAmplitude_full (N : ℕ) (b T : ℝ) (hT : T ≠ 0) :
    selectedAmplitude N (Finset.range (N+2)) b T = amplitude N T := by
  rw [selectedAmplitude_eq _ (Finset.Subset.refl _) hT,
    ZetaRieszJointAllocation.mass_total,mul_one]

private theorem boundedShare_empty (N n : ℕ) :
    ZetaRieszJointAllocation.boundedShare ∅ N n=0 := by
  simp [ZetaRieszJointAllocation.boundedShare,ZetaRieszJointAllocation.allocationShare,
    ZetaRieszJointAllocation.assignedAmplitude]

/-- Exact physical atom of the unallocated hinge main already present
in the current floor ledger. No prime is completed or filtered anew. -/
theorem unallocated_atom_eq {a k p : ℕ} (ha : Squarefree a) (hc : a.primeFactors.card=k)
    (hk : 2 ≤ k) (hp : p.Prime) (hmax : ∀ q ∈ a.primeFactors, q < p)
    {L : ℝ} (hL : 0 < L) (e y : ℝ) (N : ℕ) :
    signedPart e ∅ L y N (p*a) =
      (1/L/a)*(e*partResponse e k L (log p+log a) a*
        (amplitude N (log p+log a)*(p : ℝ)⁻¹*cos (y*(log p+log a)))) := by
  have hpd : ¬p ∣ a := by
    intro hd
    exact (hmax p (hp.mem_primeFactors hd ha.ne_zero)).false
  have hlog : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  have hscale : 0 ≤ log (p*a : ℕ)/L := div_nonneg (log_natCast_nonneg _) hL.le
  have hm : max (e*((-1 : ℝ)^(k+1)*(-(log (p*a : ℕ)/L)*
      response L (log (p*a : ℕ)) a))) 0 =
      (log (p*a : ℕ)/L)*partResponse e k L (log (p*a : ℕ)) a := by
    unfold partResponse
    rw [mul_max_of_nonneg _ _ hscale,mul_zero]
    congr 1
    ring
  have hex : exp (-(3/2 : ℝ)*log (p*a : ℕ)) =
      exp (-log (p*a : ℕ)/2)*(p : ℝ)⁻¹*(a : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*log (p*a : ℕ) = -log (p*a : ℕ)/2-log (p*a : ℕ) by ring,
      exp_sub,exp_log (by exact_mod_cast Nat.mul_pos hp.pos (Nat.pos_of_ne_zero ha.ne_zero)),
      Nat.cast_mul]
    ring
  rw [signedPart,ZetaRieszOneSidedArithmetic.weight,ZetaRieszOneSidedArithmetic.amplitude,
    ZetaRieszGlobalPrimePeriod.coefficient_eq_response ha (by omega) hp hpd,
    hc,Complex.ofReal_re,hm,hex,hlog,boundedShare_empty,sub_zero,one_mul]
  unfold amplitude
  rw [pow_succ]
  simp only [div_eq_mul_inv]
  ring

/-- Signed complete-prime-period floor for the EXACT unallocated hinge main.
All factorial orders are summed before pricing the cutoff variation. -/
theorem unallocated_fibre_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    {v y L : ℝ} (hv : 100 ≤ v) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : 0 < L) {a : ℕ} (ha : Squarefree a)
    (hcnt : a.primeFactors.card=k)
    (howner : ∀ q ∈ a.primeFactors, Real.log q ≤ v-Real.pi/y-Real.log a)
    (hlog : 5000 ≤ v-Real.pi/y-Real.log a)
    (hpeak : Real.sin (y*v) = 0) (hsign : e*Real.cos (y*v) ≤ 0) :
    -(2*amplitude N v/(L*a))*
        (responseConstant k*Real.log a.minFac*jointPeriodCost N v y (Real.log a)+
          ((2 : ℝ)^k*Real.pi/(4*y))/(v-Real.pi/y-Real.log a)) ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  let D := logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)
  let S := Finset.range (N+2)
  let R := fun p : ℕ => partResponse e k L (Real.log p+Real.log a) a
  let R₀ := partResponse e k L v a
  let w := fun p : ℕ => selectedAmplitude N S (Real.log a) (Real.log p+Real.log a)*(p : ℝ)⁻¹
  let g := fun p => w p*Real.cos (y*(Real.log p+Real.log a))
  let E := (2 : ℝ)^k*Real.pi/(4*y)
  let B := responseConstant k*Real.log a.minFac
  let W := 2*amplitude N v
  let b := v-Real.pi/y-Real.log a
  let c := e*R₀
  have hS : S ⊆ Finset.range (N+2) := Finset.Subset.refl _
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := hL
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hd : Squarefree a ∧ a.primeFactors.card=k := ⟨ha,hcnt⟩
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hB : 0 ≤ B := mul_nonneg (responseConstant_pos k).le (Real.log_natCast_nonneg _)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (amplitude_nonneg N hv0.le)
  have hcost : 0 ≤ jointPeriodCost N v y (Real.log a) := by
    have ht : 0 < v-Real.pi/y := by dsimp [b] at hb0; linarith [Real.log_natCast_nonneg a]
    unfold jointPeriodCost
    positivity
  have hgeo (p : ℕ) (hp : p ∈ D) := owner_fibre_geometry ha howner hp
  have hT (p : ℕ) (hp : p ∈ D) : Real.log a < Real.log p+Real.log a := by
    have hp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast (hgeo p hp).1.one_lt)
    linarith
  have hc : |c| ≤ B := by
    dsimp only [c,R₀]
    rw [abs_mul,he,one_mul]
    exact (partResponse_bound he k L v a).trans (response_bound ha hcnt hk L v)
  have hcphase : c*Real.cos (y*v) ≤ 0 := by
    have hr : 0 ≤ R₀ := le_max_right _ _
    have hh := mul_nonpos_of_nonneg_of_nonpos hr hsign
    dsimp only [c]
    nlinarith only [hh]
  have hperiod := selected_period_floor S hS (Real.log_natCast_nonneg a) hlog hy hNv hpeak hcphase
  have hmass := (factorial_period_floor N hlog hy hNv hpeak (c := 0) (by simp)).2
  have hmass' : (∑ p ∈ D, w p) ≤ W/b := by
    have hm : (∑ p ∈ D, w p) ≤
        ∑ p ∈ D, amplitude N (Real.log p+Real.log a)*(p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (selectedAmplitude_bounds S hS (Real.log_natCast_nonneg a) (hT p hp)).2
        (inv_nonneg.mpr (Nat.cast_nonneg p))
    exact hm.trans hmass
  have hw (p : ℕ) (hp : p ∈ D) : 0 ≤ w p :=
    mul_nonneg (selectedAmplitude_bounds S hS (Real.log_natCast_nonneg a) (hT p hp)).1
      (inv_nonneg.mpr (Nat.cast_nonneg p))
  have hg (p : ℕ) (hp : p ∈ D) : |g p| ≤ w p := by
    dsimp only [g]
    rw [abs_mul,abs_of_nonneg (hw p hp)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hw p hp)).trans_eq (mul_one _)
  have hR (p : ℕ) (hp : p ∈ D) : |R p-R₀| ≤ E := by
    have hpT := (hgeo p hp).2.2.2
    have hdisp : |Real.log p+Real.log a-v| ≤ Real.pi/y :=
      abs_le.mpr ⟨by linarith [hpT.1],by linarith [hpT.2]⟩
    exact (((partResponse_variation he k L (Real.log p+Real.log a) v a).trans
      (response_variation ha hcnt hk L _ _)).trans
        (mul_le_mul_of_nonneg_left hdisp (by positivity : (0 : ℝ) ≤ 2^k/4))).trans_eq
          (by dsimp [E]; ring)
  have herr : |e*(∑ p ∈ D, (R p-R₀)*g p)| ≤ E*(∑ p ∈ D, w p) := by
    rw [abs_mul,he,one_mul,Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun p hp => by
      rw [abs_mul]
      exact mul_le_mul (hR p hp) (hg p hp) (abs_nonneg _) hE)
  have hsplit : e*(∑ p ∈ D, R p*g p) =
      c*(∑ p ∈ D, g p)+e*(∑ p ∈ D, (R p-R₀)*g p) := by
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by dsimp only [c]; ring)
  have hbound : -W*(B*jointPeriodCost N v y (Real.log a)+E/b) ≤
      e*(∑ p ∈ D, R p*g p) := by
    have hc' := mul_le_mul_of_nonneg_right hc (mul_nonneg hW hcost)
    have hm := mul_le_mul_of_nonneg_left hmass' hE
    have hs := hperiod
    have hh := (abs_le.mp herr).1
    change -2*|c| *amplitude N v*jointPeriodCost N v y (Real.log a) ≤ c*(∑ p ∈ D, g p) at hs
    rw [hsplit]
    dsimp only [W] at hc' hm ⊢
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hc',hm,hs,hh]
  have heq : (∑ p ∈ D,
      signedPart e ∅ L y N (p*a)) =
      (1/L/a)*(e*(∑ p ∈ D, R p*g p)) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [unallocated_atom_eq ha hcnt hk (hgeo p hp).1 (hgeo p hp).2.1 hL e y N]
    have hT0 : Real.log p+Real.log a ≠ 0 := ne_of_gt
      ((Real.log_natCast_nonneg a).trans_lt (hT p hp))
    dsimp only [R,g,w,S]
    rw [selectedAmplitude_full N (Real.log a) _ hT0]
    ring
  change -(W/(L*a))*(B*jointPeriodCost N v y (Real.log a)+E/b) ≤ _
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 1/L/a by positivity)
  calc
    _ = (1/L/a)*(-W*(B*jointPeriodCost N v y (Real.log a)+E/b)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := hh

/-- Count-k unallocated row, with no numerical cofactor-share cap. -/
theorem unallocated_shell_row_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e|=1)
    {v y L H : ℝ} (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : v/2 ≤ L) {a : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card=k) (hshell : a.primeFactors ⊆ shellPrimes H)
    (howner : ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(amplitude N v/v)*(481*(2 : ℝ)^k/H)*(a : ℝ)⁻¹ ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  have ha1 : a ≠ 1 := by intro hh; simp [hh] at hc; omega
  have hmin := (Nat.minFac_prime ha1).mem_primeFactors (Nat.minFac_dvd a) ha.ne_zero
  have hminshell := (shellPrimes_data (hshell hmin)).2
  have hH0 : 0 < H := by linarith
  have hP : H ≤ v-Real.pi/y-log a := hminshell.1.trans (howner _ hmin)
  have hπ0 : 0 ≤ Real.pi/y := by positivity
  have hv100 : 100 ≤ v := by linarith [log_natCast_nonneg a]
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have hP0 : 0 < v-Real.pi/y-log a := hH0.trans_le hP
  let B := responseConstant k*log a.minFac
  let E := (2 : ℝ)^k*Real.pi/(4*y)
  have hB : 0 ≤ B := by dsimp [B]; positivity [responseConstant_pos k,log_natCast_nonneg a.minFac]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hV0 : 0 < v-Real.pi/y := by linarith [log_natCast_nonneg a]
  have hCb : 0 ≤ jointPeriodCost N v y (log a) := by
    unfold jointPeriodCost
    positivity
  have hBbound : B ≤ responseConstant k*(4*H) :=
    mul_le_mul_of_nonneg_left hminshell.2 (responseConstant_pos k).le
  have hEbound : E ≤ (2 : ℝ)^k/64 := by
    have hh := mul_le_mul_of_nonneg_left (quarter_period_width_le hy)
      (by positivity : (0 : ℝ) ≤ 2^k)
    exact (show E=(2 : ℝ)^k*(Real.pi/(4*y)) by dsimp [E]; ring) ▸
      hh.trans_eq (by ring)
  have hinner : B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a) ≤
      (20*responseConstant k+(2 : ℝ)^k/64)/H := by
    have hbc := mul_le_mul hBbound (jointPeriodCost_shell_le hy hNv hH0 hP)
      hCb (by positivity [responseConstant_pos k])
    have hec := (div_le_div_of_nonneg_left hE hH0 hP).trans
      (div_le_div_of_nonneg_right hEbound hH0.le)
    have heq : (responseConstant k*(4*H))*(5/H^2)+((2 : ℝ)^k/64)/H =
        (20*responseConstant k+(2 : ℝ)^k/64)/H := by
      field_simp
      ring
    exact (add_le_add hbc hec).trans_eq heq
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hpre : 2*amplitude N v/(L*a) ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity [amplitude_nonneg N hv0.le] :
        0 ≤ 2*amplitude N v) (by positivity : 0 < v/2) hL)
      (inv_nonneg.mpr ha0.le)
    convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have htotal := mul_le_mul hpre hinner (by positivity :
      0 ≤ B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a))
      (by positivity : 0 ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹)
  have hcoeff : 4*(20*responseConstant k+(2 : ℝ)^k/64) ≤ 481*(2 : ℝ)^k := by
    nlinarith only [responseConstant_le k,(show 0 ≤ (2 : ℝ)^k by positivity)]
  have hcost := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hcoeff hH0.le)
    (mul_nonneg hbase (inv_nonneg.mpr ha0.le))
  have hfloor := unallocated_fibre_floor hk he hv100 hNv hy hL0 ha hc howner
    (by linarith : 5000 ≤ v-Real.pi/y-log a) hpeak hsign
  change -(2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a)) ≤ _ at hfloor
  have hpaid : (2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a)) ≤
      (amplitude N v/v)*(481*(2 : ℝ)^k/H)*(a : ℝ)⁻¹ := by
    exact htotal.trans (by convert hcost using 1 <;> ring)
  rw [neg_mul] at hfloor
  simpa only [neg_mul] using (neg_le_neg hpaid).trans hfloor

/-- Count symmetry prices the full selected unallocated population, not
a completed cofactor or a separately bounded factorial channel. -/
theorem unallocated_shell_population_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e|=1)
    (S : Finset ℕ) {v y L H : ℝ} (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : v/2 ≤ L)
    (hS : ∀ a ∈ S, Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ shellPrimes H)
    (howner : ∀ a ∈ S, ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(ownerCountCost k/H)*(amplitude N v/v) ≤
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  have hv0 : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hrow := Finset.sum_le_sum (fun a (ha : a ∈ S) =>
    unallocated_shell_row_floor hk he hH hNv hy hL (hS a ha).1 (hS a ha).2.1
      (hS a ha).2.2 (howner a ha) hpeak hsign)
  rw [← Finset.mul_sum] at hrow
  have hmass := shell_cofactor_mass_le S k (by linarith : 1 ≤ H) hS
  have hconst : 0 ≤ 481*(2 : ℝ)^k/H :=
    div_nonneg (by positivity) (by linarith)
  have hprice := mul_le_mul_of_nonpos_left hmass
    (show -(amplitude N v/v)*(481*(2 : ℝ)^k/H) ≤ 0 from
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbase) hconst)
  calc
    _ = (-(amplitude N v/v)*(481*(2 : ℝ)^k/H))*(shellMass^k/(k.factorial : ℝ)) := by
      unfold ownerCountCost
      rw [mul_pow]
      ring
    _ ≤ _ := hprice.trans hrow

/-- All cofactor counts are priced once, including growing counts with
owner share tending to zero. The old numerical cofactor cap is absent. -/
theorem unallocated_all_counts_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (S : ℕ → Finset ℕ) {v y L H : ℝ} (hI : ∀ k ∈ I, 2 ≤ k) (he : |e|=1)
    (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hL : v/2 ≤ L)
    (hS : ∀ k ∈ I, ∀ a ∈ S k, Squarefree a ∧ a.primeFactors.card=k ∧
      a.primeFactors ⊆ shellPrimes H)
    (howner : ∀ k ∈ I, ∀ a ∈ S k, ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(ownerAllCountCost/H)*(amplitude N v/v) ≤
      ∑ k ∈ I, ∑ a ∈ S k, ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  have hrow := Finset.sum_le_sum (fun k hk => unallocated_shell_population_floor (hI k hk)
    he (S k) hH hNv hy hL (hS k hk) (howner k hk) hpeak hsign)
  have hv0 : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hcost := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_ownerCountCost_le I) (by linarith : 0 ≤ H))
    (div_nonneg (amplitude_nonneg N hv0.le) hv0.le)
  have hb := neg_le_neg hcost
  simpa only [neg_mul] using hb.trans (by simpa only [neg_mul,Finset.sum_neg_distrib,
    ← Finset.sum_mul,← Finset.sum_div] using hrow)

/-- One shared price for the cap-free unallocated main and its literal
ownership boundary, after joining every selected prime count. -/
def joinedOwnerCost : ℝ := ownerAllCountCost+boundaryAllCountCost

theorem joinedOwnerCost_pos : 0 < joinedOwnerCost := by
  exact add_pos ownerAllCountCost_pos boundaryAllCountCost_pos

theorem joinedOwnerCost_eq : joinedOwnerCost=2114977792 := by
  have he : exp (2*shellMass)=(4 : ℝ)^10 := by
    calc
      _ = exp (log ((4 : ℝ)^10)) := by
        congr 1
        rw [log_pow]
        unfold shellMass
        norm_num
        ring
      _ = _ := exp_log (by positivity)
  unfold joinedOwnerCost boundaryAllCountCost
  rw [ownerAllCountCost_eq,he]
  norm_num

/-- Original clipped boundary masks are charged only once even if both
staggered sign selections miss different labels. No phase freezing is used. -/
theorem unallocated_period_with_boundary_floor (I : Finset ℕ) (N : ℕ)
    (e : ℝ) (S : ℕ → Finset ℕ) (D P Q : Finset ℕ) {v y L H : ℝ}
    (hI : ∀ k ∈ I, 2 ≤ k) (he : |e|=1)
    (hH : 10000 ≤ H) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hL : v/2 ≤ L)
    (hS : ∀ k ∈ I, ∀ a ∈ S k, Squarefree a ∧ a.primeFactors.card=k ∧
      a.primeFactors ⊆ shellPrimes H)
    (howner : ∀ k ∈ I, ∀ a ∈ S k, ∀ q ∈ a.primeFactors,
      log q ≤ v-Real.pi/y-log a)
    (hD : ∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v-Real.pi/y < log n ∧ log n ≤ v+Real.pi/y) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,
        v-Real.pi/y-log (n/largestPrime n : ℕ) < log q) ∧
      (n/largestPrime n).primeFactors ⊆ shellPrimes H)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(joinedOwnerCost/H)*(amplitude N v/v) ≤
      (∑ k ∈ I, ∑ a ∈ S k, ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a))+
      (∑ n ∈ D\P, signedPart 1 ∅ L y N n)+
      (∑ n ∈ D\Q, signedPart (-1) ∅ L y N n) := by
  have hv : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hmain := unallocated_all_counts_floor I N e S hI he (by linarith)
    hNv hy hL hS howner hpeak hsign
  have hnorm := clipped_start_shell_norm_bound ∅ D y N hH hv (by linarith) hy hL hD
  have hparts := ZetaRieszOwnerTieFloor.missed_parts_floor ∅ D P Q L y N
  have hb := (neg_le_neg hnorm).trans hparts
  have hj := add_le_add hmain hb
  unfold joinedOwnerCost
  simpa only [add_div,neg_add,add_mul,neg_mul,add_assoc] using hj

/-- The combined owner-start/main cost stays summable across all owner
logarithm shells. Neither the count ceiling nor the number of shells appears. -/
theorem sum_joined_dyadic_cost_le (J : Finset ℕ) {H : ℝ} (hH : 0 < H) :
    (∑ j ∈ J, joinedOwnerCost/(H*(2 : ℝ)^j)) ≤ 2*joinedOwnerCost/H := by
  have hh := mul_le_mul_of_nonneg_left (sum_inverse_dyadic_shells_le J hH)
    joinedOwnerCost_pos.le
  have hterm (j : ℕ) : joinedOwnerCost/(H*(2 : ℝ)^j)=
      joinedOwnerCost*(1/(H*(2 : ℝ)^j)) := by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  exact hh.trans_eq (by ring)

/-- On actual retained hinges with a polynomially large owner, every prime
of the complete owner period still lies in the ORIGINAL physical prime mask.
This removes a support premise without completing arbitrary prime labels. -/
theorem hinge_whole_fibre_mem_intermediate {u : ℝ} {N K n : ℕ} {v y : ℝ}
    (hN : 1 ≤ N) (hh : n ∈ ZetaRieszHingeAllocationPayment.hingeLabels u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hy : 54 ≤ y) (hT : v-Real.pi/y < log n ∧ log n ≤ v+Real.pi/y)
    (hlarge : 32*log ((N : ℝ)+1) < log (largestPrime n))
    (hlog : 1 ≤ log ((N : ℝ)+1)) :
    ∀ p ∈ logPrimes (v-Real.pi/y-log (n/largestPrime n : ℕ)) (2*Real.pi/y),
      p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  obtain ⟨hcentral,hs,e,he,hhinge,hgap⟩ := Finset.mem_filter.mp hh
  have hc := (Finset.mem_filter.mp hcentral).1
  have hP := ZetaRieszHingeAllocationPayment.hinge_owner_log_le hc hs he hhinge hgap hL
  have hd := canonical_owner_data hs (by
    have hg := ZetaRieszJointPrimeEnergy.core_count hc
    omega)
  have hprod : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hd.2.1,Nat.cast_mul,log_mul
      (by exact_mod_cast hd.1.ne_zero) (by exact_mod_cast hd.2.2.1.ne_zero)]
  have hy0 : 0 < y := by linarith
  have hπ : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hlogN : log N ≤ log ((N : ℝ)+1) :=
    log_le_log (by exact_mod_cast (by omega : 0 < N)) (by linarith)
  apply whole_fibre_mem_intermediate hN
  · linarith only [hT.2,hprod,hlarge,hlog,hlogN,hπ]
  · have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith only [hT.1,hprod,hP,hL,hπ,hNR]

/-- The combined price vanishes relative to its SAME selected radial
units. This is not a norm payment on the exponentially growing whole core. -/
theorem tendsto_joined_logarithmic_price :
    Tendsto (fun N : ℕ => 2*joinedOwnerCost/(8*log ((N : ℝ)+1))) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := (tendsto_log_atTop.comp hn).const_mul_atTop (by norm_num : (0 : ℝ) < 8)
  simpa only [Function.comp_def] using (tendsto_const_nhds.div_atTop hl :
    Tendsto (fun N : ℕ => 2*joinedOwnerCost/(8*log ((N : ℝ)+1))) atTop (𝓝 0))

private theorem old_orbits_weighted_zero {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (w : ℂ) :
    (∑ db ∈ cancelledOrbitDivisors u N n,
      w*
        (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
          (largestPrime n) db.2 : ℂ)) = 0 := by
  unfold cancelledOrbitDivisors
  dsimp only
  split_ifs with h
  · have hcop := (canonical_block_data hn hs).2.2
    rw [Finset.sum_biUnion (by
      intro e he f hf hef
      exact orbitDivisors_disjoint hcop (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hef)]
    apply Finset.sum_eq_zero
    intro e he
    obtain ⟨he,hgeom⟩ := Finset.mem_filter.mp he
    exact weighted_orbit_eq_zero (core_data hn hs).2.1 (core_data hn hs).1 h.1
      (Nat.dvd_of_mem_divisors he) h.2 (by linarith [hgeom.2.1]) hgeom.2.2.1 _
  · exact Finset.sum_empty

/-- Every original zero deletion remains exact after the ALREADY paid
allocation replacement. Thus the new full-factorial period inequality applies
to the literal retained antidiagonal, with no hidden completion credit. -/
theorem unallocated_retained_atom_eq {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (y : ℝ) :
    residualCoefficient ∅
      (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
          (cancelledOrbitDivisors u N n ∪ affineDivisors u N n),
        phaseWeight ∅
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ) := by
  have hd := core_data hn hs
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hco := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have hpa : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hr := residual_atom_eq_convolution hd.2.1 hd.2.2 hd.1 hco.2.2.2
    ∅
    (SquarefreeVaughanLogSource.length u N) y N
  rw [hpa] at hr
  rw [hr]
  have hsub : cancelledOrbitDivisors u N n ∪ affineDivisors u N n ⊆
      (n/largestPrime n).divisorsAntidiagonal :=
    Finset.union_subset (cancelledOrbitDivisors_subset hn hs) (affineDivisors_subset hn hs)
  have he := Finset.sum_sdiff (f := fun db : ℕ×ℕ =>
    phaseWeight ∅
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
      (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
        (largestPrime n) db.2 : ℂ)) hsub
  have hz : (∑ db ∈ cancelledOrbitDivisors u N n ∪ affineDivisors u N n,
      phaseWeight ∅ (SquarefreeVaughanLogSource.length u N) N y
        (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
          (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ))=0 := by
    rw [Finset.sum_union (affine_disjoint_old_cancelled hn hs).symm,
      old_orbits_weighted_zero hn hs,affine_literal_sum_eq_zero hn hs,add_zero]
  rw [hz,add_zero] at he
  exact he.symm

/-- The original retained hinge incidences equal both full-factorial
arithmetic sign parts, including their unchanged total-log phase. -/
theorem unallocated_retained_real_eq_parts {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (y : ℝ) :
    (∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ affineDivisors u N n),
      phaseWeight ∅ (SquarefreeVaughanLogSource.length u N) N y
        (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
        (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re =
      signedPart 1 ∅ (SquarefreeVaughanLogSource.length u N) y N n+
      signedPart (-1) ∅ (SquarefreeVaughanLogSource.length u N) y N n := by
  rw [← unallocated_retained_atom_eq hn hs y,← signedPart_add]

/-- All selected owner geometries and their actual clipped-start labels
are joined before pricing. Every factorial order and original sign survives. -/
theorem unallocated_dyadic_period_floor (J : Finset ℕ) (I : ℕ → Finset ℕ)
    (N : ℕ) (e : ℝ) (S : ℕ → ℕ → Finset ℕ) (D P Q : ℕ → Finset ℕ)
    {v y L H : ℝ} (hI : ∀ j ∈ J, ∀ k ∈ I j, 2 ≤ k) (he : |e|=1)
    (hH : 10000 ≤ H) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hL : v/2 ≤ L)
    (hS : ∀ j ∈ J, ∀ k ∈ I j, ∀ a ∈ S j k, Squarefree a ∧
      a.primeFactors.card=k ∧ a.primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j))
    (howner : ∀ j ∈ J, ∀ k ∈ I j, ∀ a ∈ S j k, ∀ q ∈ a.primeFactors,
      log q ≤ v-Real.pi/y-log a)
    (hD : ∀ j ∈ J, ∀ n ∈ D j, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v-Real.pi/y < log n ∧ log n ≤ v+Real.pi/y) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,
        v-Real.pi/y-log (n/largestPrime n : ℕ) < log q) ∧
      (n/largestPrime n).primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j))
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(2*joinedOwnerCost/H)*(amplitude N v/v) ≤
      ∑ j ∈ J,
        ((∑ k ∈ I j, ∑ a ∈ S j k,
          ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
            signedPart e ∅ L y N (p*a))+
          (∑ n ∈ D j\P j, signedPart 1 ∅ L y N n)+
          (∑ n ∈ D j\Q j, signedPart (-1) ∅ L y N n)) := by
  have hH0 : 0 < H := by linarith
  have hheight (j : ℕ) : 10000 ≤ H*(2 : ℝ)^j := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) :
      (1 : ℝ) ≤ 2^j) hH0.le
    exact hH.trans (by simpa only [mul_one] using hh)
  have hrows := Finset.sum_le_sum (fun j hj => unallocated_period_with_boundary_floor
    (I j) N e (S j) (D j) (P j) (Q j) (hI j hj) he (hheight j) hNv hy hL
      (hS j hj) (howner j hj) (hD j hj) hpeak hsign)
  have hv : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hcost := neg_le_neg (mul_le_mul_of_nonneg_right
    (sum_joined_dyadic_cost_le J hH0) (div_nonneg (amplitude_nonneg N hv.le) hv.le))
  simpa only [neg_mul] using hcost.trans (by
    simpa only [neg_mul,Finset.sum_neg_distrib,← Finset.sum_mul] using hrows)

/-- The signed price joins counts, owner geometries, clipped ownership and
radial periods against ONE shared set of radial units. Whole-fibre selection
and the original ownership/phase hypotheses are explicit. -/
theorem unallocated_radial_period_floor (V : Finset ℕ) (J : ℕ → Finset ℕ)
    (I : ℕ → ℕ → Finset ℕ) (N : ℕ) (e v : ℕ → ℝ)
    (S : ℕ → ℕ → ℕ → Finset ℕ) (D P Q : ℕ → ℕ → Finset ℕ)
    {y L H : ℝ} (hH : 10000 ≤ H) (hy : 54 ≤ y)
    (hI : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, 2 ≤ k)
    (he : ∀ i ∈ V, |e i|=1) (hNv : ∀ i ∈ V, (N : ℝ)+2 ≤ v i)
    (hL : ∀ i ∈ V, v i/2 ≤ L)
    (hS : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, ∀ a ∈ S i j k,
      Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j))
    (howner : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, ∀ a ∈ S i j k,
      ∀ q ∈ a.primeFactors, log q ≤ v i-Real.pi/y-log a)
    (hD : ∀ i ∈ V, ∀ j ∈ J i, ∀ n ∈ D i j,
      Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v i-Real.pi/y < log n ∧ log n ≤ v i+Real.pi/y) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,
        v i-Real.pi/y-log (n/largestPrime n : ℕ) < log q) ∧
      (n/largestPrime n).primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j))
    (hpeak : ∀ i ∈ V, sin (y*v i)=0)
    (hsign : ∀ i ∈ V, e i*cos (y*v i) ≤ 0) :
    -(2*joinedOwnerCost/H)*(∑ i ∈ V, amplitude N (v i)/(v i)) ≤
      ∑ i ∈ V, ∑ j ∈ J i,
        ((∑ k ∈ I i j, ∑ a ∈ S i j k,
          ∑ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) ∅ L y N (p*a))+
          (∑ n ∈ D i j\P i j, signedPart 1 ∅ L y N n)+
          (∑ n ∈ D i j\Q i j, signedPart (-1) ∅ L y N n)) := by
  have hh := Finset.sum_le_sum (fun i hi => unallocated_dyadic_period_floor
    (J i) (I i) N (e i) (S i) (D i) (P i) (Q i) (hI i hi) (he i hi) hH
      (hNv i hi) hy (hL i hi) (hS i hi) (howner i hi) (hD i hi) (hpeak i hi) (hsign i hi))
  simpa only [← Finset.mul_sum] using hh

/-- The new main-and-clipped-boundary debit eventually uses at most 1/256
of the SAME previously selected positive supply. The old supply scale stays
explicit. A disjoint literal cover is still required; no credit is reused. -/
theorem eventually_joined_owner_cost_paid {c κ h y v : ℝ}
    (hc : 0 < c) (hy : 54 ≤ y) (hhu : h ≤ 1/20)
    (hκ : κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*exp 2)) :
    ∀ᶠ N : ℕ in atTop, ∀ (w : ℕ → ℝ) (f : ℕ → ℂ) (V : Finset ℕ)
      (I J : ℕ → Finset ℕ),
      (∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2) →
      (∀ M ∈ radialIndices N,
        c*(M : ℝ)*exp (2*(M : ℝ))/((M : ℝ)+1)*
          ZetaRieszRadialCompensation.radialEnvelope N M ≤
            (∑ n ∈ supply M h (w M), f n).re) →
      V ⊆ radialIndices N →
      (∀ M ∈ V, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
        center v y i < 2*M+2) →
      (∀ M ∈ V, ∀ i ∈ J M,
        2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
        center (v+Real.pi/y) y i < 2*M+2) →
      (2*joinedOwnerCost/(8*log ((N : ℝ)+1)))*
        ((∑ i ∈ V.biUnion I, exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ V.biUnion J, exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (1/256 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re := by
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hsmall := tendsto_joined_logarithmic_price.eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < κ/2))
  filter_upwards [hsmall,eventually_ge_atTop (1 : ℕ)]
    with N hprice hN w f V I J hw hscale hV hI hJ
  have hp := ZetaRieszRoughFiveJoinedFloor.period_grids_cost_paid
    hN hc hy hhu hκ w f V I J hw hscale hV hI hJ
  let U : ℝ :=
      (∑ i ∈ V.biUnion I, exp (-center v y i/2)*(center v y i)^N/N.factorial)+
      (∑ i ∈ V.biUnion J, exp (-center (v+Real.pi/y) y i/2)*
        (center (v+Real.pi/y) y i)^N/N.factorial)
  have hnonneg : 0 ≤ U := by
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      obtain ⟨M,hM,hii⟩ := Finset.mem_biUnion.mp hi
      have hcenter : 0 ≤ center v y i :=
        (show (0 : ℝ) ≤ 2*(M : ℝ) by positivity).trans (hI M hM i hii).1
      positivity
    · apply Finset.sum_nonneg
      intro i hi
      obtain ⟨M,hM,hii⟩ := Finset.mem_biUnion.mp hi
      have hcenter : 0 ≤ center (v+Real.pi/y) y i :=
        (show (0 : ℝ) ≤ 2*(M : ℝ) by positivity).trans (hJ M hM i hii).1
      positivity
  change κ*U ≤ (1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re at hp
  change (2*joinedOwnerCost/(8*log ((N : ℝ)+1)))*U ≤ _
  calc
    _ ≤ (κ/2)*U := mul_le_mul_of_nonneg_right hprice.le hnonneg
    _ = (1/2 : ℝ)*(κ*U) := by ring
    _ ≤ (1/2 : ℝ)*((1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

/-- Retaining the radial normalization gives an additional 1/(N+2)
saving against the SAME factorial supply units. It is not an improvement
to the positive whole-core majorant, which is never used here. -/
theorem radial_cost_in_supply_units (V : Finset ℕ) (N : ℕ) (v : ℕ → ℝ)
    {H : ℝ} (hH : 0 < H) (hNv : ∀ i ∈ V, (N : ℝ)+2 ≤ v i) :
    (2*joinedOwnerCost/H)*(∑ i ∈ V, amplitude N (v i)/(v i)) ≤
      (2*joinedOwnerCost/(H*((N : ℝ)+2)))*(∑ i ∈ V, amplitude N (v i)) := by
  have hN : 0 < (N : ℝ)+2 := by positivity
  have hs : (∑ i ∈ V, amplitude N (v i)/(v i)) ≤
      (∑ i ∈ V, amplitude N (v i))/((N : ℝ)+2) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    exact div_le_div_of_nonneg_left
      (amplitude_nonneg N (hN.le.trans (hNv i hi))) hN (hNv i hi)
  have hh := mul_le_mul_of_nonneg_left hs
    (by positivity [joinedOwnerCost_pos] : 0 ≤ 2*joinedOwnerCost/H)
  exact hh.trans_eq (by simp only [div_eq_mul_inv,mul_inv_rev]; ring)

/-- Whole signed main-and-boundary estimate in exactly the positive
factorial supply units used by the current floor payment. -/
theorem unallocated_radial_supply_floor (V : Finset ℕ) (J : ℕ → Finset ℕ)
    (I : ℕ → ℕ → Finset ℕ) (N : ℕ) (e v : ℕ → ℝ)
    (S : ℕ → ℕ → ℕ → Finset ℕ) (D P Q : ℕ → ℕ → Finset ℕ)
    {y L H : ℝ} (hH : 10000 ≤ H) (hy : 54 ≤ y)
    (hI : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, 2 ≤ k)
    (he : ∀ i ∈ V, |e i|=1) (hNv : ∀ i ∈ V, (N : ℝ)+2 ≤ v i)
    (hL : ∀ i ∈ V, v i/2 ≤ L)
    (hS : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, ∀ a ∈ S i j k,
      Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j))
    (howner : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, ∀ a ∈ S i j k,
      ∀ q ∈ a.primeFactors, log q ≤ v i-Real.pi/y-log a)
    (hD : ∀ i ∈ V, ∀ j ∈ J i, ∀ n ∈ D i j,
      Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v i-Real.pi/y < log n ∧ log n ≤ v i+Real.pi/y) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,
        v i-Real.pi/y-log (n/largestPrime n : ℕ) < log q) ∧
      (n/largestPrime n).primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j))
    (hpeak : ∀ i ∈ V, sin (y*v i)=0)
    (hsign : ∀ i ∈ V, e i*cos (y*v i) ≤ 0) :
    -(2*joinedOwnerCost/(H*((N : ℝ)+2)))*(∑ i ∈ V, amplitude N (v i)) ≤
      ∑ i ∈ V, ∑ j ∈ J i,
        ((∑ k ∈ I i j, ∑ a ∈ S i j k,
          ∑ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) ∅ L y N (p*a))+
          (∑ n ∈ D i j\P i j, signedPart 1 ∅ L y N n)+
          (∑ n ∈ D i j\Q i j, signedPart (-1) ∅ L y N n)) := by
  have hp := unallocated_radial_period_floor V J I N e v S D P Q hH hy
    hI he hNv hL hS howner hD hpeak hsign
  have hc := neg_le_neg (radial_cost_in_supply_units V N v (H := H) (by linarith) hNv)
  simp only [neg_mul] at hp hc ⊢
  exact hc.trans hp

/-- Exact improved price: O(1/(N log N)) against the existing positive
supply, still with all literal cover hypotheses left visible. -/
theorem tendsto_joined_radial_price :
    Tendsto (fun N : ℕ =>
      2*joinedOwnerCost/(8*log ((N : ℝ)+1)*((N : ℝ)+2))) atTop (𝓝 0) := by
  have hh := tendsto_joined_logarithmic_price.mul
    (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))))
  simpa only [Function.comp_def,zero_mul,div_eq_mul_inv,mul_inv_rev,mul_assoc,
    mul_left_comm,mul_comm] using hh

/-- Supply comparison at the sharper O(1/(N log N)) rate, keeping the
old selected phase windows, scale and 1/256 single-use price explicit. -/
theorem eventually_joined_radial_cost_paid {c κ h y v : ℝ}
    (hc : 0 < c) (hy : 54 ≤ y) (hhu : h ≤ 1/20)
    (hκ : κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*exp 2)) :
    ∀ᶠ N : ℕ in atTop, ∀ (w : ℕ → ℝ) (f : ℕ → ℂ) (V : Finset ℕ)
      (I J : ℕ → Finset ℕ),
      (∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2) →
      (∀ M ∈ radialIndices N,
        c*(M : ℝ)*exp (2*(M : ℝ))/((M : ℝ)+1)*
          ZetaRieszRadialCompensation.radialEnvelope N M ≤
            (∑ n ∈ supply M h (w M), f n).re) →
      V ⊆ radialIndices N →
      (∀ M ∈ V, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
        center v y i < 2*M+2) →
      (∀ M ∈ V, ∀ i ∈ J M,
        2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
        center (v+Real.pi/y) y i < 2*M+2) →
      (2*joinedOwnerCost/(8*log ((N : ℝ)+1)*((N : ℝ)+2)))*
        ((∑ i ∈ V.biUnion I, exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ V.biUnion J, exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (1/256 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re := by
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hsmall := tendsto_joined_radial_price.eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < κ/2))
  filter_upwards [hsmall,eventually_ge_atTop (1 : ℕ)]
    with N hprice hN w f V I J hw hscale hV hI hJ
  have hp := ZetaRieszRoughFiveJoinedFloor.period_grids_cost_paid
    hN hc hy hhu hκ w f V I J hw hscale hV hI hJ
  let U : ℝ :=
      (∑ i ∈ V.biUnion I, exp (-center v y i/2)*(center v y i)^N/N.factorial)+
      (∑ i ∈ V.biUnion J, exp (-center (v+Real.pi/y) y i/2)*
        (center (v+Real.pi/y) y i)^N/N.factorial)
  have hnonneg : 0 ≤ U := by
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      obtain ⟨M,hM,hii⟩ := Finset.mem_biUnion.mp hi
      have hcenter : 0 ≤ center v y i :=
        (show (0 : ℝ) ≤ 2*(M : ℝ) by positivity).trans (hI M hM i hii).1
      positivity
    · apply Finset.sum_nonneg
      intro i hi
      obtain ⟨M,hM,hii⟩ := Finset.mem_biUnion.mp hi
      have hcenter : 0 ≤ center (v+Real.pi/y) y i :=
        (show (0 : ℝ) ≤ 2*(M : ℝ) by positivity).trans (hJ M hM i hii).1
      positivity
  change κ*U ≤ (1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re at hp
  change (2*joinedOwnerCost/(8*log ((N : ℝ)+1)*((N : ℝ)+2)))*U ≤ _
  calc
    _ ≤ (κ/2)*U := mul_le_mul_of_nonneg_right hprice.le hnonneg
    _ = (1/2 : ℝ)*(κ*U) := by ring
    _ ≤ (1/2 : ℝ)*((1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

end RiemannGaussian.ZetaRieszClippedOwnerPeriodFloor
