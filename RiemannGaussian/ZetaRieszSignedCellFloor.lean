/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOpenCountFloor

/-!
# Pay balanced inner-hinge cells before comparing radial periods

Every original label is kept. Within a close cell with the same actual
owner and second prime, the signed imbalance multiplies one actual
reference atom; the complete remaining variation has geometric source
cost. No opposite-parity partner, matching capacity, bin orthogonality or
bound on the signed imbalance is assumed. The same original supply debit
and every label outside the selected cells remain signed in the floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSignedCellFloor
open ZetaRieszInnerHingeTransport ZetaRieszInnerHingeGapPayment
open ZetaRieszFixedOwnerPairFloor ZetaRieszJointAllocation
open ZetaRieszPrimeEndpoint ZetaRieszOwnerMaximal ZetaRieszWideOwnerAudit
open ZetaRieszSmoothOwnerDiscrepancy

/-- A phase-coupled TOTAL-log cell. This is a partition of existing
labels, not a completion or a short-interval prime-count hypothesis. -/
def logCell (N n : ℕ) : ℤ := ⌊log n/exp (-(N : ℝ)/1000)⌋

/-- The actual deterministic partition supplies the required geometric
gap without assuming any prime distribution inside a cell. -/
theorem same_logCell_gap {N n n₀ : ℕ} (hc : logCell N n=logCell N n₀) :
    |log n-log n₀| ≤ exp (-(N : ℝ)/1000) := by
  let δ := exp (-(N : ℝ)/1000)
  have hδ : 0 < δ := exp_pos _
  have hn := Int.floor_le (log n/δ)
  have hn' := Int.lt_floor_add_one (log n/δ)
  have h₀ := Int.floor_le (log n₀/δ)
  have h₀' := Int.lt_floor_add_one (log n₀/δ)
  change ⌊log n/δ⌋=⌊log n₀/δ⌋ at hc
  rw [← hc] at h₀ h₀'
  have ha : |log n/δ-log n₀/δ| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
  rw [← sub_div,abs_div,abs_of_pos hδ] at ha
  exact ((div_lt_iff₀ hδ).mp ha).le.trans_eq (by ring)

private theorem moebius_norm_le (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  have h : |(μ n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using h

/-- The reference retains its own phase and coefficient. Either parity
is allowed: the only norm is on the coupled difference after both signs
have been retained. No matching or cofactor completion is used. -/
theorem unallocated_reference_gap {p q b b₀ : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hb : Squarefree b) (hb₀ : Squarefree b₀)
    (hc : 2 ≤ b.primeFactors.card) (hc₀ : 2 ≤ b₀.primeFactors.card)
    (hqb : ¬q ∣ b) (hqb₀ : ¬q ∣ b₀)
    (hpb : ¬p ∣ q*b) (hpb₀ : ¬p ∣ q*b₀) {L : ℝ} (hL : 1 ≤ L)
    (hi : InnerHinge L p q b) (hi₀ : InnerHinge L p q b₀)
    (N : ℕ) (y : ℝ) (hU : log (p*(q*b₀) : ℕ) ≤ 3*((N : ℝ)+1))
    (hgap : |log (p*(q*b) : ℕ)-log (p*(q*b₀) : ℕ)| ≤ 1) :
    ‖SquarefreeVaughanLogSource.coefficient L (p*(q*b))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b))-
      (μ b : ℂ)*(μ b₀ : ℂ)*
        (SquarefreeVaughanLogSource.coefficient L (p*(q*b₀))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b₀)))‖ ≤
      21*(1+|y|)*((N : ℝ)+1)*radialCap N*((p*(q*b) : ℕ) : ℝ)⁻¹*
        |log (p*(q*b) : ℕ)-log (p*(q*b₀) : ℕ)| := by
  rw [unallocated_inner_atom hp hq hb hc hqb hpb hi,
    unallocated_inner_atom hp hq hb₀ hc₀ hqb₀ hpb₀ hi₀]
  have hm : (μ b₀ : ℂ)^2=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hb₀
  have he (F G : ℂ) : (μ b : ℂ)*F-(μ b : ℂ)*(μ b₀ : ℂ)*((μ b₀ : ℂ)*G) =
      (μ b : ℂ)*(F-G) := by
    calc
      _ = (μ b : ℂ)*(F-(μ b₀ : ℂ)^2*G) := by ring
      _ = _ := by rw [hm]; ring
  rw [he,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (moebius_norm_le b)).trans
  have hlog : log (p*(q*b₀) : ℕ)=log p+log q+log b₀ := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast mul_ne_zero hq.ne_zero hb₀.ne_zero),
      Nat.cast_mul,log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hb₀.ne_zero)]
    ring
  have hcU : L+log q ≤ log (p*(q*b₀) : ℕ) := by
    have hτ := hi₀.2.2.1
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hb₀.ne_zero)] at hτ
    rw [hlog]
    linarith
  have hg := inner_kernel_unit_gap N hL (log_natCast_nonneg _) (log_natCast_nonneg _)
    (by linarith [log_natCast_nonneg q] : 0 ≤ L+log q) hcU hU hgap y
  have hnpos : (0 : ℝ)<(p*(q*b) : ℕ) := by
    exact_mod_cast mul_pos hp.pos (mul_pos hq.pos (Nat.pos_of_ne_zero hb.ne_zero))
  rw [exp_neg,exp_log hnpos] at hg
  exact hg

private theorem owner_atom_eq (A : Finset ℕ) (N n : ℕ) (L y : ℝ)
    (hs : Squarefree n) (hc : 3 ≤ n.primeFactors.card) (hA : largestPrime n ∈ A)
    (hln : 0 < log n) :
    residualCoefficient (A ∩ {largestPrime n}) L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      (ownerWeight N (1-log (largestPrime n)/log n) : ℂ)*
        (SquarefreeVaughanLogSource.coefficient L n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hb := ZetaRieszOwnerVariation.single_prime_share A N hs hc hp hA
  have hl : log (n/largestPrime n : ℕ)/log n=1-log (largestPrime n)/log n := by
    rw [Nat.cast_div hd (by exact_mod_cast hprime.ne_zero),
      log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hprime.ne_zero),
      sub_div,div_self hln.ne']
  rw [hl] at hb
  have hw : ownerWeight N (1-log (largestPrime n)/log n)=
      1-boundedShare (A ∩ {largestPrime n}) N n := by rw [hb]; rfl
  rw [hw]
  simp only [residualCoefficient]
  push_cast
  ring

/-- Every selected count shares one signed reference estimate. The
allocation difference is priced against the ACTUAL label, so references
may be reused without multiplying their norm by the cell cardinality. -/
theorem owner_reference_gap (A : Finset ℕ) {N n n₀ p q b b₀ : ℕ}
    (hN : 32 ≤ N) (hp : p.Prime) (hq : q.Prime)
    (hb : Squarefree b) (hb₀ : Squarefree b₀)
    (hc : 2 ≤ b.primeFactors.card) (hc₀ : 2 ≤ b₀.primeFactors.card)
    (hqb : ¬q ∣ b) (hqb₀ : ¬q ∣ b₀) (hpb : ¬p ∣ q*b) (hpb₀ : ¬p ∣ q*b₀)
    (hn : n=p*(q*b)) (hn₀ : n₀=p*(q*b₀))
    (hs : Squarefree n) (hs₀ : Squarefree n₀)
    (hcN : 3 ≤ n.primeFactors.card) (hcN₀ : 3 ≤ n₀.primeFactors.card)
    (howner : largestPrime n=p) (howner₀ : largestPrime n₀=p) (hA : p ∈ A)
    {L : ℝ} (hL : 1 ≤ L) (hi : InnerHinge L p q b) (hi₀ : InnerHinge L p q b₀)
    (y : ℝ) (hT : 1 ≤ log n) (hT₀ : 1 ≤ log n₀)
    (hU : log n₀ ≤ 3*((N : ℝ)+1)) (hgap : |log n-log n₀| ≤ 1) :
    ‖residualCoefficient (A ∩ {largestPrime n}) L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n-
      (μ b : ℂ)*(μ b₀ : ℂ)*
        (residualCoefficient (A ∩ {largestPrime n₀}) L N n₀*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n₀)‖ ≤
      21*(1+|y|)*((N : ℝ)+1)*radialCap N*(n : ℝ)⁻¹*|log n-log n₀|+
        2*((N : ℝ)+1)*|log n-log n₀| *
          ‖SquarefreeVaughanLogSource.coefficient L n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by
  have hpN : log p ≤ log n := by
    have hd : p ∣ n := hn ▸ dvd_mul_right p (q*b)
    exact log_le_log (by exact_mod_cast hp.pos)
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hd)
  have hpN₀ : log p ≤ log n₀ := by
    have hd : p ∣ n₀ := hn₀ ▸ dvd_mul_right p (q*b₀)
    exact log_le_log (by exact_mod_cast hp.pos)
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hs₀.ne_zero) hd)
  rw [owner_atom_eq A N n L y hs hcN (howner ▸ hA) (by linarith),
    owner_atom_eq A N n₀ L y hs₀ hcN₀ (howner₀ ▸ hA) (by linarith),howner,howner₀]
  let F := SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let G := (μ b : ℂ)*(μ b₀ : ℂ)*
    (SquarefreeVaughanLogSource.coefficient L n₀*zetaPrimeLogKernel N (3/2+Complex.I*y) n₀)
  have hh := fixed_owner_pair_norm hN (log_natCast_nonneg p) hT₀ hT hpN₀ hpN (-G) F
  have hg := unallocated_reference_gap hp hq hb hb₀ hc hc₀ hqb hqb₀ hpb hpb₀
    hL hi hi₀ N y (by simpa only [← hn₀] using hU)
    (by simpa only [← hn,← hn₀] using hgap)
  simp only [← hn,← hn₀] at hg
  have he' : ‖-G+F‖=‖F-G‖ := by congr 1; ring
  rw [he',abs_sub_comm (log n₀)] at hh
  calc
    _ = ‖(ownerWeight N (1-log p/log n₀) : ℂ)*(-G)+
        (ownerWeight N (1-log p/log n) : ℂ)*F‖ := by congr 1; dsimp [F,G]; ring
    _ ≤ _ := hh.trans (add_le_add hg le_rfl)

/-- Group by the ACTUAL cell after all counts and signs are summed.
The resulting imbalance stays complex-phase weighted; no adverse part,
norm or separate count price is taken. -/
theorem sum_cell_reference {ι : Type*} [DecidableEq ι] (S : Finset ℕ)
    (g : ℕ → ι) (sign : ℕ → ℂ) (reference : ι → ℂ) :
    (∑ n ∈ S,sign n*reference (g n)) =
      ∑ i ∈ S.image g,(∑ n ∈ S.filter (fun n => g n=i),sign n)*reference i := by
  have he := Finset.sum_fiberwise_of_maps_to (t := S.image g)
    (fun n hn => Finset.mem_image_of_mem g hn) (fun n => sign n*reference (g n))
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(Finset.mem_filter.mp hn).2]

/-- The whole zero-imbalance part of EVERY admitted cell is paid
geometrically. All counts may mix, references may repeat, and no partner
capacity assertion is needed. The signed cell imbalance is not estimated. -/
theorem global_owner_reference_error (A D : Finset ℕ) (c b : ℕ → ℕ)
    (hc : ∀ n ∈ D,c n ∈ D) {N : ℕ} (hN : 32 ≤ N) (Q : ℕ)
    (hQ : D ⊆ Finset.Icc 1 Q) (hlogQ : log Q ≤ 3*((N : ℝ)+1))
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (hD : D ⊆ literalWindow N)
    (hdata : ∀ n ∈ D,Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ largestPrime n ∈ A)
    (hgap : ∀ n ∈ D,|log n-log (c n)| ≤ exp (-(N : ℝ)/1000))
    (hgeom : ∀ n ∈ D,∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ Squarefree (b n) ∧ Squarefree (b (c n)) ∧
      2 ≤ (b n).primeFactors.card ∧ 2 ≤ (b (c n)).primeFactors.card ∧
      ¬q ∣ b n ∧ ¬q ∣ b (c n) ∧ ¬p ∣ q*b n ∧ ¬p ∣ q*b (c n) ∧
      n=p*(q*b n) ∧ c n=p*(q*b (c n)) ∧ largestPrime n=p ∧ largestPrime (c n)=p ∧
      InnerHinge L p q (b n) ∧ InnerHinge L p q (b (c n))) :
    u^(N+1)*(∑ n ∈ D,
      ‖residualCoefficient (A ∩ {largestPrime n}) L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n-
        (μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*
          (residualCoefficient (A ∩ {largestPrime (c n)}) L N (c n)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (c n))‖) ≤
      (168*radiusCeiling*(1+|y|)+
        2*radiusCeiling*zetaMoebiusLogMajorantMass (1+1/262144))*
          ((N : ℝ)+1)^3*exp (-(N : ℝ)/1250) := by
  let F := fun n => SquarefreeVaughanLogSource.coefficient L n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let O := fun n => residualCoefficient (A ∩ {largestPrime n}) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let C := 21*(1+|y|)*((N : ℝ)+1)*radialCap N*exp (-(N : ℝ)/1000)
  let δ := 2*((N : ℝ)+1)*exp (-(N : ℝ)/1000)
  have hRCap := radialCap_nonneg N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hη : exp (-(N : ℝ)/1000) ≤ 1 := exp_le_one_iff.mpr (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith)
  have hlow n (hn : n ∈ D) : 1 ≤ log n := by
    have ht := (mem_literalWindow N n).mp (hD hn)
    have hNr : (32 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hupper n (hn : n ∈ D) : log n ≤ 3*((N : ℝ)+1) := by
    have hd := Finset.mem_Icc.mp (hQ hn)
    exact (log_le_log (by exact_mod_cast hd.1) (by exact_mod_cast hd.2)).trans hlogQ
  have hp n (hn : n ∈ D) :
      ‖O n-(μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*O (c n)‖ ≤ C*(n : ℝ)⁻¹+δ*‖F n‖ := by
    obtain ⟨p,q,hp,hq,hb,hb₀,hbc,hbc₀,hqb,hqb₀,hpb,hpb₀,he,he₀,ho,ho₀,hi,hi₀⟩ := hgeom n hn
    obtain ⟨hs,hsC,hsA⟩ := hdata n hn
    obtain ⟨hs₀,hsC₀,_⟩ := hdata (c n) (hc n hn)
    have hh := owner_reference_gap A hN hp hq hb hb₀ hbc hbc₀ hqb hqb₀ hpb hpb₀
      he he₀ hs hs₀ hsC hsC₀ ho ho₀ (ho ▸ hsA) hL hi hi₀ y
      (hlow n hn) (hlow (c n) (hc n hn)) (hupper (c n) (hc n hn))
      ((hgap n hn).trans hη)
    change ‖O n-(μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*O (c n)‖ ≤ _ at hh
    apply hh.trans
    apply add_le_add
    · have h := mul_le_mul_of_nonneg_left (hgap n hn)
        (by positivity : 0 ≤ 21*(1+|y|)*((N : ℝ)+1)*radialCap N*(n : ℝ)⁻¹)
      exact h.trans_eq (by dsimp [C]; ring)
    · have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgap n hn) (by positivity : 0 ≤ 2*((N : ℝ)+1)))
        (norm_nonneg (F n))
      exact h
  have hsum : (∑ n ∈ D,‖O n-(μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*O (c n)‖) ≤
      C*(1+log Q)+δ*(∑ n ∈ D,‖F n‖) := by
    calc
      _ ≤ ∑ n ∈ D,(C*(n : ℝ)⁻¹+δ*‖F n‖) := Finset.sum_le_sum hp
      _ = C*(∑ n ∈ D,(n : ℝ)⁻¹)+δ*(∑ n ∈ D,‖F n‖) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left
          ((Finset.sum_le_sum_of_subset_of_nonneg hQ (by intros; positivity)).trans
            (by simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
              using harmonic_le_one_add_log Q)) hC) le_rfl
  have hcap : 1+log Q ≤ 4*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hraw : u^(N+1)*(C*(1+log Q)) ≤
      168*radiusCeiling*(1+|y|)*((N : ℝ)+1)^3*exp (-(N : ℝ)/1250) := by
    calc
      _ ≤ u^(N+1)*C*(4*((N : ℝ)+1)) := by
        have h := mul_le_mul_of_nonneg_left hcap (mul_nonneg (pow_nonneg hu (N+1)) hC)
        simpa only [mul_assoc] using h
      _ = (84*(1+|y|)*((N : ℝ)+1)^3)*
          (u^(N+1)*2^(N+1)*exp (-(N : ℝ)/1000)) := by dsimp [C,radialCap]; ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (small_gap_source_rate hu hU N)
          (by positivity : 0 ≤ 84*(1+|y|)*((N : ℝ)+1)^3)
        exact hh.trans_eq (by ring)
  have hvar := total_owner_gap_variation D (fun _ => 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by intros; norm_num) (by linarith : 0 < L) hu hU N y
  simp only [one_mul,mul_one] at hvar
  change u^(N+1)*δ*(∑ n ∈ D,‖F n‖) ≤ _ at hvar
  have hm : 0 ≤ zetaMoebiusLogMajorantMass (1+1/262144) :=
    tsum_nonneg (fun n => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
  have hr : 0 ≤ radiusCeiling := by norm_num [radiusCeiling]
  have hcub : ((N : ℝ)+1) ≤ ((N : ℝ)+1)^3 := by
    have hh : 0 ≤ (N : ℝ)*((N : ℝ)+1)*((N : ℝ)+2) := by positivity
    nlinarith only [hh]
  have hvarcap := mul_le_mul_of_nonneg_right hcub
    (by positivity : 0 ≤ 2*radiusCeiling*exp (-(N : ℝ)/1250)*
      zetaMoebiusLogMajorantMass (1+1/262144))
  change u^(N+1)*(∑ n ∈ D,‖O n-(μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*O (c n)‖) ≤ _
  have hs := mul_le_mul_of_nonneg_left hsum (pow_nonneg hu (N+1))
  calc
    _ ≤ 168*radiusCeiling*(1+|y|)*((N : ℝ)+1)^3*exp (-(N : ℝ)/1250)+
        2*radiusCeiling*((N : ℝ)+1)*exp (-(N : ℝ)/1250)*
          zetaMoebiusLogMajorantMass (1+1/262144) := by nlinarith only [hs,hraw,hvar]
    _ ≤ _ := by nlinarith only [hvarcap]

/-- Exact cell compression for the ORIGINAL fully allocated atoms,
including the single existing global nonowner payment. Only the balanced
variation is norm-priced; cell imbalance, remaining labels and funding
are left signed. All literal support and gap obligations remain. -/
theorem original_cell_error (A D : Finset ℕ) (c b : ℕ → ℕ)
    (hc : ∀ n ∈ D,c n ∈ D) {N : ℕ} (hN : 32 ≤ N) (Q : ℕ)
    (hQ : D ⊆ Finset.Icc 1 Q) (hlogQ : log Q ≤ 3*((N : ℝ)+1))
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (hD : D ⊆ literalWindow N)
    (hdata : ∀ n ∈ D,Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ largestPrime n ∈ A)
    (hgap : ∀ n ∈ D,|log n-log (c n)| ≤ exp (-(N : ℝ)/1000))
    (hgeom : ∀ n ∈ D,∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ Squarefree (b n) ∧ Squarefree (b (c n)) ∧
      2 ≤ (b n).primeFactors.card ∧ 2 ≤ (b (c n)).primeFactors.card ∧
      ¬q ∣ b n ∧ ¬q ∣ b (c n) ∧ ¬p ∣ q*b n ∧ ¬p ∣ q*b (c n) ∧
      n=p*(q*b n) ∧ c n=p*(q*b (c n)) ∧ largestPrime n=p ∧ largestPrime (c n)=p ∧
      InnerHinge L p q (b n) ∧ InnerHinge L p q (b (c n))) :
    ‖(u : ℂ)^(N+1)*((∑ n ∈ D,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
      ∑ n ∈ D,(μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*
        (residualCoefficient (A ∩ {largestPrime (c n)}) L N (c n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (c n)))‖ ≤
      ZetaRieszOpenCountFloor.matchingBudget N y := by
  let F := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let O := fun n => residualCoefficient (A ∩ {largestPrime n}) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let G := fun n => (μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*O (c n)
  have hcost := global_owner_reference_error A D c b hc hN Q hQ hlogQ hL hu hU
    y hD hdata hgap hgeom
  have howner : ‖(u : ℂ)^(N+1)*(∑ n ∈ D,(O n-G n))‖ ≤
      u^(N+1)*(∑ n ∈ D,‖O n-G n‖) := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hu (N+1))
  have hnon := ZetaRieszOwnerPairFloor.weighted_nonowner_error A D (fun _ => 1)
    (by norm_num : (0 : ℝ) < 1) (by intros; norm_num) (by linarith : 0 < L)
    N hD y hu hU
  simp only [one_mul] at hnon
  have he : (u : ℂ)^(N+1)*((∑ n ∈ D,F n)-∑ n ∈ D,G n) =
      (u : ℂ)^(N+1)*(∑ n ∈ D,(O n-G n))+
      (u : ℂ)^(N+1)*∑ n ∈ D,
        (residualCoefficient A L N n-residualCoefficient (A ∩ {largestPrime n}) L N n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    have hd : (∑ n ∈ D,
        (residualCoefficient A L N n-residualCoefficient (A ∩ {largestPrime n}) L N n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n) = (∑ n ∈ D,F n)-(∑ n ∈ D,O n) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      dsimp [F,O]
      ring
    rw [hd,Finset.sum_sub_distrib]
    ring
  change ‖(u : ℂ)^(N+1)*((∑ n ∈ D,F n)-∑ n ∈ D,G n)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (howner.trans hcost) hnon)

/-- Sum EVERY actual cofactor count in each cell before retaining its
phase-weighted imbalance. This finite identity spends no label twice. -/
theorem sum_cofactor_cells (D : Finset ℕ) (c b : ℕ → ℕ) (O : ℕ → ℂ) :
    (∑ n ∈ D,(μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*O (c n)) =
      ∑ i ∈ D.image c,
        (∑ n ∈ D.filter (fun n => c n=i),(μ (b n) : ℂ))*(μ (b i) : ℂ)*O i := by
  have h := sum_cell_reference D c (fun n => (μ (b n) : ℂ))
    (fun i => (μ (b i) : ℂ)*O i)
  simpa only [mul_assoc] using h

/-- A balanced cell contributes no reference channel at all, including
its full phase. Balance is the ACTUAL finite signed count, not a density
or an inference from the number of occupied prime-log bins. -/
theorem reference_zero_of_cell_balance (D : Finset ℕ) (c b : ℕ → ℕ) (O : ℕ → ℂ)
    (hbalance : ∀ i ∈ D.image c,
      (∑ n ∈ D.filter (fun n => c n=i),(μ (b n) : ℂ))=0) :
    (∑ n ∈ D,(μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*O (c n))=0 := by
  rw [sum_cofactor_cells]
  exact Finset.sum_eq_zero (fun i hi => by rw [hbalance i hi,zero_mul,zero_mul])

/-- Direct whole-floor inequality after paying all balanced cell
variation at once. The original signed imbalance, untouched support and
SAME supply debit remain joined. No matching existence or coverage
hypothesis is introduced, and no bound on the imbalance is claimed. -/
theorem floor_after_cells (A R Y D : Finset ℕ) (hDR : D ⊆ R) (c b : ℕ → ℕ)
    (hc : ∀ n ∈ D,c n ∈ D) {N : ℕ} (hN : 32 ≤ N) (Q K : ℕ)
    (hQ : D ⊆ Finset.Icc 1 Q) (hlogQ : log Q ≤ 3*((N : ℝ)+1))
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y debit err : ℝ) (hD : D ⊆ literalWindow N)
    (hdata : ∀ n ∈ D,Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ largestPrime n ∈ A)
    (hgap : ∀ n ∈ D,|log n-log (c n)| ≤ exp (-(N : ℝ)/1000))
    (hgeom : ∀ n ∈ D,∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ Squarefree (b n) ∧ Squarefree (b (c n)) ∧
      2 ≤ (b n).primeFactors.card ∧ 2 ≤ (b (c n)).primeFactors.card ∧
      ¬q ∣ b n ∧ ¬q ∣ b (c n) ∧ ¬p ∣ q*b n ∧ ¬p ∣ q*b (c n) ∧
      n=p*(q*b n) ∧ c n=p*(q*b (c n)) ∧ largestPrime n=p ∧ largestPrime (c n)=p ∧
      InnerHinge L p q (b n) ∧ InnerHinge L p q (b (c n)))
    (hfloor : u^(N+1)*((∑ n ∈ R,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      debit*(∑ n ∈ Y,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-err ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re) :
    u^(N+1)*(((∑ n ∈ R\D,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
      ∑ n ∈ D,(μ (b n) : ℂ)*(μ (b (c n)) : ℂ)*
        (residualCoefficient (A ∩ {largestPrime (c n)}) L N (c n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (c n))).re-
      debit*(∑ n ∈ Y,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-err-
      ZetaRieszOpenCountFloor.matchingBudget N y ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  have hb := original_cell_error A D c b hc hN Q hQ hlogQ hL hu hU
    y hD hdata hgap hgeom
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  have he (z : ℂ) : ((u : ℂ)^(N+1)*z).re=u^(N+1)*z.re := by
    rw [← Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [he,Complex.sub_re] at hr
  have hsum := Finset.sum_sdiff (f := fun n => residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n) hDR
  rw [← hsum] at hfloor
  simp only [Complex.add_re] at hfloor ⊢
  nlinarith only [hr,hfloor]

end RiemannGaussian.ZetaRieszSignedCellFloor
