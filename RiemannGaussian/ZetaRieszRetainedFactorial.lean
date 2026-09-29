/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAllocationVariation
import RiemannGaussian.ZetaRieszWeightedPrimeTail

/-!
# Positive factorial coefficients for the original unassigned carrier

The unused majority allocation is retained exactly before bounding the signed
prime/Riesz response. No order-zero or order-one mass is removed.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszRetainedFactorial
open ZetaRieszJointAllocation
open ZetaRieszWeightedPrimeTail

/-- The original allocation subtracts precisely the disjoint selected
majority incidences. The remaining full multinomial has a nonnegative
selector, with every original unpaid order and eligible prime retained. -/
theorem unassigned_multinomial (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hc : 3 ≤ n.primeFactors.card) :
    (1-boundedShare A N n)*Real.log n^(N+1) =
      ∑ d ∈ Finset.piAntidiag n.primeFactors (N+1),
        if ∀ p ∈ n.primeFactors.filter (· ∈ A), N+1-d p ∉ ZetaRieszWingHighOrders.unpaidOrders N
        then allocationWeight n.primeFactors (fun p : ℕ => Real.log p) d else 0 := by
  let S := n.primeFactors
  let I := S.filter (· ∈ A)
  let U := ZetaRieszWingHighOrders.unpaidOrders N
  let M := N+1
  let w := allocationWeight S (fun p : ℕ => Real.log p)
  have hM : (M.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
  have hn1 : 1 < n := by
    have hn0 := hn.ne_zero
    have hne : n ≠ 1 := by intro h; simp [h] at hc
    omega
  have hnp : ¬n.Prime := by intro hp; simp [hp.primeFactors] at hc
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hel p (hp : p ∈ S) : eligibleCofactor p (n/p) :=
    ZetaRieszMarkedSaturation.cofactor_data hn hc hp
  have hnorm : boundedShare A N n*Real.log n^M = assignedAmplitude A N n*M.factorial := by
    rw [boundedShare,if_pos ⟨hn,hn1,hnp⟩,allocationShare]
    dsimp [M]
    field_simp
  have hmarked p (hp : p ∈ S) :
      (∑ k ∈ U, Real.log (n/p : ℕ)^k/(k.factorial : ℝ)*
        (Real.log p^(M-k)/((M-k).factorial : ℝ)))*M.factorial =
        ∑ d ∈ (Finset.piAntidiag S M).filter (fun d => M-d p ∈ U), w d := by
    rw [marked_allocation S hp _ M U (fun k hk => by have := unpaid_orders_submajority N k hk; dsimp [M]; omega)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k ≤ M := by have := unpaid_orders_submajority N k hk; dsimp [M]; omega
    rw [factorial_split _ _ M k hkM,div_mul_cancel₀ _ hM,
      sum_log_erase_eq_log_cofactor hn hp]
  have hassigned : assignedAmplitude A N n*M.factorial =
      ∑ p ∈ I, ∑ d ∈ (Finset.piAntidiag S M).filter (fun d => M-d p ∈ U), w d := by
    rw [assignedAmplitude,Finset.sum_mul]
    change (∑ p ∈ S, (∑ k ∈ U, if p ∈ A ∧ eligibleCofactor p (n/p) then _ else 0)*
      (M.factorial : ℝ)) = _
    rw [show (∑ p ∈ I, ∑ d ∈ (Finset.piAntidiag S M).filter (fun d => M-d p ∈ U), w d) =
      ∑ p ∈ S, if p ∈ A then ∑ d ∈ (Finset.piAntidiag S M).filter (fun d => M-d p ∈ U), w d else 0
      from Finset.sum_filter _ _]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hel p hp,and_true]
    by_cases hpA : p ∈ A
    · simpa only [if_pos hpA] using hmarked p hp
    · simp only [if_neg hpA,Finset.sum_const_zero,zero_mul]
  have hfull : Real.log n^M = ∑ d ∈ Finset.piAntidiag S M, w d := by
    rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hn]
    exact Finset.sum_pow_eq_sum_piAntidiag S (fun p : ℕ => Real.log p) M
  have hp d (hd : d ∈ Finset.piAntidiag S M) :
      w d-(∑ p ∈ I, if M-d p ∈ U then w d else 0) =
        if ∀ p ∈ I, M-d p ∉ U then w d else 0 := by
    have hcard : (I.filter (fun p => M-d p ∈ U)).card ≤ 1 :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans
        (selected_card_le_one S U M (unpaid_orders_submajority N) hd)
    by_cases hnone : ∀ p ∈ I, M-d p ∉ U
    · rw [if_pos hnone,Finset.sum_eq_zero (fun p hp => if_neg (hnone p hp)),sub_zero]
    · have hnonempty : (I.filter (fun p => M-d p ∈ U)).Nonempty := by
        push Not at hnone
        obtain ⟨p,hp,hpu⟩ := hnone
        exact ⟨p,Finset.mem_filter.mpr ⟨hp,hpu⟩⟩
      have hcard1 : (I.filter (fun p => M-d p ∈ U)).card=1 := by
        have := Finset.card_pos.mpr hnonempty
        omega
      rw [if_neg hnone,← Finset.sum_filter,Finset.sum_const,hcard1]
      simp
  calc
    _ = Real.log n^M-assignedAmplitude A N n*M.factorial := by
      rw [sub_mul,one_mul,hnorm]
    _ = (∑ d ∈ Finset.piAntidiag S M, w d)-
        ∑ p ∈ I, ∑ d ∈ (Finset.piAntidiag S M).filter (fun d => M-d p ∈ U), w d := by
      rw [hfull,hassigned]
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm,← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hp

private theorem split_weight (S : Finset ℕ) {p : ℕ} (hp : p ∉ S)
    (x : ℕ → ℝ) {M j k : ℕ} (hjk : j+k=M) {d : ℕ → ℕ}
    (hd : d ∈ Finset.piAntidiag S k) :
    allocationWeight (S.cons p hp) x (d+fun q => if q=p then j else 0) =
      (M.choose j : ℝ)*x p^j*allocationWeight S x d := by
  have hdm := Finset.mem_piAntidiag.mp hd
  have hdp : d p=0 := by by_contra h; exact hp (hdm.2 p h)
  unfold allocationWeight
  rw [Nat.multinomial_cons,Finset.prod_cons]
  simp only [Pi.add_apply,if_true,hdp,zero_add]
  have hsum : (∑ q ∈ S, (d q+if q=p then j else 0))=k := by
    simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',hp,if_false,add_zero] using hdm.1
  have hm : Nat.multinomial S (d+fun q => if q=p then j else 0)=Nat.multinomial S d := by
    apply Nat.multinomial_congr
    intro q hq
    simp only [Pi.add_apply,if_neg (ne_of_mem_of_not_mem hq hp),add_zero]
  have hprod : (∏ q ∈ S, x q^(d q+if q=p then j else 0)) = ∏ q ∈ S, x q^d q := by
    apply Finset.prod_congr rfl
    intro q hq
    rw [if_neg (ne_of_mem_of_not_mem hq hp),add_zero]
  rw [hsum,hjk,hm,hprod,Nat.cast_mul]
  ring

private theorem retained_cons (S A U : Finset ℕ) {p : ℕ} (hp : p ∉ S) (hpA : p ∈ A)
    (x : ℕ → ℝ) (M : ℕ) :
    (∑ d ∈ Finset.piAntidiag (S.cons p hp) M,
      if ∀ q ∈ (S.cons p hp).filter (· ∈ A), M-d q ∉ U
      then allocationWeight (S.cons p hp) x d else 0) =
      ∑ j ∈ Finset.range (M+1), (M.choose j : ℝ)*x p^j*
        (if M-j ∉ U then ∑ d ∈ Finset.piAntidiag S (M-j),
          if ∀ q ∈ S.filter (· ∈ A), M-d q ∉ U then allocationWeight S x d else 0
          else 0) := by
  rw [Finset.piAntidiag_cons,Finset.sum_disjiUnion]
  have hpairs (b : ℕ×ℕ) (hb : b ∈ Finset.HasAntidiagonal.antidiagonal M) :
      (∑ d ∈ Finset.piAntidiag S b.2,
        if ∀ q ∈ (S.cons p hp).filter (· ∈ A),
          M-(d+fun q => if q=p then b.1 else 0) q ∉ U
        then allocationWeight (S.cons p hp) x (d+fun q => if q=p then b.1 else 0) else 0) =
      (M.choose b.1 : ℝ)*x p^b.1*
        (if M-b.1 ∉ U then ∑ d ∈ Finset.piAntidiag S b.2,
          if ∀ q ∈ S.filter (· ∈ A), M-d q ∉ U then allocationWeight S x d else 0 else 0) := by
    have hbM := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    by_cases hmark : M-b.1 ∉ U
    · rw [if_pos hmark,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdp : d p=0 := by
        by_contra h
        exact hp ((Finset.mem_piAntidiag.mp hd).2 p h)
      have he : (∀ q ∈ (S.cons p hp).filter (· ∈ A),
          M-(d+fun q => if q=p then b.1 else 0) q ∉ U) ↔
          (∀ q ∈ S.filter (· ∈ A), M-d q ∉ U) := by
        constructor
        · intro h q hq
          have hqs := (Finset.mem_filter.mp hq).1
          have hqA := (Finset.mem_filter.mp hq).2
          have hv := h q (Finset.mem_filter.mpr ⟨Finset.mem_cons.mpr (Or.inr hqs),hqA⟩)
          simpa only [Pi.add_apply,if_neg (ne_of_mem_of_not_mem hqs hp),add_zero] using hv
        · intro h q hq
          obtain ⟨hqS,hqA⟩ := Finset.mem_filter.mp hq
          rcases Finset.mem_cons.mp hqS with rfl | hqS
          · simpa only [Pi.add_apply,if_true,hdp,zero_add] using hmark
          · simpa only [Pi.add_apply,if_neg (ne_of_mem_of_not_mem hqS hp),add_zero] using
              h q (Finset.mem_filter.mpr ⟨hqS,hqA⟩)
      simp only [he]
      split_ifs
      · exact split_weight S hp x hbM hd
      · ring
    · rw [if_neg hmark,mul_zero]
      apply Finset.sum_eq_zero
      intro d hd
      apply if_neg
      intro h
      have hdp : d p=0 := by by_contra hn; exact hp ((Finset.mem_piAntidiag.mp hd).2 p hn)
      have hv := h p (Finset.mem_filter.mpr ⟨Finset.mem_cons.mpr (Or.inl rfl),hpA⟩)
      apply hmark
      simpa only [Pi.add_apply,if_true,hdp,zero_add] using hv
  simp only [Finset.sum_map,addRightEmbedding_apply]
  rw [Finset.sum_congr rfl hpairs,Finset.Nat.antidiagonal_eq_map,Finset.sum_map]
  rfl

/-- Fixing the marked prime order leaves nonnegative cofactor coefficients
bounded by the complete binomial coefficients. They are independent of the
marked prime, retain every eligible incidence, and keep orders zero and one. -/
theorem exists_retained_coefficients (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hc : 2 ≤ n.primeFactors.card) :
    ∃ B : ℕ → ℝ,
      (∀ j ≤ N+1, 0 ≤ B j ∧ B j ≤ ((N+1).choose j : ℝ)*Real.log n^(N+1-j)) ∧
      ∀ p : ℕ, p.Prime → p ∈ A → ¬p ∣ n →
        (1-boundedShare A N (p*n))*Real.log (p*n : ℕ)^(N+1) =
          ∑ j ∈ Finset.range (N+2), B j*Real.log p^j := by
  let S := n.primeFactors
  let U := ZetaRieszWingHighOrders.unpaidOrders N
  let M := N+1
  let C := fun j : ℕ => if M-j ∉ U then ∑ d ∈ Finset.piAntidiag S (M-j),
    if ∀ q ∈ S.filter (· ∈ A), M-d q ∉ U
      then allocationWeight S (fun q : ℕ => Real.log q) d else 0 else 0
  have hC j : 0 ≤ C j ∧ C j ≤ Real.log n^(M-j) := by
    have hlog := CoprimeEulerPhase.squarefree_log_eq_prime_sum hn
    have hfull : Real.log n^(M-j) =
        ∑ d ∈ Finset.piAntidiag S (M-j), allocationWeight S (fun q : ℕ => Real.log q) d := by
      rw [hlog]
      exact Finset.sum_pow_eq_sum_piAntidiag S _ _
    dsimp only [C]
    by_cases hmark : M-j ∉ U
    · rw [if_pos hmark]
      constructor
      · apply Finset.sum_nonneg
        intro d _
        have hw : 0 ≤ allocationWeight S (fun q : ℕ => Real.log q) d := by
          dsimp [allocationWeight]
          positivity
        split_ifs <;> positivity
      · rw [hfull]
        apply Finset.sum_le_sum
        intro d _
        split_ifs
        · rfl
        · dsimp [allocationWeight]; positivity
    · rw [if_neg hmark]
      exact ⟨le_rfl,pow_nonneg (Real.log_natCast_nonneg n) _⟩
  refine ⟨fun j => (M.choose j : ℝ)*C j,fun j _ =>
    ⟨mul_nonneg (Nat.cast_nonneg _) (hC j).1,
      mul_le_mul_of_nonneg_left (hC j).2 (Nat.cast_nonneg _)⟩,?_⟩
  intro p hp hpA hpn
  have hpS : p ∉ S := fun h => hpn (Nat.dvd_of_mem_primeFactors h)
  have hsf := Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hpn,hp.squarefree,hn⟩
  have hpf : (p*n).primeFactors = S.cons p hpS := by
    rw [Nat.primeFactors_mul hp.ne_zero hn.ne_zero,hp.primeFactors,Finset.singleton_union,
      Finset.cons_eq_insert]
  have hcnt : 3 ≤ (p*n).primeFactors.card := by rw [hpf,Finset.card_cons]; dsimp [S]; omega
  rw [unassigned_multinomial A N hsf hcnt,hpf]
  rw [retained_cons S A U hpS hpA (fun q : ℕ => Real.log q) M]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [C]
  ring

/-- Exact retained factorial expansion of an original real carrier atom.
The cofactor coefficients are independent of the marked prime, permitting
joint cancellation across several prime periods before taking a norm. -/
theorem atom_expansion (A : Finset ℕ) (N : ℕ) (L y : ℝ)
    {n p : ℕ} (hn : Squarefree n) (hc : 2 ≤ n.primeFactors.card)
    (hp : p.Prime) (hpn : ¬p ∣ n) (B : ℕ → ℝ)
    (hB : (1-boundedShare A N (p*n))*Real.log (p*n : ℕ)^(N+1) =
      ∑ j ∈ Finset.range (N+2), B j*Real.log p^j) :
    (residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2),
        (Real.exp (-Real.log n/2)*B j/(n : ℝ))*
        (factorialAmplitude j (Real.log p)*Real.cos (y*(Real.log p+Real.log n))/(p : ℝ))*
          (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-Real.log p) n)) := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬n.Prime := by intro h; simp [h.primeFactors] at hc
  have hmu : (ArithmeticFunction.moebius n : ℝ) = (-1 : ℝ)^n.primeFactors.card := by
    exact_mod_cast ZetaRieszReflectedLinear.moebius_eq_primeCount hn
  have hm2 : (ArithmeticFunction.moebius n : ℝ)^2=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  have hsign : (-1 : ℝ)^(n.primeFactors.card+1)*(-(ArithmeticFunction.moebius n : ℝ))=1 := by
    rw [pow_succ,← hmu]
    nlinarith only [hm2]
  have hlog : Real.log (p*n : ℕ)=Real.log p+Real.log n := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hn.ne_zero)]
  have hex : Real.exp (-(Real.log p+Real.log n)/2) =
      Real.exp (-Real.log p/2)*Real.exp (-Real.log n/2) := by
    rw [show -(Real.log p+Real.log n)/2 = -Real.log p/2+(-Real.log n/2) by ring,Real.exp_add]
  rw [ZetaRieszGlobalPrimePeriod.re_residual_atom hn hc hp hpn,
    ZetaRieszSquarefreeDualMean.response_reflection L (Real.log p) hn hn1 hnp]
  dsimp only [ZetaRieszGlobalPrimePeriod.signedPrimeWeight]
  have he :
      (-1 : ℝ)^(n.primeFactors.card+1)*(-(1/L))*(1-boundedShare A N (p*n))*
        (Real.exp (-(Real.log p+Real.log n)/2)*(Real.log p+Real.log n)^(N+1)/N.factorial)*
        (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log n))*
        (-(ArithmeticFunction.moebius n : ℝ)*
          (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-Real.log p) n))/(n : ℝ) =
      ((-1 : ℝ)^(n.primeFactors.card+1)*(-(ArithmeticFunction.moebius n : ℝ)))*
        (-1/(L*N.factorial))*Real.exp (-(Real.log p+Real.log n)/2)/(n : ℝ)*
          ((1-boundedShare A N (p*n))*Real.log (p*n : ℕ)^(N+1))*
          (Real.cos (y*(Real.log p+Real.log n))/(p : ℝ))*
          (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-Real.log p) n) := by
    rw [hlog]
    ring
  rw [he,hsign,one_mul,hB,hex]
  simp only [factorialAmplitude,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Both signed bounds for the ORIGINAL residual coefficient over a full
prime period. The entire factorial kernel and boundedShare allocation are
included, with all counts and orders and the correlated product phase. The
explicit order budget remains to be summed at source scale; arbitrary holes
inside the marked-prime period are not filled by this theorem. -/
theorem exists_literal_period_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Finset ℕ) (N M : ℕ) (S : Finset ℕ) (a y L : ℝ),
      1 ≤ M → 5000 ≤ a → 54 ≤ |y| → 0 < L → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let h := 2*Real.pi/|y|;
      let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+h)⌋₊).filter Nat.Prime;
      P ⊆ A → (∀ n ∈ S, ∀ p ∈ P, ¬p ∣ n) →
      let W := fun j : ℕ => Real.exp (-a/2)*(a+h)^j;
      let Q := fun j : ℕ => amplitudeEnergy a y (W j) (W j*factorialScore a h j);
      let J := (∑ n ∈ S, ∑ p ∈ P,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let K := Real.sqrt E/(L*N.factorial)*Real.exp (-Real.log M/2)*
        (∑ j ∈ Finset.range (N+2), ((N+1).choose j : ℝ)*Real.log (2*M : ℕ)^(N+1-j)*Real.sqrt (Q j));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_factorial_shell_bounds
  refine ⟨E,hE,fun A N M S a y L hM ha hy hL hS hSF => ?_⟩
  dsimp only
  let h := 2*Real.pi/|y|
  let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+h)⌋₊).filter Nat.Prime
  intro hPA hcop
  have hex n (hn : n ∈ S) := exists_retained_coefficients A N (hSF n hn).1 (hSF n hn).2
  choose B hcoef hid using hex
  let w := fun j n => if hn : n ∈ S then Real.exp (-Real.log n/2)*B n hn j/(n : ℝ) else 0
  let V := fun j => Real.exp (-Real.log M/2)*((N+1).choose j : ℝ)*Real.log (2*M : ℕ)^(N+1-j)
  let Q := fun j => amplitudeEnergy a y (Real.exp (-a/2)*(a+h)^j)
    ((Real.exp (-a/2)*(a+h)^j)*factorialScore a h j)
  have hw j (hj : j ∈ Finset.range (N+2)) n (hn : n ∈ S) : |w j n| ≤ V j/n := by
    have hjN : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
    have hMn := Finset.mem_Ioc.mp (hS hn)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : Real.log M ≤ Real.log n :=
      Real.log_le_log hM0 (by exact_mod_cast hMn.1.le)
    have hlog' : Real.log n ≤ Real.log (2*M : ℕ) :=
      Real.log_le_log hn0 (by exact_mod_cast hMn.2)
    have hb0 := (hcoef n hn j hjN).1
    have hb := (hcoef n hn j hjN).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_natCast_nonneg n) hlog' _) (Nat.cast_nonneg _))
    dsimp only [w,V]
    rw [dif_pos hn,abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ hn0.le
    simpa only [mul_assoc] using
      (mul_le_mul
        (Real.exp_le_exp.mpr (show -Real.log n/2 ≤ -Real.log M/2 by linarith))
        hb hb0 (Real.exp_pos (-Real.log M/2)).le)
  have hi n (hn : n ∈ S) :
      (∑ p ∈ P, residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
        (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2),
          w j n*weightedResponse (factorialAmplitude j) a y L (Real.log n) n) := by
    rw [Complex.re_sum]
    have he p (hp : p ∈ P) := atom_expansion A N L y (hSF n hn).1 (hSF n hn).2
      (Finset.mem_filter.mp hp).2 (hcop n hn p hp) (B n hn)
      (hid n hn p (Finset.mem_filter.mp hp).2 (hPA hp) (hcop n hn p hp))
    rw [Finset.sum_congr rfl he,← Finset.mul_sum,Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [weightedResponse,w]
    rw [dif_pos hn,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have htotal :
      (∑ n ∈ S, ∑ p ∈ P, residualCoefficient A L N (p*n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2),
        ∑ n ∈ S, w j n*weightedResponse (factorialAmplitude j) a y L (Real.log n) n) := by
    rw [Complex.re_sum,Finset.sum_congr rfl hi,← Finset.mul_sum,Finset.sum_comm]
  have hj j (hj : j ∈ Finset.range (N+2)) :
      |∑ n ∈ S, w j n*weightedResponse (factorialAmplitude j) a y L (Real.log n) n| ≤
        Real.sqrt E*V j*Real.sqrt (Q j) := by
    exact abs_le.mpr (hbound a y L (V j) j (fun n => Real.log n) (w j) M S ha hy
      (by dsimp [V]; positivity) hM hS (fun n hn => (hSF n hn).1) (hw j hj))
  have hsum := (Finset.abs_sum_le_sum_abs
    (fun j => ∑ n ∈ S, w j n*weightedResponse (factorialAmplitude j) a y L (Real.log n) n)
    (Finset.range (N+2))).trans (Finset.sum_le_sum hj)
  apply abs_le.mp
  rw [htotal,abs_mul,abs_div,abs_neg,abs_one,abs_of_pos (show 0 < L*(N.factorial : ℝ) by positivity)]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1/(L*(N.factorial : ℝ)))).trans_eq
  dsimp only [V]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Average the absolute factorial score before bounding it. The price is
the square root of the binomial variance, not the most extreme order. -/
theorem mean_absolute_score (m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ j ∈ Finset.range (m+1), mass m j x*|(j : ℝ)-m*x|) ≤
      Real.sqrt ((m : ℝ)*x*(1-x)) := by
  have hm j := mass_nonneg m j hx hx1
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m+1))
    (fun j => Real.sqrt (mass m j x))
    (fun j => Real.sqrt (mass m j x)*|(j : ℝ)-m*x|)
  have he j : Real.sqrt (mass m j x)*(Real.sqrt (mass m j x)*|(j : ℝ)-m*x|) =
      mass m j x*|(j : ℝ)-m*x| := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hm j)]
  simp_rw [he,mul_pow,Real.sq_sqrt (hm _),sq_abs] at hc
  rw [mass_total,one_mul] at hc
  have hv : (∑ j ∈ Finset.range (m+1), mass m j x*((j : ℝ)-m*x)^2) =
      (m : ℝ)*x*(1-x) := by
    convert ZetaRieszAllocationVariation.mass_variance m x using 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hv] at hc
  exact (le_abs_self _).trans (Real.abs_le_sqrt hc)

/-- All factorial orders, including zero and one, pay one averaged saddle
score. The last term is a uniform within-period derivative error. -/
theorem mean_factorialScore (m : ℕ) {a h x : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ j ∈ Finset.range (m+1), mass m j x*factorialScore a h j) ≤
      Real.sqrt ((m : ℝ)*x*(1-x))/a+|(m : ℝ)*x/a-1/2|+m*h/a^2 := by
  have hj j (hj : j ∈ Finset.range (m+1)) :
      factorialScore a h j ≤ |(j : ℝ)-m*x|/a+|(m : ℝ)*x/a-1/2|+m*h/a^2 := by
    have hja : (j : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hab := abs_add_le (((j : ℝ)-m*x)/a) ((m : ℝ)*x/a-1/2)
    have he : ((j : ℝ)-m*x)/a+((m : ℝ)*x/a-1/2) = j/a-1/2 := by ring
    rw [he,abs_div,abs_of_pos ha] at hab
    exact add_le_add hab (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hja hh) (sq_nonneg a))
  calc
    _ ≤ ∑ j ∈ Finset.range (m+1), mass m j x*
        (|(j : ℝ)-m*x|/a+|(m : ℝ)*x/a-1/2|+m*h/a^2) :=
      Finset.sum_le_sum (fun j hj' => mul_le_mul_of_nonneg_left (hj j hj') (mass_nonneg m j hx hx1))
    _ = (∑ j ∈ Finset.range (m+1), mass m j x*|(j : ℝ)-m*x|)/a+
        |(m : ℝ)*x/a-1/2|+m*h/a^2 := by
      simp_rw [mul_add,← mul_div_assoc]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp only [← Finset.sum_div,← Finset.sum_mul,mass_total,one_mul]
    _ ≤ _ := add_le_add (add_le_add
      (div_le_div_of_nonneg_right (mean_absolute_score m hx hx1) ha.le) le_rfl) le_rfl

/-- Linearize only the explicit numerical energy budget, after the signed
prime tail and both hinges have been evaluated together. -/
theorem sqrt_amplitudeEnergy_le {a y W s : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W) (hs : 0 ≤ s) :
    let h := 2*Real.pi/|y|;
    let B := 2/(|y| *a)+4/a^2;
    Real.sqrt (amplitudeEnergy a y W (W*s)) ≤
      W*((Real.sqrt a*(4/a^2)+Real.sqrt h*B)+
        ((Real.sqrt a+Real.sqrt h)*h*B)*s) := by
  dsimp only
  let h := 2*Real.pi/|y|
  let B := 2/(|y| *a)+4/a^2
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  have he : amplitudeEnergy a y W (W*s) =
      (W*Real.sqrt a*(4/a^2+s*h*B))^2+(W*Real.sqrt h*(1+s*h)*B)^2 := by
    change a*(W*(4/a^2)+W*s*h*B)^2+h*((W+W*s*h)*B)^2 = _
    simp only [mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hh]
    ring
  rw [he]
  have hp : 0 ≤ (W*Real.sqrt a*(4/a^2+s*h*B))*(W*Real.sqrt h*(1+s*h)*B) := by positivity
  change (W*Real.sqrt a*(4/a^2+s*h*B))^2+(W*Real.sqrt h*(1+s*h)*B)^2 ≤
    (W*((Real.sqrt a*(4/a^2)+Real.sqrt h*B)+((Real.sqrt a+Real.sqrt h)*h*B)*s))^2
  nlinarith only [hp]

private theorem binomial_reweight (m j : ℕ) (hj : j ≤ m) {t b : ℝ} (ht : 0 < t) (hb : 0 ≤ b) :
    ((m.choose j : ℝ)*b^(m-j))*t^j = (t+b)^m*mass m j (t/(t+b)) := by
  have hT : t+b ≠ 0 := ne_of_gt (by positivity)
  have he : 1-t/(t+b)=b/(t+b) := by field_simp; ring
  dsimp only [mass]
  rw [he,div_pow,div_pow,div_mul_div_comm,← pow_add,Nat.add_sub_of_le hj]
  field_simp

/-- Sum the entire factorial-order budget explicitly. Binomial variance
retains the radial saddle saving with no order-count or maximum-score loss. -/
theorem factorial_order_budget (m : ℕ) {a b y : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    let h := 2*Real.pi/|y|;
    let t := a+h;
    let x := t/(t+b);
    let B := 2/(|y| *a)+4/a^2;
    let W := fun j : ℕ => Real.exp (-a/2)*t^j;
    (∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)*b^(m-j)*
      Real.sqrt (amplitudeEnergy a y (W j) (W j*factorialScore a h j))) ≤
      Real.exp (-a/2)*(t+b)^m*((Real.sqrt a*(4/a^2)+Real.sqrt h*B)+
        ((Real.sqrt a+Real.sqrt h)*h*B)*
          (Real.sqrt ((m : ℝ)*x*(1-x))/a+|(m : ℝ)*x/a-1/2|+m*h/a^2)) := by
  dsimp only
  let h := 2*Real.pi/|y|
  let t := a+h
  let x := t/(t+b)
  let B := 2/(|y| *a)+4/a^2
  let C := Real.sqrt a*(4/a^2)+Real.sqrt h*B
  let D := (Real.sqrt a+Real.sqrt h)*h*B
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by dsimp [x]; exact (div_le_one (by positivity)).mpr (by linarith)
  have hD : 0 ≤ D := by dsimp [D,B]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)*b^(m-j)*
        (Real.exp (-a/2)*t^j)*(C+D*factorialScore a h j) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [C,D,B,t,h,mul_assoc] using mul_le_mul_of_nonneg_left
        (sqrt_amplitudeEnergy_le (y := y) ha.le (by positivity : 0 ≤ Real.exp (-a/2)*t^j)
          (by dsimp [factorialScore]; positivity : 0 ≤ factorialScore a h j))
        (by positivity : 0 ≤ (m.choose j : ℝ)*b^(m-j))
    _ = Real.exp (-a/2)*(t+b)^m*
        (C+D*(∑ j ∈ Finset.range (m+1), mass m j x*factorialScore a h j)) := by
      have he j (hj : j ∈ Finset.range (m+1)) :
          (m.choose j : ℝ)*b^(m-j)*(Real.exp (-a/2)*t^j) =
          (Real.exp (-a/2)*(t+b)^m)*mass m j x := by
        have hr := binomial_reweight m j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) ht hb
        dsimp only [x]
        linear_combination Real.exp (-a/2)*hr
      simp_rw [Finset.sum_congr rfl (fun j hj => congrArg (·*(C+D*factorialScore a h j)) (he j hj))]
      simp_rw [mul_assoc (Real.exp (-a/2)*(t+b)^m)]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,mass_total,one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (mean_factorialScore m ha hh hx hx1) hD))
      (by positivity)

/-- Explicit cost after summing every factorial order. It has no residual
prime, divisor, cofactor or allocation sum; the global period sum remains. -/
def summedPeriodCost (N M : ℕ) (a y L : ℝ) : ℝ :=
  let m := N+1
  let h := 2*Real.pi/|y|
  let b := Real.log (2*M : ℕ)
  let T := a+h+b
  let x := (a+h)/T
  let B := 2/(|y| *a)+4/a^2
  let C := Real.sqrt a*(4/a^2)+Real.sqrt h*B
  let D := (Real.sqrt a+Real.sqrt h)*h*B
  (1/(L*N.factorial))*Real.exp (-Real.log M/2)*Real.exp (-a/2)*T^m*
    (C+D*(Real.sqrt ((m : ℝ)*x*(1-x))/a+|(m : ℝ)*x/a-1/2|+m*h/a^2))

/-- The original retained carrier on a complete ordinary-prime period has
both signed bounds with its entire factorial-order budget evaluated. Every
allocation, both Riesz hinges and the exact product phase remain literal. -/
theorem exists_literal_summed_period_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Finset ℕ) (N M : ℕ) (S : Finset ℕ) (a y L : ℝ),
      1 ≤ M → 5000 ≤ a → 54 ≤ |y| → 0 < L → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime;
      P ⊆ A → (∀ n ∈ S, ∀ p ∈ P, ¬p ∣ n) →
      let J := (∑ n ∈ S, ∑ p ∈ P,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      -(Real.sqrt E*summedPeriodCost N M a y L) ≤ J ∧
        J ≤ Real.sqrt E*summedPeriodCost N M a y L := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_period_bounds
  refine ⟨E,hE,fun A N M S a y L hM ha hy hL hS hSF hPA hcop => ?_⟩
  have hb := hbound A N M S a y L hM ha hy hL hS hSF hPA hcop
  have ho := factorial_order_budget (N+1) (y := y) (by linarith : 0 < a)
    (Real.log_natCast_nonneg (2*M))
  have hc := mul_le_mul_of_nonneg_left ho
    (by positivity : 0 ≤ Real.sqrt E/(L*(N.factorial : ℝ))*Real.exp (-Real.log M/2))
  have he : Real.sqrt E/(L*(N.factorial : ℝ))*Real.exp (-Real.log M/2)*
      (Real.exp (-a/2)*(a+2*Real.pi/|y|+Real.log (2*M : ℕ))^(N+1)*
        ((Real.sqrt a*(4/a^2)+Real.sqrt (2*Real.pi/|y|)*(2/(|y| *a)+4/a^2))+
          ((Real.sqrt a+Real.sqrt (2*Real.pi/|y|))*(2*Real.pi/|y|)*(2/(|y| *a)+4/a^2))*
            (Real.sqrt (((N+1 : ℕ) : ℝ)*((a+2*Real.pi/|y|)/(a+2*Real.pi/|y|+Real.log (2*M : ℕ)))*
              (1-(a+2*Real.pi/|y|)/(a+2*Real.pi/|y|+Real.log (2*M : ℕ))))/a+
              |((N+1 : ℕ) : ℝ)*((a+2*Real.pi/|y|)/(a+2*Real.pi/|y|+Real.log (2*M : ℕ)))/a-1/2|+
              ((N+1 : ℕ) : ℝ)*(2*Real.pi/|y|)/a^2))) =
        Real.sqrt E*summedPeriodCost N M a y L := by
    dsimp only [summedPeriodCost]
    ring
  rw [he] at hc
  exact ⟨(neg_le_neg hc).trans hb.1,hb.2.trans hc⟩

/-- Arbitrary finite radial and share families of complete prime periods
share one constant. Their actual scalar costs are summed, without a maximum
prime count, factorial order or extra family-cardinality multiplier. -/
theorem exists_literal_family_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (A : Finset ℕ) (N : ℕ)
      (M : ℕ → ℕ) (S : ℕ → Finset ℕ) (a : ℕ → ℝ) (y L : ℝ),
      54 ≤ |y| → 0 < L →
      (∀ i ∈ I, 1 ≤ M i) → (∀ i ∈ I, 5000 ≤ a i) →
      (∀ i ∈ I, S i ⊆ Finset.Ioc (M i) (2*M i)) →
      (∀ i ∈ I, ∀ n ∈ S i, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let P := fun i => (Finset.Ioc ⌊Real.exp (a i)⌋₊
        ⌊Real.exp (a i+2*Real.pi/|y|)⌋₊).filter Nat.Prime;
      (∀ i ∈ I, P i ⊆ A) →
      (∀ i ∈ I, ∀ n ∈ S i, ∀ p ∈ P i, ¬p ∣ n) →
      let J := (∑ i ∈ I, ∑ n ∈ S i, ∑ p ∈ P i,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let K := Real.sqrt E*(∑ i ∈ I, summedPeriodCost N (M i) (a i) y L);
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_summed_period_bounds
  refine ⟨E,hE,fun I A N M S a y L hy hL hM ha hS hSF hPA hcop => ?_⟩
  dsimp only
  rw [Complex.re_sum]
  have hi i (hi : i ∈ I) := hbound A N (M i) (S i) (a i) y L
    (hM i hi) (ha i hi) hy hL (hS i hi) (hSF i hi) (hPA i hi) (hcop i hi)
  constructor
  · have hh := Finset.sum_le_sum (fun i hi' => (hi i hi').1)
    simpa only [Finset.sum_neg_distrib,← Finset.mul_sum] using hh
  · have hh := Finset.sum_le_sum (fun i hi' => (hi i hi').2)
    simpa only [← Finset.mul_sum] using hh

end RiemannGaussian.ZetaRieszRetainedFactorial
