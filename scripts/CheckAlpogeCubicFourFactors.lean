import CheckAlpogeCubicRough

/-! # Removing products of four large factors from the cubic window -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real ZetaVaughanReduction
open scoped Classical Pointwise ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
  ArithmeticFunction.Omega

/-- A factorization into four integers strictly larger than the cutoff. -/
def HasFourLargeFactors (n p : ℕ) : Prop :=
  ∃ a b c d : ℕ, n<a ∧ n<b ∧ n<c ∧ n<d ∧ a*b*c*d=p

/-- Each factor lies in the short interval directly above the cutoff. -/
private theorem factor_le_of_four {n k a b c d : ℕ} (hn : 0 < n)
    (hb : n ≤ b) (hc : n ≤ c) (hd : n ≤ d) (h : a*b*c*d ≤ (n+k)*n^3) :
    a ≤ n+k := by
  apply Nat.le_of_mul_le_mul_right _ (pow_pos hn 3)
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left a hb) hc) hd
  exact (show a*n^3=a*n*n*n by ring).le.trans (hprod.trans h)

/-- There are at most the fourth power of the averaging depth many such
integers in the full support, counting each product only once. -/
theorem card_fourLargeFactors {n : ℕ} (hn : 0 < n) :
    ((Icc 0 (cubicSampleEnd n)).filter (HasFourLargeFactors n)).card ≤ (Nat.log 2 n+1)^4 := by
  classical
  let k := Nat.log 2 n+1
  let J := Ioc n (n+k)
  have hs : (Icc 0 (cubicSampleEnd n)).filter (HasFourLargeFactors n) ⊆ J^4 := by
    intro p hp
    obtain ⟨hp,⟨a,b,c,d,ha,hb,hc,hd,he⟩⟩ := mem_filter.mp hp
    have h := (mem_Icc.mp hp).2
    rw [← he,show cubicSampleEnd n=(n+k)*n^3 by unfold cubicSampleEnd; dsimp [k]; ring] at h
    have memJ (x y z w : ℕ) (hx : n<x) (hy : n<y) (hz : n<z) (hw : n<w)
        (heq : x*y*z*w=a*b*c*d) : x ∈ J :=
      mem_Ioc.mpr ⟨hx,factor_le_of_four hn hy.le hz.le hw.le (heq.le.trans h)⟩
    rw [← he,show J^4=J*J*J*J by simp only [pow_succ,pow_zero,one_mul]]
    exact mul_mem_mul (mul_mem_mul (mul_mem_mul (memJ a b c d ha hb hc hd rfl)
      (memJ b a c d hb ha hc hd (by ring))) (memJ c a b d hc ha hb hd (by ring)))
      (memJ d a b c hd ha hb hc (by ring))
  calc
    _ ≤ (J^4).card := card_le_card hs
    _ ≤ J.card^4 := card_pow_le
    _ = _ := by simp [J,k]

theorem abs_truncatedMoebiusSum_le (n t : ℕ) : |truncatedMoebiusSum n t| ≤ n := by
  rw [truncatedMoebiusSum_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _d ∈ t.divisors.filter (· ≤ n), (1:ℝ) := sum_le_sum fun d _ => by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ ≤ ∑ _d ∈ Ioc 0 n, (1:ℝ) := sum_le_sum_of_subset_of_nonneg (fun d hd =>
      mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1,(mem_filter.mp hd).2⟩)
      (fun _ _ _ => zero_le_one)
    _ = _ := by simp

/-- A common bound on the truncated Möbius sums of divisors bounds the full coefficient. -/
private theorem cubicRoughCoefficient_le_of_divisors (n p : ℕ) {B : ℝ} (hB : 0≤B)
    (hL : ∀ d : ℕ, d ∣ p → |truncatedMoebiusSum n d| ≤ B) :
    |cubicRoughCoefficient n p| ≤ (1+2*B)*log p := by
  have hΛ : |Λ p - head n Λ p| ≤ log p := by
    by_cases hp : p ≤ n
    · simp [head,hp, log_natCast_nonneg]
    · simpa [head,hp,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
        (ArithmeticFunction.vonMangoldt_le_log (n := p))
  have hrough : 0 ≤ roughPrimeLog n p := sum_nonneg fun v _ => by
    split_ifs <;> positivity [ArithmeticFunction.vonMangoldt_nonneg (n := v)]
  have hlog : roughPrimeLog n p ≤ log p := by
    rw [roughPrimeLog,← ArithmeticFunction.vonMangoldt_sum]
    exact sum_le_sum fun v _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  have hmain : |truncatedMoebiusSum n p * roughPrimeLog n p| ≤ B*log p := by
    rw [abs_mul,abs_of_nonneg hrough]
    exact mul_le_mul (hL p dvd_rfl) hlog hrough hB
  unfold cubicRoughCoefficient
  apply (abs_sub _ _).trans
  apply (add_le_add (d := B*log p) ((abs_sub _ _).trans (add_le_add hΛ hmain)) _).trans_eq
  · ring
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ v ∈ p.divisors, Λ v * B := by
      apply sum_le_sum
      intro v hv
      split_ifs
      · rw [abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_left (hL _ (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hv))) ArithmeticFunction.vonMangoldt_nonneg
      · simp only [abs_zero]
        positivity [ArithmeticFunction.vonMangoldt_nonneg (n := v)]
    _ = _ := by rw [← sum_mul,ArithmeticFunction.vonMangoldt_sum]; ring

/-- The coefficient grows at most linearly in the divisor cutoff, uniformly
in the tested integer apart from its single logarithm. -/
theorem abs_cubicRoughCoefficient_le (n p : ℕ) :
    |cubicRoughCoefficient n p| ≤ (1+2*(n:ℝ))*log p :=
  cubicRoughCoefficient_le_of_divisors n p (Nat.cast_nonneg _) (fun d _ => abs_truncatedMoebiusSum_le n d)

/-- The same bound with divisor count in place of the sieve cutoff is
summable over a long prefix by counting divisors in the other order. -/
theorem abs_cubicRoughCoefficient_le_divisors {p : ℕ} (hp : 0<p) (n : ℕ) :
    |cubicRoughCoefficient n p| ≤ (1+2*(p.divisors.card:ℝ))*log p := by
  apply cubicRoughCoefficient_le_of_divisors n p (Nat.cast_nonneg _)
  intro d hd
  rw [truncatedMoebiusSum_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _v ∈ d.divisors.filter (· ≤ n), (1:ℝ) := sum_le_sum fun v _ => by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := v)
    _ ≤ ∑ _v ∈ p.divisors, (1:ℝ) := sum_le_sum_of_subset_of_nonneg
      ((filter_subset ..).trans (Nat.divisors_subset_of_dvd hp.ne' hd)) (fun _ _ _ => zero_le_one)
    _ = _ := by simp

/-- Retain the truncated coefficient only on integers which cannot be split
into four factors above the cutoff. -/
def cubicThreeFactorCoefficient (n p : ℕ) : ℝ :=
  if HasFourLargeFactors n p then 0 else cubicRoughCoefficient n p

private theorem rough_gt_cutoff {n r : ℕ} (hr : 1 < r) (hc : r.Coprime n.factorial) : n < r := by
  by_contra! h
  have he := Nat.eq_one_of_dvd_coprimes hc dvd_rfl (Nat.dvd_factorial (by omega : 0<r) h)
  omega

private theorem peel_rough_prime {n r : ℕ} (hc : r.Coprime n.factorial) (hΩ : 0 < Ω r) :
    ∃ q t : ℕ, n<q ∧ t.Coprime n.factorial ∧ Ω r = 1+Ω t ∧ r=q*t := by
  have hr := ArithmeticFunction.cardFactors_pos_iff_one_lt.mp hΩ
  obtain ⟨q,hq,t,he⟩ := Nat.exists_prime_and_dvd (by omega : r ≠ 1)
  have ht : t ≠ 0 := by rintro rfl; simp at he; omega
  have hq' := hc.of_dvd_left (show q ∣ r from ⟨t,he⟩)
  refine ⟨q,t,rough_gt_cutoff hq.one_lt hq',hc.of_dvd_left (he ▸ dvd_mul_left t q),?_,he⟩
  rw [he,ArithmeticFunction.cardFactors_mul hq.ne_zero ht,ArithmeticFunction.cardFactors_apply_prime hq]

private theorem fourLargeFactors_of_mixed {n s r : ℕ} (hs : n < s)
    (hc : r.Coprime n.factorial) (hΩ : 3 ≤ Ω r) : HasFourLargeFactors n (s*r) := by
  obtain ⟨a,t,ha,ht,h1,he⟩ := peel_rough_prime hc (by omega)
  obtain ⟨b,c,hb,hc',h2,hf⟩ := peel_rough_prime ht (by omega)
  have hc1 := ArithmeticFunction.cardFactors_pos_iff_one_lt.mp (show 0 < Ω c by omega)
  refine ⟨s,a,b,c,hs,ha,hb,rough_gt_cutoff hc1 hc',?_⟩
  rw [he,hf]
  ring

theorem fourLargeFactors_iff_cardFactors_of_rough {n r : ℕ} (hn : 1 ≤ n)
    (hc : r.Coprime n.factorial) : HasFourLargeFactors n r ↔ 4 ≤ Ω r := by
  constructor
  · rintro ⟨a,b,c,d,ha,hb,hc',hd,rfl⟩
    have hpos {x : ℕ} (hx : n<x) : 0 < Ω x :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (hn.trans_lt hx)
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hc0 : c ≠ 0 := by omega
    have hd0 : d ≠ 0 := by omega
    rw [ArithmeticFunction.cardFactors_mul (mul_ne_zero (mul_ne_zero ha0 hb0) hc0) hd0,
      ArithmeticFunction.cardFactors_mul (mul_ne_zero ha0 hb0) hc0,
      ArithmeticFunction.cardFactors_mul ha0 hb0]
    have := hpos ha
    have := hpos hb
    have := hpos hc'
    have := hpos hd
    omega
  · intro hΩ
    obtain ⟨q,t,hq,ht,he,rfl⟩ := peel_rough_prime hc (by omega)
    exact fourLargeFactors_of_mixed hq ht (by omega)

/-- On the rough integers only semiprimes and products of three primes carry
weight, counting repeated prime factors with multiplicity. -/
theorem cubicThreeFactorCoefficient_rough_eq {n r : ℕ} (hn : 1 ≤ n) (hr : n < r)
    (hc : r.Coprime n.factorial) :
    cubicThreeFactorCoefficient n r = if Ω r=2 ∨ Ω r=3 then Λ r-log r else 0 := by
  have he := cubicRoughCoefficient_eq_on_rough_progression (n := n) (s := 1)
    (by decide) (hn.trans (Nat.le_self_pow (by decide : 3 ≠ 0) n)) hc
  rw [one_mul] at he
  rw [cubicThreeFactorCoefficient,fourLargeFactors_iff_cardFactors_of_rough hn hc,he,
    bilinear_rough_eq hn hr (fun d hd => Nat.Coprime.of_dvd_left
      (Nat.dvd_factorial (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2) hc.symm)]
  have hΩ := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (hn.trans_lt hr)
  by_cases h4 : 4 ≤ Ω r
  · have h23 : ¬(Ω r=2 ∨ Ω r=3) := by omega
    simp [h4,h23]
  by_cases h23 : Ω r=2 ∨ Ω r=3
  · simp [h4,h23]
  have hp := ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (show Ω r=1 by omega)
  simp [h4,h23,ArithmeticFunction.vonMangoldt_apply_prime hp]

theorem cubicThreeFactorCoefficient_rough_neg_iff {n r : ℕ} (hn : 1 ≤ n) (hr : n < r)
    (hc : r.Coprime n.factorial) : cubicThreeFactorCoefficient n r < 0 ↔ Ω r=2 ∨ Ω r=3 := by
  rw [cubicThreeFactorCoefficient_rough_eq hn hr hc]
  by_cases h : Ω r=2 ∨ Ω r=3
  · rw [ite_eq_left h]
    refine ⟨fun _ => h,fun _ => sub_neg.mpr ?_⟩
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs
    · apply log_lt_log (Nat.cast_pos.mpr (Nat.minFac_pos _))
      exact_mod_cast (Nat.not_prime_iff_minFac_lt (by omega : 2 ≤ r)).mp
        (fun hp => by have := ArithmeticFunction.cardFactors_apply_prime hp; omega)
    · exact log_pos (by exact_mod_cast hn.trans_lt hr)
  · simp [h]

/-- Given any base greater than one, a rough cofactor with at least three
prime factors makes the retained coefficient zero. -/
theorem cubicThreeFactorCoefficient_mixed_zero {n s r : ℕ} (hs : 1 < s)
    (hc : r.Coprime n.factorial) (hΩ : 3 ≤ Ω r) : cubicThreeFactorCoefficient n (s*r) = 0 := by
  by_cases hsn : s ≤ n
  · have he := cubicRoughCoefficient_eq_on_rough_progression (by omega : 0<s)
      (hsn.trans (Nat.le_self_pow (by decide : 3 ≠ 0) n)) hc
    rw [cubicThreeFactorCoefficient,he,bilinear_mixed_eq_zero hs hsn (fun d hd =>
      Nat.Coprime.of_dvd_left (Nat.dvd_factorial (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2) hc.symm)]
    simp
  · exact ite_eq_left (fourLargeFactors_of_mixed (lt_of_not_ge hsn) hc hΩ)

private theorem bilinear_zero_of_no_pair {n s : ℕ}
    (h : ∀ d k : ℕ, d*k=s → n<d → k ≤ n) : bilinear n n s = 0 := by
  rw [bilinear_eq]
  apply sum_eq_zero
  intro x hx
  by_cases hd : n<x.1
  · have hk := h x.1 x.2 (Nat.mem_divisorsAntidiagonal.mp hx).1 hd
    have hz : cofactor n x.2 = 0 := by
      rw [cofactor_eq]
      apply sum_eq_zero
      intro d hv
      obtain ⟨hdv,hk0⟩ := Nat.mem_divisors.mp hv
      exact ite_eq_right (not_lt.mpr ((Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdv).trans hk))
    simp [hd,hz]
  · exact ite_eq_right hd

/-- With two large factors in the rough cofactor, the base contributes no
bilinear term anywhere in the full averaging support. -/
theorem cubicThreeFactorCoefficient_two_large_cofactor {n s a b : ℕ} (hn : 8 ≤ n) (hs : 0<s)
    (ha : n<a) (hb : n<b) (hc : (a*b).Coprime n.factorial)
    (hsize : s*(a*b) ≤ cubicSampleEnd n) :
    cubicThreeFactorCoefficient n (s*(a*b)) =
      if HasFourLargeFactors n (s*(a*b)) then 0 else
        (Λ (s*(a*b))-head n Λ (s*(a*b))) - (Λ s-head n Λ s) - truncatedMoebiusSum n s*log (a*b) := by
  unfold cubicThreeFactorCoefficient
  by_cases h4 : HasFourLargeFactors n (s*(a*b))
  · simp [h4]
  rw [ite_eq_right h4,ite_eq_right h4]
  have hs2 : s ≤ 2*n^2 := by
    apply Nat.le_of_mul_le_mul_right _ (by positivity : 0<n^2)
    have hp : n^2 ≤ a*b := (pow_two n).le.trans (Nat.mul_le_mul ha.le hb.le)
    exact (Nat.mul_le_mul_left s hp).trans ((hsize.trans (cubicSampleEnd_le hn)).trans_eq (by ring))
  have hs3 : s ≤ n^3 := hs2.trans ((Nat.mul_le_mul_right (n^2) (by omega : 2 ≤ n)).trans_eq (by ring))
  rw [cubicRoughCoefficient_eq_on_rough_progression hs hs3 hc,bilinear_mul_rough hs
    (Nat.mul_pos ((Nat.zero_le _).trans_lt ha) ((Nat.zero_le _).trans_lt hb)) hc]
  have hz : bilinear n n s = 0 := by
    apply bilinear_zero_of_no_pair
    intro d k he hd
    by_contra! hk
    exact h4 ⟨d,k,a,b,hd,hk,ha,hb,by rw [he]; ring⟩
  rw [hz,zero_add,Nat.cast_mul]

/-- The unsigned loss on rough semiprimes and products of three primes. -/
def roughCompositeLoss (n r : ℕ) : ℝ :=
  if r.Coprime n.factorial ∧ (Ω r=2 ∨ Ω r=3) then log r-Λ r else 0

/-- The rest of the coefficient is supported on integers with a small prime divisor. -/
def cubicSmallPrimeCoefficient (n p : ℕ) : ℝ :=
  if p.Coprime n.factorial then 0 else cubicThreeFactorCoefficient n p

private theorem threeFactorCoefficient_split {n : ℕ} (hn : 1 ≤ n) :
    cubicThreeFactorCoefficient n = cubicSmallPrimeCoefficient n - roughCompositeLoss n := by
  funext p
  change cubicThreeFactorCoefficient n p = cubicSmallPrimeCoefficient n p - roughCompositeLoss n p
  by_cases hc : p.Coprime n.factorial
  · by_cases hp : n<p
    · rw [cubicSmallPrimeCoefficient,ite_eq_left hc,roughCompositeLoss,
        cubicThreeFactorCoefficient_rough_eq hn hp hc]
      by_cases hΩ : Ω p=2 ∨ Ω p=3
      · rw [ite_eq_left hΩ,ite_eq_left (And.intro hc hΩ)]
        ring
      · rw [ite_eq_right hΩ,ite_eq_right (fun h => hΩ h.2),sub_zero]
    have hz : p=0 ∨ p=1 := by
      by_cases h0 : p=0
      · exact Or.inl h0
      exact Or.inr (Nat.eq_one_of_dvd_coprimes hc dvd_rfl
        (Nat.dvd_factorial (Nat.pos_of_ne_zero h0) (Nat.le_of_not_gt hp)))
    have hΩ := ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mpr hz
    rw [cubicSmallPrimeCoefficient,ite_eq_left hc,roughCompositeLoss,
      ite_eq_right (fun h => by omega : ¬(p.Coprime n.factorial ∧ (Ω p=2 ∨ Ω p=3))),
      sub_zero,cubicThreeFactorCoefficient]
    split_ifs
    · rfl
    rcases hz with rfl | rfl
    · simp [cubicRoughCoefficient,head]
    · simp [cubicRoughCoefficient,roughPrimeLog,head,hn]
  · simp [cubicSmallPrimeCoefficient,roughCompositeLoss,hc]

theorem cubicWeightedResponse_roughCompositeLoss_nonneg (n : ℕ) :
    0 ≤ cubicWeightedResponse n (roughCompositeLoss n) := by
  have hl (p : ℕ) : 0 ≤ roughCompositeLoss n p := by
    unfold roughCompositeLoss
    split_ifs
    · exact sub_nonneg.mpr ArithmeticFunction.vonMangoldt_le_log
    · exact le_rfl
  unfold cubicWeightedResponse
  apply add_nonneg (div_nonneg (sum_nonneg fun p _ => hl p) (by norm_num))
  let f := fun M => ∑ p ∈ Ioc (3*n^3) M, roughCompositeLoss n p*weight M p
  let k := Nat.log 2 n+1
  let W := 2*n^3+1
  let A := n^4-k*n^3
  change 0 ≤ repeatedMean W k f A
  rw [← repeat_const (by dsimp [W]; omega : 0 < W) k A 0]
  exact repeat_mono W k A fun M _ _ => sum_nonneg fun p hp => mul_nonneg (hl p)
    (weight_mem (N := M) ((Nat.zero_le _).trans_lt (mem_Ioc.mp hp).1)).1

/-- Uniform control of the contribution omitted from a fourth-power sample. -/
theorem fourFactorResponse_bound {n : ℕ} (hn : 8 ≤ n) :
    |cubicWeightedResponse n (cubicRoughCoefficient n) -
        cubicWeightedResponse n (cubicThreeFactorCoefficient n)| ≤
      2*((Nat.log 2 n+1:ℕ):ℝ)^4*((1+2*(n:ℝ))*log (cubicSampleEnd n)) := by
  let S := (Icc 0 (cubicSampleEnd n)).filter (HasFourLargeFactors n)
  let B := (1+2*(n:ℝ))*log (cubicSampleEnd n)
  have hB : 0 ≤ B := mul_nonneg (by positivity) (log_natCast_nonneg _)
  rw [cubicWeightedResponse_sub]
  apply (cubicWeightedResponse_abs hn _).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = ∑ p ∈ S, |cubicRoughCoefficient n p| := by
      unfold S
      rw [sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases hp : HasFourLargeFactors n p <;> simp [cubicThreeFactorCoefficient,hp]
    _ ≤ ∑ _p ∈ S, B := by
      apply sum_le_sum
      intro p hp
      apply (abs_cubicRoughCoefficient_le n p).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hle := (mem_Icc.mp (mem_filter.mp hp).1).2
      by_cases hz : p=0
      · simpa [hz] using log_natCast_nonneg (cubicSampleEnd n)
      exact log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hle)
    _ = (S.card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_fourLargeFactors (by omega : 0<n)) hB

/-- After window normalization the entire four-factor contribution is bounded
by a convergent three-halves power series. -/
theorem fourFactorResponse_normalized {n : ℕ} (hn : 8 ≤ n) :
    |cubicWeightedResponse n (cubicRoughCoefficient n) -
        cubicWeightedResponse n (cubicThreeFactorCoefficient n)|/(n:ℝ)^3 ≤
      (264*21^4:ℝ)*(n:ℝ)^(-(3/2):ℝ) := by
  let t := (n:ℝ)^(1/10:ℝ)
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : 0 < (n:ℝ) := zero_lt_one.trans_le hn1
  have ht : 1 ≤ t := one_le_rpow hn1 (by norm_num)
  have hlog : log n ≤ 10*t := by
    simpa [t,div_eq_mul_inv,mul_comm] using log_natCast_le_rpow_div n (by norm_num : (0:ℝ)<1/10)
  have h2 : (1/2:ℝ) ≤ log 2 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [log_inv] at h
    linarith only [h]
  have hk : ((Nat.log 2 n+1:ℕ):ℝ) ≤ 21*t := by
    have h := natLog_le_logb n 2
    rw [← log_div_log] at h
    have hh := (le_div_iff₀ (by linarith only [h2] : 0 < log (2:ℝ))).mp h
    push_cast
    nlinarith only [hh,hlog,ht,mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))]
  have hEnd : 0 < cubicSampleEnd n := by unfold cubicSampleEnd; positivity
  have hE := log_le_log (Nat.cast_pos.mpr hEnd)
    (show (cubicSampleEnd n:ℝ) ≤ (2:ℝ)*(n:ℝ)^4 by exact_mod_cast cubicSampleEnd_le hn)
  rw [log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),log_pow,Nat.cast_ofNat] at hE
  have hE' : log (cubicSampleEnd n) ≤ 44*t := by
    linarith only [hE,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),hlog,ht]
  have hweight := mul_le_mul (show 1+2*(n:ℝ) ≤ 3*n by linarith only [hn1]) hE'
    (log_natCast_nonneg _) (by positivity)
  have hfull := mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hk 4)
    (by norm_num : (0:ℝ) ≤ 2)) hweight
    (by positivity [log_natCast_nonneg (cubicSampleEnd n)]) (by positivity [ht])
  have hpow : (n:ℝ)*t^5 = (n:ℝ)^((3/2):ℝ) := by
    calc
      _ = (n:ℝ)^(1:ℝ)*(n:ℝ)^((1/10:ℝ)*(5:ℕ)) := by
        rw [rpow_one,rpow_mul_natCast (Nat.cast_nonneg _)]
      _ = _ := by rw [← rpow_add hn0]; norm_num
  have hscale : (n:ℝ)^(-(3/2):ℝ)*(n:ℝ)^3=(n:ℝ)^((3/2):ℝ) := by
    rw [← rpow_add_natCast hn0.ne']; norm_num
  apply (div_le_iff₀ (pow_pos hn0 3)).mpr
  rw [mul_assoc,hscale,← hpow]
  exact (fourFactorResponse_bound hn).trans (hfull.trans_eq (by ring))

/-- Positive deficit after removing every product of four large factors. -/
def cubicThreeFactorMassOn (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (cubicSmoothMoments n -
    cubicWeightedResponse n (cubicThreeFactorCoefficient n)) 0 / (n:ℝ)^3

/-- The small-prime response must compensate the explicit nonnegative rough
loss as well as the two smooth moments. The sign is fixed before truncation. -/
theorem cubicThreeFactorMassOn_eq_smallPrime {m b : ℕ} (hm : 1 ≤ m) :
    cubicThreeFactorMassOn m b = ∑ n ∈ Icc m b, max
      (cubicSmoothMoments n + cubicWeightedResponse n (roughCompositeLoss n) -
        cubicWeightedResponse n (cubicSmallPrimeCoefficient n)) 0 / (n:ℝ)^3 := by
  unfold cubicThreeFactorMassOn
  apply sum_congr rfl
  intro n hn
  rw [threeFactorCoefficient_split (hm.trans (mem_Icc.mp hn).1),← cubicWeightedResponse_sub]
  ring_nf

private def fourFactorMajorant (n : ℕ) := (264*21^4:ℝ)*(n:ℝ)^(-(3/2):ℝ)

private theorem fourFactorMajorant_summable : Summable fourFactorMajorant :=
  (summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ) < -1)).mul_left _

private theorem fourFactorMajorant_nonneg (n : ℕ) : 0 ≤ fourFactorMajorant n := by
  unfold fourFactorMajorant
  positivity

/-- The error on every interval with left endpoint m is bounded by the tail
of the same convergent series, independently of the right endpoint. -/
theorem cubicThreeFactorMassOn_error {m b : ℕ} (hm : 8 ≤ m) :
    |cubicRoughMassOn m b-cubicThreeFactorMassOn m b| ≤
      (∑' n : ℕ, (264*21^4:ℝ)*(n:ℝ)^(-(3/2):ℝ)) -
      ∑ n ∈ range m, (264*21^4:ℝ)*(n:ℝ)^(-(3/2):ℝ) := by
  unfold cubicRoughMassOn cubicThreeFactorMassOn
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc m b, fourFactorMajorant n := by
      apply sum_le_sum
      intro n hn
      have h := abs_max_sub_max_le_abs
        (cubicSmoothMoments n-cubicWeightedResponse n (cubicRoughCoefficient n))
        (cubicSmoothMoments n-cubicWeightedResponse n (cubicThreeFactorCoefficient n)) 0
      rw [show ∀ a b c : ℝ, (a-b)-(a-c)=c-b by intros; ring,abs_sub_comm
        (cubicWeightedResponse n (cubicThreeFactorCoefficient n))] at h
      rw [← sub_div,abs_div,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3)]
      exact (div_le_div_of_nonneg_right h (by positivity)).trans
        (fourFactorResponse_normalized (hm.trans (mem_Icc.mp hn).1))
    _ ≤ _ := by
      have hd : Disjoint (range m) (Icc m b) := disjoint_left.mpr fun n hn hm =>
        (not_le.mpr (mem_range.mp hn)) (mem_Icc.mp hm).1
      have h := fourFactorMajorant_summable.sum_le_tsum (range m ∪ Icc m b)
        (fun n _ => fourFactorMajorant_nonneg n)
      rw [sum_union hd] at h
      change _ ≤ (∑' n, fourFactorMajorant n) - ∑ n ∈ range m, fourFactorMajorant n
      linarith only [h]

theorem cubicThreeFactorMassOn_error_vanishes {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ, ∀ m ≥ A, ∀ b : ℕ, |cubicRoughMassOn m b-cubicThreeFactorMassOn m b| < ε := by
  have h := fourFactorMajorant_summable.hasSum.tendsto_sum_nat
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.mp (h.eventually (lt_mem_nhds
    (sub_lt_self (∑' n, fourFactorMajorant n) hε)))
  refine ⟨max 8 A,fun m hm b => ?_⟩
  apply (cubicThreeFactorMassOn_error (by omega : 8 ≤ m)).trans_lt
  change (∑' n, fourFactorMajorant n) - ∑ n ∈ range m, fourFactorMajorant n < ε
  have hb : (∑' n, fourFactorMajorant n)-ε < ∑ n ∈ range m, fourFactorMajorant n :=
    hA m (by omega)
  linarith only [hb]

/-- The window criterion now needs only products that admit no splitting into
four factors above the divisor cutoff. -/
theorem rh_of_cubicThreeFactorMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicThreeFactorMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicRoughMassOn_powerWindows
  let K := ∑' n, fourFactorMajorant n
  have hK : 0 ≤ K := tsum_nonneg fourFactorMajorant_nonneg
  apply subpowerWindows_of_log_cube_error hK _ h
  intro m b hm
  have hb : 1 ≤ (1+log b)^3 := one_le_pow₀ (by linarith only [log_natCast_nonneg b])
  have he := (abs_le.mp (cubicThreeFactorMassOn_error (b := b) hm)).2
  change _ ≤ K-∑ n ∈ range m, fourFactorMajorant n at he
  linarith only [he,sum_nonneg (s := range m) (fun n _ => fourFactorMajorant_nonneg n),
    mul_le_mul_of_nonneg_left hb hK]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.card_fourLargeFactors,
      ``RiemannGaussian.AlpogeMined.cubicThreeFactorCoefficient_rough_neg_iff,
      ``RiemannGaussian.AlpogeMined.cubicThreeFactorCoefficient_mixed_zero,
      ``RiemannGaussian.AlpogeMined.cubicThreeFactorCoefficient_two_large_cofactor,
      ``RiemannGaussian.AlpogeMined.cubicThreeFactorMassOn_eq_smallPrime,
      ``RiemannGaussian.AlpogeMined.cubicThreeFactorMassOn_error_vanishes,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicThreeFactorMassOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
