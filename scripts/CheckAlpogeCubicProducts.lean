import CheckAlpogeCubicVaughan

/-! # The large-factor product sum through three cubic cutoffs -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real ZetaVaughanReduction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta

/-- The product coefficient before summing over its positive multiples. -/
def vaughanPair (n : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ) - head n μ) * (Λ - head n Λ)

/-- The absolute coefficient at a fixed product is at most its logarithm. -/
theorem abs_vaughanPair_le_log (n e : ℕ) : |vaughanPair n e| ≤ log e := by
  rw [vaughanPair, ArithmeticFunction.mul_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a ∈ e.divisorsAntidiagonal, Λ a.2 := by
      apply sum_le_sum
      intro a _
      change |((μ a.1 : ℝ) - head n μ a.1)*(Λ a.2 - head n Λ a.2)| ≤ Λ a.2
      have hμ : |(μ a.1:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      by_cases hd : a.1 ≤ n <;> by_cases hv : a.2 ≤ n <;>
        simp [head, hd, hv, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          ArithmeticFunction.vonMangoldt_nonneg]
      exact (mul_le_mul_of_nonneg_right hμ ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ v => Λ v),
        ← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.vonMangoldt_mul_zeta,
        ArithmeticFunction.log_apply]

private theorem bilinear_eq_strides {p X : ℕ} (hpX : p ≤ X) (n : ℕ) :
    bilinear n n p = ∑ e ∈ Ioc 0 X, vaughanPair n e * strideUnit e p := by
  by_cases hp : p = 0
  · simp [hp, strideUnit]
  have heq : bilinear n n = vaughanPair n * ζ := by
    simp only [bilinear, cofactor, vaughanPair, mul_assoc]
  rw [heq, ArithmeticFunction.coe_mul_zeta_apply]
  have hset : p.divisors = (Ioc 0 X).filter (fun e => e ∣ p) := by
    ext e
    simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨he, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos he (Nat.pos_of_ne_zero hp),
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hp) he).trans hpX⟩, he⟩
    · exact fun h => ⟨h.2, hp⟩
  rw [hset, sum_filter]
  apply sum_congr rfl
  intro e he
  by_cases hd : e ∣ p
  · have hq := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hp) hd) (mem_Ioc.mp he).1
    simp [strideUnit, hd, hq.ne']
  · simp [strideUnit, hd]

/-- A uniform bound for the unsigned mass of the full large-factor coefficient. -/
theorem bilinear_prefix_abs_le (n X : ℕ) :
    ∑ p ∈ Icc 0 X, |bilinear n n p| ≤ (X:ℝ)*log X*(1+log X) := by
  calc
    _ ≤ ∑ p ∈ Icc 0 X, ∑ e ∈ Ioc 0 X, log X * strideUnit e p := by
      apply sum_le_sum
      intro p hp
      rw [bilinear_eq_strides (mem_Icc.mp hp).2 n]
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro e he
      have hs : 0 ≤ strideUnit e p := by unfold strideUnit; split_ifs <;> norm_num
      rw [abs_mul, abs_of_nonneg hs]
      apply mul_le_mul_of_nonneg_right _ hs
      exact (abs_vaughanPair_le_log n e).trans (log_le_log
        (Nat.cast_pos.mpr (mem_Ioc.mp he).1) (by exact_mod_cast (mem_Ioc.mp he).2))
    _ = ∑ e ∈ Ioc 0 X, log X * ((X/e:ℕ):ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      rw [← mul_sum]
      congr 1
      have h := strideUnit_prefix (mem_Ioc.mp he).1 (X:ℝ)
      simpa only [coefficientPrefix, Nat.floor_natCast, Nat.floor_div_natCast] using h
    _ ≤ ∑ e ∈ Ioc 0 X, ((X:ℝ)*log X)*(e:ℝ)⁻¹ := by
      apply sum_le_sum
      intro e _
      exact (mul_le_mul_of_nonneg_left Nat.cast_div_le (log_natCast_nonneg X)).trans_eq (by ring)
    _ ≤ _ := by
      rw [← mul_sum, show Ioc 0 X = Icc 1 X by ext e; simp only [mem_Ioc, mem_Icc]; omega]
      exact mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (by decide : 1 ≤ 1))
        (mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _))

/-- A complete period or its complement gives a half-contraction for
every denominator up to three cubic cutoffs. -/
theorem cubicMean_weight_half {n p : ℕ} (hn : 1 ≤ n) (hp : n^3 ≤ p) (hp3 : p ≤ 3*n^3) :
    |cubicMean n (fun M => weight M p) - 1/2| ≤ 2/(n:ℝ) := by
  let D := n^3
  let W := 2*D+1
  let k := Nat.log 2 n+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hW : 0 < W := by dsimp [W]; omega
  have hp0 := hD.trans_le hp
  have hrem : min (W%p) (p-W%p) ≤ D := by
    change p ≤ 3*D at hp3
    by_cases h : W < p
    · rw [Nat.mod_eq_of_lt h]
      exact (min_le_right _ _).trans (by dsimp [W]; omega)
    · have hr := Nat.mod_lt W hp0
      dsimp only [W] at h
      omega
  have hratio : (((min (W%p) (p-W%p):ℕ):ℝ)/W) ≤ 1/2 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hW)).mpr
    have hr : ((min (W%p) (p-W%p):ℕ):ℝ) ≤ (D:ℝ) := by exact_mod_cast hrem
    apply hr.trans
    dsimp only [W]
    push_cast
    linarith
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hpow : (1/2:ℝ)^k ≤ 1/(n:ℝ) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le hn0
      (by exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le)
  have hsmall : 1/(2*(p:ℝ)) ≤ 1/(n:ℝ) := by
    have hp1 : n ≤ p := (Nat.le_self_pow (by decide : 3 ≠ 0) n).trans hp
    apply one_div_le_one_div_of_le hn0
    have hpR : (n:ℝ) ≤ p := by exact_mod_cast hp1
    linarith only [hpR, Nat.cast_nonneg (α := ℝ) p]
  have hrow := repeated_weight_residue_error hp0 hW k (n^4-k*D)
  change |cubicMean n (fun M => weight M p) - (1/2+1/(2*(p:ℝ)))| ≤ _ at hrow
  have hh := hrow.trans ((pow_le_pow_left₀ (by positivity) hratio k).trans hpow)
  calc
    _ = |(cubicMean n (fun M => weight M p)-(1/2+1/(2*(p:ℝ))))+1/(2*(p:ℝ))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by
      rw [abs_of_nonneg (by positivity : 0 ≤ 1/(2*(p:ℝ)))]
      exact (add_le_add hh hsmall).trans_eq (by ring))

private theorem cubicMean_triple_congr {n : ℕ} (hn : 8 ≤ n) {f g : ℕ → ℝ}
    (h : ∀ M ≥ 3*n^3, f M = g M) : cubicMean n f = cubicMean n g := by
  let k := Nat.log 2 n+1
  have hk : 2*k ≤ n := (cubic_tail_parameters hn).1
  have hA : 3*n^3 ≤ n^4-k*n^3 := by
    rw [show n^4=n*n^3 by ring, ← Nat.sub_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  change repeatedMean (2*n^3+1) k f (n^4-k*n^3) = repeatedMean (2*n^3+1) k g (n^4-k*n^3)
  apply le_antisymm <;> apply repeat_mono <;> intro M hm _
  · exact (h M (hA.trans hm)).le
  · exact (h M (hA.trans hm)).ge

private theorem weightedCoefficient_split {D R M : ℕ} (hDR : D ≤ R) (hRM : R ≤ M)
    (c : ℕ → ℝ) : weightedCoefficient M D c =
      (∑ p ∈ Icc 0 R, c p * weight M (max D p)) + ∑ p ∈ Ioc R M, c p*weight M p := by
  have hl : (∑ p ∈ Icc 0 R, c p*weight M (max D p)) =
      weight M D * coefficientPrefix c D + ∑ p ∈ Ioc D R, c p*weight M p := by
    have hset : Icc 0 R = Icc 0 D ∪ Ioc D R := by ext p; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hset, sum_union (disjoint_left.mpr fun p hp hq =>
      (not_lt_of_ge (mem_Icc.mp hp).2) (mem_Ioc.mp hq).1)]
    unfold coefficientPrefix
    rw [Nat.floor_natCast, mul_sum]
    congr 1
    · apply sum_congr rfl
      intro p hp
      rw [max_eq_left (mem_Icc.mp hp).2, mul_comm]
    · apply sum_congr rfl
      intro p hp
      rw [max_eq_right (mem_Ioc.mp hp).1.le]
  rw [hl, add_assoc, Finset.sum_Ioc_consecutive (f := fun p : ℕ => c p*weight M p) hDR hRM]
  rfl

/-- Half weight through three cubic cutoffs, followed by the moving upper sum. -/
def cubicWeightedResponse (n : ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑ p ∈ Icc 0 (3*n^3), c p)/2 +
    cubicMean n (fun M => ∑ p ∈ Ioc (3*n^3) M, c p*weight M p)

/-- The product coefficient through three cutoffs has constant half weight.
All larger products retain the original moving reciprocal weight. -/
def cubicProductResponse (n : ℕ) : ℝ :=
  cubicWeightedResponse n (bilinear n n)

/-- Every nonzero pair has both factors strictly above n. -/
theorem vaughanPair_eq_zero {n e : ℕ} (he : e < (n+1)^2) : vaughanPair n e = 0 := by
  rw [vaughanPair, ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro a ha
  have hp := (Nat.mem_divisorsAntidiagonal.mp ha).1
  change ((μ a.1:ℝ)-head n μ a.1)*(Λ a.2-head n Λ a.2)=0
  by_cases hd : a.1 ≤ n
  · simp [head, hd]
  · have hv : a.2 ≤ n := by
      by_contra! h
      have hb := Nat.mul_le_mul (by omega : n+1 ≤ a.1) (by omega : n+1 ≤ a.2)
      rw [← pow_two, hp] at hb
      omega
    simp [head, hv]

private theorem sum_bilinear_products (X n : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Icc 0 X, bilinear n n p * f p =
      ∑ e ∈ Ioc 0 X, vaughanPair n e * ∑ k ∈ Ioc 0 (X/e), f (e*k) := by
  calc
    _ = ∑ p ∈ Icc 0 X, ∑ e ∈ Ioc 0 X, vaughanPair n e * (strideUnit e p*f p) := by
      apply sum_congr rfl
      intro p hp
      rw [bilinear_eq_strides (mem_Icc.mp hp).2 n, sum_mul]
      simp only [mul_assoc]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      rw [← mul_sum]
      congr 1
      have h (p : ℕ) : strideUnit e p * f p =
          if e ∣ p then (if p/e=0 then 0 else f (e*(p/e))) else 0 := by
        by_cases hdiv : e ∣ p
        · simp only [strideUnit, ite_eq_left hdiv, Nat.mul_div_cancel' hdiv]
          split_ifs <;> simp
        · simp [strideUnit, hdiv]
      simp_rw [h]
      rw [← sum_filter, sum_stride (fun k => if k=0 then 0 else f (e*k)) X (mem_Ioc.mp he).1,
        ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le (X/e))]
      simp only [ite_true, zero_add]
      apply sum_congr rfl
      intro k hk
      rw [ite_eq_right (mem_Ioc.mp hk).1.ne']

private theorem weighted_bilinear_upper_products (M R n : ℕ) :
    ∑ p ∈ Ioc R M, bilinear n n p*weight M p =
      ∑ e ∈ Ioc 0 M, vaughanPair n e *
        ∑ k ∈ Ioc (R/e) (M/e), weight M (e*k) := by
  let f (p : ℕ) := if R < p then weight M p else 0
  have hs : ∑ p ∈ Icc 0 M, bilinear n n p*f p = ∑ p ∈ Ioc R M, bilinear n n p*weight M p := by
    simp only [f, mul_ite, mul_zero, ← sum_filter]
    congr 1
    ext p
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [← hs, sum_bilinear_products]
  apply sum_congr rfl
  intro e he
  congr 1
  unfold f
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_Ioc]
  have he0 := (mem_Ioc.mp he).1
  have hdiv : R/e < k ↔ R < e*k := by rw [Nat.div_lt_iff_lt_mul he0, Nat.mul_comm k e]
  rw [← hdiv]
  exact ⟨fun h => ⟨h.2,h.1.2⟩,
    fun h => ⟨⟨(Nat.zero_le (R/e)).trans_lt h.1,h.2⟩,h.1⟩⟩

private theorem moebius_tail_on_mixed {n s u : ℕ} (hs : 1 < s) (hsn : s ≤ n) (hu : 0 < u)
    (hr : ∀ d ∈ Ioc 0 n, d.Coprime u) :
    (((μ : ArithmeticFunction ℝ)-head n μ)*ζ) (s*u) = 0 := by
  have hs0 : 0 < s := by omega
  have hsu := Nat.mul_pos hs0 hu
  have hsune : s*u ≠ 1 := by
    have h := Nat.le_mul_of_pos_right s hu
    omega
  have hset : (s*u).divisors.filter (fun d => d ≤ n) = s.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,_⟩,hdn⟩
      have hc := hr d (mem_Ioc.mpr ⟨Nat.pos_of_dvd_of_pos hd hsu,hdn⟩)
      exact ⟨hc.dvd_of_dvd_mul_right hd,hs0.ne'⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨hd.trans (dvd_mul_right s u),hsu.ne'⟩,(Nat.le_of_dvd hs0 hd).trans hsn⟩
  rw [sub_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta]
  change (1:ArithmeticFunction ℝ) (s*u) - (head n (μ:ArithmeticFunction ℝ)*ζ) (s*u) = 0
  rw [ArithmeticFunction.one_apply_ne hsune, ArithmeticFunction.coe_mul_zeta_apply]
  change 0-(∑ d ∈ (s*u).divisors, if d ≤ n then (μ d:ℝ) else 0)=0
  rw [← sum_filter,hset]
  have hsum := congrArg (fun f : ArithmeticFunction ℝ => f s)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne (by omega)] at hsum
  have hz : ∑ d ∈ s.divisors, (μ d:ℝ) = 0 := hsum
  rw [hz, sub_zero]

/-- Every mixed product whose complete small-prime part is strictly between
one and the cutoff inclusive has identically zero bilinear coefficient. -/
theorem bilinear_mixed_eq_zero {n s r : ℕ} (hs : 1 < s) (hsn : s ≤ n)
    (hr : ∀ d ∈ Ioc 0 n, d.Coprime r) : bilinear n n (s*r) = 0 := by
  by_cases hr0 : r=0
  · simp [hr0]
  have hsr := hr s (mem_Ioc.mpr ⟨by omega,hsn⟩)
  let H := ((μ:ArithmeticFunction ℝ)-head n μ)*ζ
  have heq : bilinear n n = (Λ-head n Λ)*H := by
    unfold bilinear cofactor H
    ring
  rw [heq, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun v k => (Λ-head n Λ:ArithmeticFunction ℝ) v * H k)]
  apply sum_eq_zero
  intro v hv
  change (Λ v-head n Λ v)*H (s*r/v) = 0
  by_cases hvn : v ≤ n
  · simp [head, hvn]
  by_cases hpow : IsPrimePow v
  · have hmem := mem_filter.mpr ⟨hv,hpow⟩
    rw [Nat.mul_divisors_filter_prime_pow hsr,filter_union] at hmem
    have hvr : v ∣ r := by
      rcases mem_union.mp hmem with h | h
      · have hvs := Nat.dvd_of_mem_divisors (mem_filter.mp h).1
        exact (hvn ((Nat.le_of_dvd (by omega) hvs).trans hsn)).elim
      · exact Nat.dvd_of_mem_divisors (mem_filter.mp h).1
    have hv0 := Nat.pos_of_dvd_of_pos hvr (Nat.pos_of_ne_zero hr0)
    have hu := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hvr) hv0
    rw [Nat.mul_div_assoc s hvr]
    apply mul_eq_zero_of_right
    exact moebius_tail_on_mixed hs hsn hu (fun d hd =>
      Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd hvr) (hr d hd))
  · simp [head, hvn, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]

private theorem head_mul_on_rough (f g : ArithmeticFunction ℝ) {n r : ℕ} (hn : 1 ≤ n)
    (hr0 : 0 < r) (hr : ∀ d ∈ Ioc 0 n, d.Coprime r) :
    (head n f * g) r = f 1 * g r := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun d q => head n f d * g q)]
  rw [sum_eq_single 1]
  · simp [head, hn]
  · intro d hd hne
    by_cases hdn : d ≤ n
    · have hdv := Nat.dvd_of_mem_divisors hd
      have hc := hr d (mem_Ioc.mpr ⟨Nat.pos_of_dvd_of_pos hdv hr0,hdn⟩)
      exact (hne (Nat.eq_one_of_dvd_coprimes hc dvd_rfl hdv)).elim
    · simp [head, hdn]
  · exact fun h => (h (Nat.one_mem_divisors.mpr hr0.ne')).elim

/-- On a rough integer beyond the cutoff, the bilinear coefficient is
the von Mangoldt weight minus the full logarithm. -/
theorem bilinear_rough_eq {n r : ℕ} (hn : 1 ≤ n) (hnr : n < r)
    (hr : ∀ d ∈ Ioc 0 n, d.Coprime r) : bilinear n n r = Λ r-log r := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f r) (vaughan n n)
  change Λ r = head n Λ r + (head n (μ:ArithmeticFunction ℝ) * ArithmeticFunction.log) r -
    (head n (μ:ArithmeticFunction ℝ) * head n Λ * ζ) r + bilinear n n r at h
  rw [mul_assoc, head_mul_on_rough _ _ hn (by omega) hr, head_mul_on_rough _ _ hn (by omega) hr,
    head_mul_on_rough _ _ hn (by omega) hr] at h
  simp [head, hnr.not_ge, ArithmeticFunction.log_apply] at h
  linarith only [h]

/-- An exact product formula for the frozen lower band and the remaining moving upper band. -/
theorem cubicProductResponse_eq_pairs (n : ℕ) :
    cubicProductResponse n =
      (∑ e ∈ Ioc 0 (3*n^3), vaughanPair n e * ((3*n^3/e:ℕ):ℝ))/2 +
      cubicMean n (fun M => ∑ e ∈ Ioc 0 M, vaughanPair n e *
        ∑ k ∈ Ioc (3*n^3/e) (M/e), weight M (e*k)) := by
  unfold cubicProductResponse cubicWeightedResponse
  congr 1
  · have h := sum_bilinear_products (3*n^3) n (fun _ => (1:ℝ))
    simp only [mul_one, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at h
    rw [h]
  · exact congrArg (cubicMean n) (funext fun M => weighted_bilinear_upper_products M (3*n^3) n)

private theorem coprime_small_divisors {n r : ℕ} (hr : r.Coprime n.factorial)
    (d : ℕ) (hd : d ∈ Ioc 0 n) : d.Coprime r :=
  Nat.Coprime.of_dvd_left (Nat.dvd_factorial (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2) hr.symm

/-- In the moving upper sum, mixed products with a complete small-prime
part through n vanish. Rough products have an explicit logarithmic weight. -/
theorem cubicProductResponse_eq_sieved {n : ℕ} (hn : 1 ≤ n) :
    cubicProductResponse n = (∑ p ∈ Icc 0 (3*n^3), bilinear n n p)/2 +
      cubicMean n (fun M => ∑ p ∈ (Ioc (3*n^3) M).filter
        (fun p => ∀ s ∈ p.divisors, 1<s → s≤n → ¬(p/s).Coprime n.factorial),
        (if p.Coprime n.factorial then Λ p-log p else bilinear n n p)*weight M p) := by
  unfold cubicProductResponse cubicWeightedResponse
  congr 1
  apply congrArg (cubicMean n)
  funext M
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : ∀ s ∈ p.divisors, 1<s → s≤n → ¬(p/s).Coprime n.factorial
  · rw [ite_eq_left h]
    by_cases hr : p.Coprime n.factorial
    · have hpn : n < p := (Nat.le_self_pow (by decide : 3 ≠ 0) n).trans_lt
        ((show n^3 ≤ 3*n^3 by omega).trans_lt (mem_Ioc.mp hp).1)
      rw [ite_eq_left hr, bilinear_rough_eq hn hpn (coprime_small_divisors hr)]
    · rw [ite_eq_right hr]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨s,hs,hs1,hsn,hr⟩ := h
    have hz := bilinear_mixed_eq_zero hs1 hsn (coprime_small_divisors hr)
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hs)] at hz
    rw [hz, zero_mul]

/-- Cost of replacing the weights on the entire initial product band. -/
theorem cubicProductResponse_error {n : ℕ} (hn : 8 ≤ n) :
    |cubicMean n (fun M => weightedCoefficient M (n^3) (bilinear n n)) -
      cubicProductResponse n| ≤ 6*(n:ℝ)^2 * log (3*(n:ℝ)^3) * (1+log (3*(n:ℝ)^3)) := by
  let D := n^3
  let R := 3*D
  let c := bilinear n n
  let tail (M : ℕ) := ∑ p ∈ Ioc R M, c p * weight M p
  let low := ∑ p ∈ Icc 0 R, (c p) • (fun M : ℕ => weight M (max D p))
  have hDR : D ≤ R := by dsimp [R]; omega
  have hmap : cubicMean n (fun M => weightedCoefficient M D c) = cubicMean n (low+tail) := by
    apply cubicMean_triple_congr hn
    intro M hm
    rw [weightedCoefficient_split hDR hm]
    simp only [low, tail, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have he : cubicMean n (fun M => weightedCoefficient M D c)-cubicProductResponse n =
      ∑ p ∈ Icc 0 R, c p * (cubicMean n (fun M => weight M (max D p))-1/2) := by
    change cubicMean n (fun M => weightedCoefficient M D c) -
      ((∑ p ∈ Icc 0 R, c p)/2+cubicMean n tail) = _
    rw [hmap, map_add]
    simp only [low, map_sum, map_smul, smul_eq_mul, mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ ∑ p ∈ Icc 0 R, |c p| * (2/(n:ℝ)) := by
      apply sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (cubicMean_weight_half (by omega : 1 ≤ n)
        (le_max_left D p) (max_le hDR (mem_Icc.mp hp).2)) (abs_nonneg _)
    _ ≤ ((R:ℝ)*log R*(1+log R)) * (2/(n:ℝ)) := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (bilinear_prefix_abs_le n R) (by positivity)
    _ = _ := by dsimp [R,D]; push_cast; field_simp; ring

/-- On any complete window the total normalized cost is at most cubic in its logarithm. -/
theorem cubicProductResponse_window_error {m b : ℕ} (hm : 8 ≤ m) :
    ∑ n ∈ Icc m b, |cubicMean n (fun M => weightedCoefficient M (n^3) (bilinear n n)) -
      cubicProductResponse n|/(n:ℝ)^3 ≤ 54*(1+log b)^3 := by
  calc
    _ ≤ ∑ n ∈ Icc m b, (54*(1+log b)^2)*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn8 := hm.trans (mem_Icc.mp hn).1
      have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hl := log_le_log hn0 (show (n:ℝ) ≤ b by exact_mod_cast (mem_Icc.mp hn).2)
      have hL : log (3*(n:ℝ)^3) ≤ 2+3*log b := by
        rw [log_mul (by norm_num) (pow_ne_zero _ hn0.ne'), log_pow, Nat.cast_ofNat]
        linarith only [hl, log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
      have hpos : 0 ≤ log (3*(n:ℝ)^3) := log_nonneg (by
        have hh : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        nlinarith only [one_le_pow₀ hh (n := 3)])
      have hprod := mul_le_mul (b := 3*(1+log b)) (d := 3*(1+log b))
        (by linarith only [hL]) (by linarith only [hL]) (by linarith only [hpos])
        (by positivity [log_natCast_nonneg b]) (a := log (3*(n:ℝ)^3)) (c := 1+log (3*(n:ℝ)^3))
      apply (div_le_iff₀ (pow_pos hn0 3)).mpr
      rw [show 54*(1+log b)^2*(n:ℝ)⁻¹*(n:ℝ)^3 = (6*(n:ℝ)^2)*(3*(1+log b)*(3*(1+log b))) by field_simp; ring]
      exact (cubicProductResponse_error hn8).trans (by
        rw [mul_assoc (6*(n:ℝ)^2)]
        exact mul_le_mul_of_nonneg_left hprod (by positivity))
    _ ≤ _ := by
      rw [← mul_sum]
      exact (mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (a := m) (b := b) (by omega))
        (by positivity : 0 ≤ 54*(1+log b)^2)).trans_eq (by ring)

/-- The two smooth moments with their truncated arithmetic coefficients. -/
def cubicSmoothMoments (n : ℕ) : ℝ :=
  cubicMean n (fun M =>
    (1+moebiusLogReciprocal n+moebiusReciprocal n*(1+mangoldtReciprocal n)) *
      tailQuadratureSumIntegral M (n^3) id -
    moebiusReciprocal n * tailQuadratureSumIntegral M (n^3) (fun x => x*log x))

/-- The two explicit smooth moments minus the product sum with its fixed initial weight. -/
def cubicProductResidual (n : ℕ) : ℝ :=
  cubicSmoothMoments n - cubicProductResponse n

theorem cubicVaughanResidual_sub_product {n : ℕ} (hn : 8 ≤ n) :
    cubicVaughanResidual n - cubicProductResidual n = cubicProductResponse n -
      cubicMean n (fun M => weightedCoefficient M (n^3) (bilinear n n)) := by
  rw [cubicVaughanResidual_eq_moments hn, cubicProductResidual]
  let f (M : ℕ) := weightedCoefficient M (n^3) (bilinear n n)
  let g (M : ℕ) := moebiusReciprocal n * tailQuadratureSumIntegral M (n^3) (fun x => x*log x)
  let t (M : ℕ) := (1+moebiusLogReciprocal n+moebiusReciprocal n*(1+mangoldtReciprocal n)) *
    tailQuadratureSumIntegral M (n^3) id
  change cubicMean n (-f-g+t) - (cubicMean n (t-g)-cubicProductResponse n) = _
  rw [map_add, map_sub, map_neg, map_sub]
  dsimp only [f]
  ring

/-- Positive normalized mass for the product sum with the widened cutoff. -/
def cubicProductMassOn (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (cubicProductResidual n) 0 / (n:ℝ)^3

theorem cubicProductMassOn_error {m b : ℕ} (hm : 8 ≤ m) :
    |cubicVaughanMassOn m b - cubicProductMassOn m b| ≤ 54*(1+log b)^3 := by
  unfold cubicVaughanMassOn cubicProductMassOn
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply le_trans _ (cubicProductResponse_window_error (b := b) hm)
  apply sum_le_sum
  intro n hn
  rw [← sub_div, abs_div, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (abs_max_sub_max_le_abs _ _ 0).trans_eq (by
    rw [cubicVaughanResidual_sub_product (hm.trans (mem_Icc.mp hn).1), abs_sub_comm])

/-- A cofinal subpower upper bound on the residual with all weights frozen
through three cubic cutoffs suffices for RH. -/
theorem rh_of_cubicProductMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicProductMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicVaughanMassOn_powerWindows
  apply subpowerWindows_of_log_cube_error (K := 54) (by norm_num) _ h
  intro m b hm
  linarith only [(abs_le.mp (cubicProductMassOn_error (b := b) hm)).2]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.cubicProductResponse_eq_sieved,
      ``RiemannGaussian.AlpogeMined.cubicProductResponse_eq_pairs,
      ``RiemannGaussian.AlpogeMined.abs_vaughanPair_le_log,
      ``RiemannGaussian.AlpogeMined.cubicProductResponse_window_error,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicProductMassOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
