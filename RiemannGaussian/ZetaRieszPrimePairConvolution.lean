import RiemannGaussian.ZetaRieszHeadOrders

/-!
# Prime-pair corrections in the same finite cofactor moments as the head

The finite unlogged moments retain product phases, all complementary
factorial orders, the repeated-prime diagonal, and unordered integer counts.
-/

namespace RiemannGaussian.ZetaRieszPrimePairConvolution
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszHeadOrders ZetaPrimeCofactorCompletion ZetaRieszRemainingPrefix
open ZetaRieszCentralWindow ZetaRieszCentralPair ZetaRieszAnnulusJoint

/-- The finite unlogged cofactor moment, retaining every prime phase. -/
def finiteMoment (A : Finset ℕ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ a ∈ A, zetaPrimeLogKernel k s a

/-- The logged and unlogged finite cofactor arrays share every phase;
one shifted factorial order exactly accounts for the logarithm. -/
theorem cofactorMoment_eq_succ (A : Finset ℕ) (k : ℕ) (s : ℂ) :
    cofactorMoment A k s = ((k + 1 : ℕ) : ℂ) * finiteMoment A (k + 1) s := by
  simp only [cofactorMoment, finiteMoment, Finset.mul_sum, log_mul_kernel]

/-- Both finite prime factors give an exact factorial convolution,
including the diagonal and every complementary order. -/
theorem ordered_kernel_eq_convolution (A B : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) (M : ℕ) (s : ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, zetaPrimeLogKernel M s (a * b)) =
      ∑ k ∈ Finset.range (M + 1), finiteMoment A k s * finiteMoment B (M - k) s := by
  simp only [finiteMoment, Finset.sum_mul]
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [logKernel_product M s (hA a ha) (hB b hb)]
  simp only [Finset.mul_sum, zetaPrimeLogKernel]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Two prime product labels coincide in precisely their two possible
orientations. This supplies the actual unordered multiplicity. -/
theorem prime_mul_eq_iff {a p b q : ℕ} (ha : a.Prime)
    (hb : b.Prime) (hq : q.Prime) :
    a * p = b * q ↔ (a = b ∧ p = q) ∨ (a = q ∧ p = b) := by
  constructor
  · intro he
    have hd : a ∣ b * q := he ▸ dvd_mul_right a p
    rcases ha.dvd_mul.mp hd with hab | haq
    · have hab := (Nat.prime_dvd_prime_iff_eq ha hb).mp hab
      subst b
      exact Or.inl ⟨rfl, Nat.eq_of_mul_eq_mul_left ha.pos he⟩
    · have haq := (Nat.prime_dvd_prime_iff_eq ha hq).mp haq
      subst q
      rw [mul_comm b a] at he
      exact Or.inr ⟨rfl, Nat.eq_of_mul_eq_mul_left ha.pos he⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact mul_comm _ _

/-- The ordered off-diagonal prime pairs, without collapsing their
two incidences into an integer label. -/
def distinctPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun ap => ap.1 ≠ ap.2)

/-- Every unordered integer fibre consists of exactly its two swapped
distinct-prime incidences, with no square or multiplicity omitted. -/
theorem distinct_product_fibre (A : Finset ℕ) (hA : ∀ a ∈ A, a.Prime)
    {a p : ℕ} (ha : a ∈ A) (hp : p ∈ A) (hap : a ≠ p) :
    (distinctPairs A).filter (fun bq => bq.1 * bq.2 = a * p) = {(a, p), (p, a)} := by
  ext bq
  rcases bq with ⟨b, q⟩
  simp only [distinctPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨hb, hq⟩, _⟩, he⟩
    rcases (prime_mul_eq_iff (hA b hb) (hA a ha) (hA p hp)).mp he with h | h
    · exact Or.inl (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.1 h.2)
  · rintro (he | he)
    · cases he
      exact ⟨⟨⟨ha, hp⟩, hap⟩, rfl⟩
    · cases he
      exact ⟨⟨⟨hp, ha⟩, Ne.symm hap⟩, mul_comm _ _⟩

/-- The ordered distinct-prime response counts each genuine product
integer exactly twice, for every complex observation on that integer. -/
theorem sum_distinct_eq_twice_labels (A : Finset ℕ) (hA : ∀ a ∈ A, a.Prime) (f : ℕ → ℂ) :
    (∑ ap ∈ distinctPairs A, f (ap.1 * ap.2)) = 2 * ∑ n ∈ pairedLabels A, f n := by
  have hmap : ∀ ap ∈ distinctPairs A, ap.1 * ap.2 ∈ pairedLabels A := by
    intro ap hap
    exact Finset.mem_image.mpr ⟨ap, hap, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun ap => f (ap.1 * ap.2)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨⟨a, p⟩, hap, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hap, hne⟩ := Finset.mem_filter.mp hap
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  rw [distinct_product_fibre A hA ha hp hne]
  have hpair : (a, p) ≠ (p, a) := fun h => hne (congrArg Prod.fst h)
  simp only [Finset.sum_pair hpair, mul_comm p a]
  ring

/-- The full ordered pair sum is twice its unordered distinct-prime
integer response plus its single repeated-prime diagonal. -/
theorem sum_ordered_eq_twice_labels_add_diagonal (A : Finset ℕ)
    (hA : ∀ a ∈ A, a.Prime) (f : ℕ → ℂ) :
    (∑ a ∈ A, ∑ p ∈ A, f (a * p)) =
      2 * ∑ n ∈ pairedLabels A, f n + ∑ a ∈ A, f (a ^ 2) := by
  rw [← sum_distinct_eq_twice_labels A hA f]
  have he : (∑ ap ∈ distinctPairs A, f (ap.1 * ap.2)) +
      ∑ ap ∈ (A ×ˢ A).filter (fun ap => ap.1 = ap.2), f (ap.1 * ap.2) =
        ∑ ap ∈ A ×ˢ A, f (ap.1 * ap.2) := by
    simpa only [distinctPairs, not_not] using
      Finset.sum_filter_add_sum_filter_not (A ×ˢ A) (fun ap => ap.1 ≠ ap.2) (fun ap => f (ap.1 * ap.2))
  have hd : (∑ ap ∈ (A ×ˢ A).filter (fun ap => ap.1 = ap.2), f (ap.1 * ap.2)) =
      ∑ a ∈ A, f (a ^ 2) := by
    simp only [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_eq_single a]
    · simp [pow_two]
    · intro p _ hpa
      simp [Ne.symm hpa]
    · exact fun h => (h ha).elim
  rw [hd, Finset.sum_product] at he
  exact he.symm

/-- The original fixed polynomial is exactly the sum of its shifted
factorial kernels, before any phase or coefficient is compressed. -/
theorem filterKernel_eq_moments (P : Polynomial ℂ) (N n : ℕ) (s : ℂ) :
    zetaPrimeFilterKernel P N s n = ∑ j ∈ P.support, P.coeff j * zetaPrimeLogKernel (N + j) s n := by
  rw [zetaPrimeFilterKernel_nat]
  simp only [Finset.mul_sum, zetaPrimeLogKernel]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The full product logarithm shifts every original factorial order,
with no lost term from the fixed polynomial filter. -/
theorem logFilterKernel_eq_shifted (P : Polynomial ℂ) (N n : ℕ) (s : ℂ) :
    (Real.log n : ℂ) * zetaPrimeFilterKernel P N s n =
      ∑ j ∈ P.support, (P.coeff j * ((N + j + 1 : ℕ) : ℂ)) *
        zetaPrimeLogKernel (N + j + 1) s n := by
  rw [filterKernel_eq_moments, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, log_mul_kernel]
  ring

/-- The full distinct-prime correction with its unique integer labels
and original logarithmic coefficient and complex filter. -/
def pairLogResponse (A : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ pairedLabels A, (Real.log n : ℂ) * zetaPrimeFilterKernel P N s n

/-- The half ordered convolution shares its finite moment array with
the logged cofactor head. Its single repeated-prime diagonal is retained. -/
def pairConvolution (A : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ P.support, (P.coeff j * ((N + j + 1 : ℕ) : ℂ) / 2) *
    ∑ k ∈ Finset.range (N + j + 2), finiteMoment A k s * finiteMoment A (N + j + 1 - k) s

/-- The exact half ordered diagonal has coefficient log(a) at a squared
prime label; it is distinct from the earlier Riesz-prefix diagonal. -/
def pairDiagonal (A : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ a ∈ A, (Real.log a : ℂ) * zetaPrimeFilterKernel P N s (a ^ 2 : ℕ)

/-- The genuine unordered prime-pair correction is exactly its
factorial convolution minus the full single diagonal. -/
theorem pairLogResponse_eq_convolution_sub_diagonal (A : Finset ℕ)
    (hA : ∀ a ∈ A, a.Prime) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    pairLogResponse A P N s = pairConvolution A P N s - pairDiagonal A P N s := by
  let f := fun n : ℕ => (Real.log n : ℂ) * zetaPrimeFilterKernel P N s n
  have he := sum_ordered_eq_twice_labels_add_diagonal A hA f
  have hc : (∑ a ∈ A, ∑ p ∈ A, f (a * p)) = 2 * pairConvolution A P N s := by
    dsimp only [f]
    simp only [logFilterKernel_eq_shifted]
    calc
      _ = ∑ a ∈ A, ∑ j ∈ P.support, ∑ p ∈ A,
          (P.coeff j * ((N + j + 1 : ℕ) : ℂ)) * zetaPrimeLogKernel (N + j + 1) s (a * p) := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ j ∈ P.support, ∑ a ∈ A, ∑ p ∈ A,
          (P.coeff j * ((N + j + 1 : ℕ) : ℂ)) * zetaPrimeLogKernel (N + j + 1) s (a * p) :=
        Finset.sum_comm
      _ = ∑ j ∈ P.support, (P.coeff j * ((N + j + 1 : ℕ) : ℂ)) *
          ∑ a ∈ A, ∑ p ∈ A, zetaPrimeLogKernel (N + j + 1) s (a * p) := by
        simp only [Finset.mul_sum]
      _ = _ := by
        simp only [ordered_kernel_eq_convolution A A (fun a ha => (hA a ha).pos)
          (fun a ha => (hA a ha).pos), pairConvolution, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hd : (∑ a ∈ A, f (a ^ 2)) = 2 * pairDiagonal A P N s := by
    simp only [f, pairDiagonal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  rw [hc, hd] at he
  change 2 * pairConvolution A P N s = 2 * pairLogResponse A P N s + 2 * pairDiagonal A P N s at he
  linear_combination -(1 / 2 : ℂ) * he

/-- Passing from the actual central pair correction to the complete
finite log-weighted pair sum has independently vanishing error. -/
theorem tendsto_pairLog_sub_central (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (pairLogResponse (intermediatePrimes u N) P N (3 / 2 + Complex.I * y) -
        centralPairResponse P u y N)) atTop (nhds 0) := by
  have h := tendsto_sub_centralBand (fun N => pairedLabels (intermediatePrimes u N))
    (fun _ n => (Real.log n : ℂ)) (fun _ n _ => by
      simpa only [Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg n)] using
        log_le_divisor_majorant n) P y (by linarith : 0 < u) huh
  apply h.congr'
  filter_upwards [eventually_ge_atTop 20] with N hN
  rw [centralPairResponse_eq_log_sum P y hu hN]
  rfl

/-- The actual half ordered prime-square diagonal has a convergent
Euler allowance for every positive tilt below one, uniformly in height. -/
theorem norm_pairDiagonal_le (A : Finset ℕ) (hA : ∀ a ∈ A, a.Prime)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ‖pairDiagonal A P N (3 / 2 + Complex.I * y)‖ ≤
      q⁻¹ ^ N * (∑ j ∈ P.support, ‖P.coeff j‖ * q⁻¹ ^ j) *
        ∑' n, ZetaPrimeNonlinearTail.squareLogWeight (3 / 2 - q) n := by
  let F : ℝ := ∑ j ∈ P.support, ‖P.coeff j‖ * q⁻¹ ^ j
  have hF : 0 ≤ F := Finset.sum_nonneg (fun _ _ => by positivity)
  have hterm (a : ℕ) (ha : a ∈ A) :
      ‖(Real.log a : ℂ) * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a ^ 2 : ℕ)‖ ≤
        (q⁻¹ ^ N * F) * ZetaPrimeNonlinearTail.squareLogWeight (3 / 2 - q) a := by
    have hx : (1 : ℝ) ≤ (a ^ 2 : ℕ) := by
      exact_mod_cast (one_le_pow₀ (hA a ha).one_le : 1 ≤ a ^ 2)
    have hk := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y) hx hq
    have hlog : Real.log (a ^ 2 : ℕ) = 2 * Real.log a := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    simp only [show (3 / 2 + Complex.I * (y : ℂ)).re = 3 / 2 by simp, hlog] at hk
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg a)]
    apply (mul_le_mul_of_nonneg_left hk (Real.log_natCast_nonneg a)).trans_eq
    dsimp [ZetaPrimeNonlinearTail.squareLogWeight, zetaPrimeExpWeight, F]
    rw [show -(3 / 2 - q) * (2 * Real.log a) = -(2 * (3 / 2 - q)) * Real.log a by ring]
    ring
  have hmass : (∑ a ∈ A, ZetaPrimeNonlinearTail.squareLogWeight (3 / 2 - q) a) ≤
      ∑' n, ZetaPrimeNonlinearTail.squareLogWeight (3 / 2 - q) n :=
    Summable.sum_le_tsum A (fun n _ => mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg n))
      (ZetaPrimeNonlinearTail.summable_squareLogWeight (by linarith))
  unfold pairDiagonal
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ A, (q⁻¹ ^ N * F) * ZetaPrimeNonlinearTail.squareLogWeight (3 / 2 - q) a :=
      Finset.sum_le_sum hterm
    _ = (q⁻¹ ^ N * F) * ∑ a ∈ A, ZetaPrimeNonlinearTail.squareLogWeight (3 / 2 - q) a := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

/-- The precise normalized diagonal budget retains the fixed filter
and every selected prime, with no cancellation or zero hypothesis. -/
theorem norm_normalized_pairDiagonal_le (A : Finset ℕ) (hA : ∀ a ∈ A, a.Prime)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {u q : ℝ} (hu : 0 < u)
    (hq : 0 < q) (hq1 : q < 1) :
    ‖(u : ℂ) ^ (N + 1) * pairDiagonal A P N (3 / 2 + Complex.I * y)‖ ≤
      (u / q) ^ N * (u * (∑ j ∈ P.support, ‖P.coeff j‖ * q⁻¹ ^ j) *
        ∑' n, ZetaPrimeNonlinearTail.squareLogWeight (3 / 2 - q) n) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  apply (mul_le_mul_of_nonneg_left (norm_pairDiagonal_le A hA P N y hq hq1) (by positivity)).trans_eq
  rw [pow_succ, div_pow, div_eq_mul_inv, inv_pow]
  ring

/-- The exact prime-square diagonal in the pair convolution vanishes
independently for all source radii below one and arbitrary moving prime masks. -/
theorem tendsto_pairDiagonal (A : ℕ → Finset ℕ) (hA : ∀ N a, a ∈ A N → a.Prime)
    (P : Polynomial ℂ) (y : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * pairDiagonal (A N) P N (3 / 2 + Complex.I * y))
      atTop (nhds 0) := by
  let q : ℝ := (u + 1) / 2
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hrate : u / q < 1 := (div_lt_one hq).mpr (by dsimp [q]; linarith)
  apply squeeze_zero_norm (fun N => norm_normalized_pairDiagonal_le (A N) (hA N) P N y hu hq hq1)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hrate).mul_const
      (u * (∑ j ∈ P.support, ‖P.coeff j‖ * q⁻¹ ^ j) *
        ∑' n, ZetaPrimeNonlinearTail.squareLogWeight (3 / 2 - q) n)

/-- The actual central prime-pair correction is asymptotic to the
half ordered factorial convolution, with both independent errors paid. -/
theorem tendsto_pairConvolution_sub_central (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (pairConvolution (intermediatePrimes u N) P N (3 / 2 + Complex.I * y) -
        centralPairResponse P u y N)) atTop (nhds 0) := by
  have hu0 : 0 < u := by linarith
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hd := tendsto_pairDiagonal (intermediatePrimes u)
    (fun N a ha => ((mem_intermediatePrimes u N a).mp ha).1) P y hu0 hu1
  have h := (tendsto_pairLog_sub_central P y hu huh).add hd
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [pairLogResponse_eq_convolution_sub_diagonal (intermediatePrimes u N)
    (fun a ha => ((mem_intermediatePrimes u N a).mp ha).1) P N (3 / 2 + Complex.I * y)]
  ring


end
end RiemannGaussian.ZetaRieszPrimePairConvolution
