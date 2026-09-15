/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeRieszWindows
import RiemannGaussian.ZetaRieszCentralPrimeLayers
import Mathlib.Combinatorics.SetFamily.LYM

/-!
# Antichain savings in signed Riesz divisor windows

Two exact prime differences leave a moving logarithmic divisor window.
When every remaining prime logarithm is at least its width, the surviving
prime subsets form an antichain. Sperner's theorem bounds that support.
-/

namespace RiemannGaussian.ZetaRieszSperner
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows

/-- Subsets whose total weight lies in one strict window. -/
def subsetWindow {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (b v : ℝ) : Finset (Finset ι) :=
  Finset.univ.powerset.filter (fun A => v - b < ∑ i ∈ A, w i ∧ ∑ i ∈ A, w i < v)

/-- A window no wider than any individual positive weight cannot
contain two comparable distinct subsets. The endpoint convention is exact. -/
theorem subsetWindow_antichain {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {b : ℝ} (hb : 0 < b) (hw : ∀ i, b ≤ w i) (v : ℝ) :
    IsAntichain (· ⊆ ·) (subsetWindow w b v : Set (Finset ι)) := by
  intro A hA B hB hne hsub
  have hAwin := (Finset.mem_filter.mp hA).2
  have hBwin := (Finset.mem_filter.mp hB).2
  have hnot : ¬ B ⊆ A := fun he => hne (Finset.Subset.antisymm hsub he)
  obtain ⟨i, hiB, hiA⟩ := Finset.not_subset.mp hnot
  have hi : insert i A ⊆ B := Finset.insert_subset_iff.mpr ⟨hiB, hsub⟩
  have hh : (∑ j ∈ insert i A, w j) ≤ ∑ j ∈ B, w j :=
    Finset.sum_le_sum_of_subset_of_nonneg hi (fun j _ _ => hb.le.trans (hw j))
  rw [Finset.sum_insert hiA] at hh
  linarith [hw i, hAwin.1, hBwin.2]

/-- The whole surviving window costs at most the middle binomial
coefficient, rather than the complete Boolean divisor cube. -/
theorem subsetWindow_card_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {b : ℝ} (hb : 0 < b) (hw : ∀ i, b ≤ w i) (v : ℝ) :
    (subsetWindow w b v).card ≤ (Fintype.card ι).choose (Fintype.card ι / 2) :=
  (subsetWindow_antichain w hb hw v).sperner

/-- The prime subset of a divisor, inside the cofactor's exact finite
prime universe. -/
def divisorPrimeSet (m d : ℕ) : Finset m.primeFactors :=
  d.primeFactors.subtype (fun p => p ∈ m.primeFactors)

/-- Passing to the finite prime universe loses no divisor prime. -/
theorem divisorPrimeSet_map {m d : ℕ} (hm : Squarefree m) (hd : d ∈ m.divisors) :
    (divisorPrimeSet m d).map (Function.Embedding.subtype _) = d.primeFactors := by
  apply Finset.subtype_map_of_mem
  exact fun _ hp => Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hm.ne_zero hp

/-- The subset weight equals the actual divisor logarithm exactly. -/
theorem divisorPrimeSet_log_sum {m d : ℕ} (hm : Squarefree m) (hd : d ∈ m.divisors) :
    (∑ p ∈ divisorPrimeSet m d, Real.log (p.val : ℝ)) = Real.log d := by
  rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum
    (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)), ← divisorPrimeSet_map hm hd]
  simp only [Finset.sum_map, Function.Embedding.coe_subtype]

/-- Squarefreeness makes the prime-subset encoding injective on every
actual divisor, including the unit and the full cofactor. -/
theorem divisorPrimeSet_injective {m : ℕ} (hm : Squarefree m) :
    Set.InjOn (divisorPrimeSet m) (m.divisors : Set ℕ) := by
  intro d hd e he hde
  have h := congrArg (Finset.map (Function.Embedding.subtype _)) hde
  rw [divisorPrimeSet_map hm hd, divisorPrimeSet_map hm he] at h
  rw [← Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)),
    ← Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)), h]

/-- The actual logarithmic divisor window is bounded by Sperner's
middle layer whenever every cofactor prime logarithm exceeds its width. -/
theorem divisorWindow_card_le {m : ℕ} (hm : Squarefree m) {b : ℝ} (hb : 0 < b)
    (hw : ∀ p ∈ m.primeFactors, b ≤ Real.log p) (v : ℝ) :
    (m.divisors.filter (fun d : ℕ => v - b < Real.log d ∧ Real.log d < v)).card ≤
      m.primeFactors.card.choose (m.primeFactors.card / 2) := by
  let D := m.divisors.filter (fun d : ℕ => v - b < Real.log d ∧ Real.log d < v)
  have hi : Set.InjOn (divisorPrimeSet m) (D : Set ℕ) :=
    (divisorPrimeSet_injective hm).mono (Finset.filter_subset _ _)
  have hsub : D.image (divisorPrimeSet m) ⊆
      subsetWindow (fun p : m.primeFactors => Real.log (p.val : ℝ)) b v := by
    intro A hA
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    rw [divisorPrimeSet_log_sum hm (Finset.mem_filter.mp hd).1]
    exact (Finset.mem_filter.mp hd).2
  calc
    _ = (D.image (divisorPrimeSet m)).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ _ := (Finset.card_le_card hsub).trans (by
      simpa only [Fintype.card_coe] using
        subsetWindow_card_le (fun p : m.primeFactors => Real.log (p.val : ℝ)) hb
          (fun p => hw p.val p.property) v)

/-- The entire signed Mobius window receives an independent antichain
bound; its arithmetic premise is a size condition on the actual primes. -/
theorem abs_signedDivisorWindow_le {m : ℕ} (hm : Squarefree m) {b : ℝ} (hb : 0 < b)
    (hw : ∀ p ∈ m.primeFactors, b ≤ Real.log p) (v : ℝ) :
    |signedDivisorWindow b v m| ≤ (m.primeFactors.card.choose (m.primeFactors.card / 2) : ℝ) := by
  unfold signedDivisorWindow
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ d ∈ m.divisors.filter (fun d : ℕ => v - b < Real.log d ∧ Real.log d < v),
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ m.divisors.filter (fun d : ℕ => v - b < Real.log d ∧ Real.log d < v), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = ((m.divisors.filter (fun d : ℕ => v - b < Real.log d ∧ Real.log d < v)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast divisorWindow_card_le hm hb hw v

/-- After cancelling two inserted prime fibres, Sperner pays every
surviving divisor window. The full Riesz profile is bounded at all cutoffs. -/
theorem abs_riesz_two_primes_sperner (L : ℝ) {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m)
    (hm : Squarefree m) (hmin : ∀ r ∈ m.primeFactors, q ≤ r) :
    |VaughanLogAverage.riesz L (p * (q * m))| ≤
      Real.log p * (m.primeFactors.card.choose (m.primeFactors.card / 2) : ℝ) := by
  apply abs_riesz_two_primes_le_of_window_bound L hp hq hpq hpm hqm
  intro s _
  apply abs_signedDivisorWindow_le hm
    (Real.log_pos (by exact_mod_cast hq.one_lt))
  intro r hr
  exact Real.log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast hmin r hr)

/-- The antichain saving acts on the literal original Riesz band weight,
with every complex amplitude, factorial shift and support mask retained. -/
theorem norm_bandWeight_sperner (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m)
    (hm : Squarefree m) (hmin : ∀ r ∈ m.primeFactors, q ≤ r) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * (q * m))‖ ≤
      ‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t (p * (q * m))‖ *
        (Real.log p * (m.primeFactors.card.choose (m.primeFactors.card / 2) : ℝ)) := by
  rw [ZetaArithmeticBandCorrelation.bandWeight_eq_amplitude_mul_riesz, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_riesz_two_primes_sperner L hp hq hpq hpm hqm hm hmin) (norm_nonneg _)

/-- Every squarefree integer with at least two prime factors admits the
required factorization using its two smallest primes. All support conditions
for the moving-window antichain estimate are therefore arithmetic facts. -/
theorem exists_two_smallest_factorization {n : ℕ} (hn : Squarefree n)
    (hcard : 2 ≤ n.primeFactors.card) :
    ∃ p q m : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * (q * m) ∧
      Squarefree m ∧ ¬ p ∣ m ∧ ¬ q ∣ m ∧
      (∀ r ∈ n.primeFactors, p ≤ r) ∧ (∀ r ∈ m.primeFactors, q ≤ r) ∧
      m.primeFactors.card = n.primeFactors.card - 2 := by
  let S := n.primeFactors
  have hcardS : 2 ≤ S.card := hcard
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  let p := S.min' hS
  have hpS : p ∈ S := Finset.min'_mem _ _
  have hS2 : (S.erase p).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hpS]
    omega)
  let q := (S.erase p).min' hS2
  have hqS : q ∈ S.erase p := Finset.min'_mem _ _
  let T := (S.erase p).erase q
  let m := ∏ r ∈ T, r
  have hT : ∀ r ∈ T, r.Prime := fun r hr => Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
  have hmT : m.primeFactors = T := Nat.primeFactors_prod hT
  have he : n = p * (q * m) := by
    calc
      _ = ∏ r ∈ S, r := (Nat.prod_primeFactors_of_squarefree hn).symm
      _ = p * ∏ r ∈ S.erase p, r := (Finset.mul_prod_erase _ _ hpS).symm
      _ = _ := by rw [← Finset.mul_prod_erase _ _ hqS]
  have hm : Squarefree m := (he ▸ hn).of_mul_right.of_mul_right
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpS
  have hq : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hqS)
  have hpm : ¬ p ∣ m := by
    intro h
    have hh := hp.mem_primeFactors h hm.ne_zero
    rw [hmT] at hh
    exact Finset.notMem_erase p S (Finset.mem_of_mem_erase hh)
  have hqm : ¬ q ∣ m := by
    intro h
    have hh := hq.mem_primeFactors h hm.ne_zero
    rw [hmT] at hh
    exact Finset.notMem_erase q (S.erase p) hh
  refine ⟨p, q, m, hp, hq, (Finset.ne_of_mem_erase hqS).symm, he, hm, hpm, hqm, ?_, ?_, ?_⟩
  · intro r hr
    exact Finset.min'_le S r hr
  · intro r hr
    rw [hmT] at hr
    exact Finset.min'_le (S.erase p) r (Finset.mem_of_mem_erase hr)
  · rw [hmT, Finset.card_erase_of_mem hqS, Finset.card_erase_of_mem hpS]
    change S.card - 1 - 1 = S.card - 2
    omega

/-- The smallest prime logarithm is at most the average of all the
prime logarithms, with squarefreeness retaining their exact total. -/
theorem smallest_prime_log_le_mean {n p : ℕ} (hn : Squarefree n)
    (hcard : 0 < n.primeFactors.card) (hp : p.Prime)
    (hmin : ∀ r ∈ n.primeFactors, p ≤ r) :
    Real.log p ≤ Real.log n / n.primeFactors.card := by
  have hsum : (∑ _r ∈ n.primeFactors, Real.log p) ≤ ∑ r ∈ n.primeFactors, Real.log r := by
    apply Finset.sum_le_sum
    intro r hr
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hmin r hr)
  rw [Finset.sum_const, nsmul_eq_mul, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at hsum
  exact (le_div_iff₀ (by exact_mod_cast hcard)).mpr (by nlinarith)

/-- Every squarefree composite has an independent all-cutoff Riesz
bound after the two smallest prime fibres cancel. The allowance is a
middle-layer coefficient divided by the complete prime count. -/
theorem abs_riesz_le_middle_layer (L : ℝ) {n : ℕ} (hn : Squarefree n)
    (hcard : 2 ≤ n.primeFactors.card) :
    |VaughanLogAverage.riesz L n| ≤
      (Real.log n / n.primeFactors.card) *
        ((n.primeFactors.card - 2).choose ((n.primeFactors.card - 2) / 2) : ℝ) := by
  obtain ⟨p, q, m, hp, hq, hpq, he, hm, hpm, hqm, hpmin, hqmin, hcount⟩ :=
    exists_two_smallest_factorization hn hcard
  have h := abs_riesz_two_primes_sperner L hp hq hpq hpm hqm hm hqmin
  rw [← he, hcount] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (smallest_prime_log_le_mean hn (by omega) hp hpmin) (Nat.cast_nonneg _))

/-- The literal signed coefficient inherits the complete antichain
saving for every squarefree composite, with its original positive length. -/
theorem norm_coefficient_le_middle_layer {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤
      (Real.log n / L) * (Real.log n / n.primeFactors.card) *
        ((n.primeFactors.card - 2).choose ((n.primeFactors.card - 2) / 2) : ℝ) := by
  have hlog := Real.log_natCast_nonneg n
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
      abs_neg, abs_of_nonneg hlog, abs_of_pos hL]
    have hh := mul_le_mul_of_nonneg_left (abs_riesz_le_middle_layer L hn hcard)
      (div_nonneg hlog hL.le)
    convert hh using 1
    · rfl
    · ring
    · ring
  · simp only [norm_zero]
    positivity

/-- A finite actual carrier retains its full factorial filter and
prime counts in the new antichain allowance. The whole signed sum is
bounded only after the exact two-prime cancellation has occurred. -/
theorem norm_sum_le_middle_layers (D : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {L : ℝ} (hL : 0 < L) (hD : ∀ n ∈ D, Squarefree n)
    (hcard : ∀ n ∈ D, 2 ≤ n.primeFactors.card) :
    ‖∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      ∑ n ∈ D, (Real.log n / L) * (Real.log n / n.primeFactors.card) *
        ((n.primeFactors.card - 2).choose ((n.primeFactors.card - 2) / 2) : ℝ) *
          ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_coefficient_le_middle_layer hL (hD n hn) (hcard n hn))
    (norm_nonneg _)

/-- Every nonzero literal coefficient has at least two prime factors;
the unit, ordinary primes and nonsquarefree integers are exactly absent. -/
theorem coefficient_ne_zero_support {L : ℝ} {n : ℕ}
    (hc : SquarefreeVaughanLogSource.coefficient L n ≠ 0) :
    Squarefree n ∧ 2 ≤ n.primeFactors.card := by
  have hs : Squarefree n ∧ ¬ n.Prime := by
    by_contra h
    exact hc (by simp [SquarefreeVaughanLogSource.coefficient, h])
  refine ⟨hs.1, ?_⟩
  by_contra hcard
  have hh : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 := by omega
  rcases hh with hh | hh
  · have he : n = 1 := by
      rw [← Nat.prod_primeFactors_of_squarefree hs.1, Finset.card_eq_zero.mp hh, Finset.prod_empty]
    subst n
    exact hc (by simp [SquarefreeVaughanLogSource.coefficient])
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hh
    have hn : n = p := by rw [← Nat.prod_primeFactors_of_squarefree hs.1, hp, Finset.prod_singleton]
    exact hs.2 (hn ▸ Nat.prime_of_mem_primeFactors (by rw [hp]; simp))

/-- The antichain allowance on precisely the original nonzero support. -/
def middleLayerAllowance (L : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ 2 ≤ n.primeFactors.card then
    (Real.log n / L) * (Real.log n / n.primeFactors.card) *
      ((n.primeFactors.card - 2).choose ((n.primeFactors.card - 2) / 2) : ℝ)
  else 0

/-- The literal allowance is nonnegative for every positive cutoff. -/
theorem middleLayerAllowance_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ middleLayerAllowance L n := by
  unfold middleLayerAllowance
  split_ifs
  · have := Real.log_natCast_nonneg n
    positivity
  · rfl

/-- No support or prime-selection premise remains in the antichain
bound for the original signed arithmetic coefficient. -/
theorem norm_coefficient_le_allowance {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ middleLayerAllowance L n := by
  by_cases hc : SquarefreeVaughanLogSource.coefficient L n = 0
  · rw [hc, norm_zero]
    exact middleLayerAllowance_nonneg hL n
  · obtain ⟨hs, hk⟩ := coefficient_ne_zero_support hc
    rw [middleLayerAllowance, if_pos ⟨hs, hk⟩]
    exact norm_coefficient_le_middle_layer hL hs hk

/-- The complete original signed carrier has a finite antichain
allowance with all arithmetic conditions discharged. The factorial filter
is retained exactly; decay of this full allowance is not asserted. -/
theorem norm_original_band_le_middle_layers (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {L : ℝ} (hL : 0 < L) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ≤
      ∑ n ∈ zetaPrimeLogBand N, middleLayerAllowance L n *
        ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_coefficient_le_allowance hL n) (norm_nonneg _)

/-- On the reflection-side band, the exact antichain allowance removes
at least a factor twice the prime count from the old Boolean mass. -/
theorem middle_layer_le_divisor_saving {k : ℕ} (hk : 2 ≤ k) :
    (2 : ℝ) * ((k - 2).choose ((k - 2) / 2) : ℝ) / k ≤
      (2 : ℝ) ^ k / (2 * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc : ((k - 2).choose ((k - 2) / 2) : ℝ) ≤ (2 : ℝ) ^ (k - 2) := by
    exact_mod_cast Nat.choose_le_two_pow (k - 2) ((k - 2) / 2)
  have he : (2 : ℝ) ^ k = 4 * (2 : ℝ) ^ (k - 2) := by
    calc
      _ = (2 : ℝ) ^ ((k - 2) + 2) := by rw [Nat.sub_add_cancel hk]
      _ = _ := by rw [pow_add]; norm_num; ring
  rw [he]
  apply (div_le_div_iff₀ hk0 (by positivity : (0 : ℝ) < 2 * k)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hc hk0.le]

/-- The coefficient's complete middle-layer saving on the side
log(n)<=2L of the reflection midpoint. -/
theorem norm_coefficient_le_middle_layer_central {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) (hmid : Real.log n ≤ 2 * L) :
    ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤
      Real.log n * (2 * ((n.primeFactors.card - 2).choose ((n.primeFactors.card - 2) / 2) : ℝ) /
        n.primeFactors.card) := by
  have hd : Real.log n / L ≤ 2 := (div_le_iff₀ hL).mpr hmid
  have hlog := Real.log_natCast_nonneg n
  apply (norm_coefficient_le_middle_layer hL hn hcard).trans
  calc
    _ ≤ 2 * (Real.log n / n.primeFactors.card) *
        ((n.primeFactors.card - 2).choose ((n.primeFactors.card - 2) / 2) : ℝ) := by gcongr
    _ = _ := by ring

/-- The original central band itself satisfies the midpoint hypothesis.
Every nonzero arithmetic atom therefore has the new all-frequency bound. -/
theorem norm_actual_central_coefficient_le {u : ℝ} {N n : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N) :
    ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
      Real.log n * (2 * ((n.primeFactors.card - 2).choose ((n.primeFactors.card - 2) / 2) : ℝ) /
        n.primeFactors.card) := by
  by_cases hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n = 0
  · rw [hc, norm_zero]
    have := Real.log_natCast_nonneg n
    positivity
  · obtain ⟨hs, hk⟩ := coefficient_ne_zero_support hc
    apply norm_coefficient_le_middle_layer_central (SquarefreeVaughanLogSource.length_pos _ _) hs hk
    exact (ZetaRieszCentralPrimeLayers.log_lt_twice_length_of_mem_annulus huh
      (ZetaRieszCentralPrimeLayers.centralUnpairedBand_subset_annulus u N hn)).le

/-- A simple explicit improvement of the old central divisor-count
allowance, while the sharper middle-layer bound remains available. -/
theorem norm_actual_central_coefficient_le_divisor_saving {u : ℝ} {N n : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N) :
    ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
      Real.log n * ((2 : ℝ) ^ n.primeFactors.card / (2 * n.primeFactors.card)) := by
  by_cases hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n = 0
  · rw [hc, norm_zero]
    have := Real.log_natCast_nonneg n
    positivity
  · have hs := coefficient_ne_zero_support hc
    exact (norm_actual_central_coefficient_le huh hn).trans
      (mul_le_mul_of_nonneg_left (middle_layer_le_divisor_saving hs.2) (Real.log_natCast_nonneg n))

end
end RiemannGaussian.ZetaRieszSperner
