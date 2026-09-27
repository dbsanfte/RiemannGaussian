/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFivePrimeCells

/-!
# Explicit adverse four-prime cells in the literal core

All three cutoffs in the exact positive four-prime coefficient are retained.
Macroscopic cofactor cells use a last-prime window depending on the exact
cofactor, keeping the full product phase in one fixed log interval. Literal
ordering predicates extend the bound across overlapping prime intervals.
Upper population bounds give a debit factor 501/500. The signed core floor
retains every label outside the selected adverse cells. No full angular
comparison or numerical whole-carrier floor follows from a single cell.
-/

namespace RiemannGaussian.ZetaRieszFourPrimeCells
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszCoupledWindow ZetaRieszMacroPrimeWindows

private theorem amplitude_radial {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    amplitude N n =
      (Real.exp (-Real.log n/2)*(Real.log n)^N/N.factorial)*(n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Real.exp (-(3/2 : ℝ)*Real.log n) =
      Real.exp (-Real.log n/2)*(n : ℝ)⁻¹ := by
    have hi : (n : ℝ)⁻¹ = Real.exp (-Real.log n) := by rw [Real.exp_neg,Real.exp_log hnR]
    rw [hi,← Real.exp_add]
    congr 1
    ring
  rw [amplitude,he]
  ring

/-- An explicit lower bound for any selected adverse last-prime
population. Upper counts pay its debit; unselected primes are not assigned
a favorable phase and are not removed from any whole carrier. -/
theorem eventually_cofactor_floor {h α : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (t L y B : ℝ) (A S : Finset ℕ),
      m ≠ 0 → α*N ≤ t-Real.log m → 0 ≤ B → S ⊆ logPrimes (t-Real.log m) h →
      (∀ p ∈ S, -B ≤ (1-boundedShare A N (m*p))*
          ((SquarefreeVaughanLogSource.coefficient L (m*p)).re*
            Real.cos (y*Real.log (m*p : ℕ)))) →
      -((B*(Real.exp (-t/2)*(t+h)^N/N.factorial)/(m : ℝ))*
        ((10001/10000 : ℝ)*h/(t-Real.log m))) ≤
      (∑ p ∈ S,
        residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re := by
  filter_upwards [ZetaRieszPhaseBudget.eventually_phase_window_mass hh hhu hα]
    with N hN m t L y B A S hm ha hB hS hscore
  have ht : 0 ≤ t := by
    have hn : 0 ≤ α*(N : ℝ) := mul_nonneg hα.le (Nat.cast_nonneg N)
    linarith [Real.log_natCast_nonneg m]
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hpoint (p : ℕ) (hp : p ∈ S) :
      -((B*V/(m : ℝ))*(p : ℝ)⁻¹) ≤
        (residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re := by
    have hb := product_log_bounds hm (hS hp)
    have hmp : m*p ≠ 0 := mul_ne_zero hm hb.1.ne_zero
    have hrad : Real.exp (-Real.log (m*p : ℕ)/2)*
        (Real.log (m*p : ℕ))^N/N.factorial ≤ V := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [hb.2.1]))
        (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hb.2.2 N) (by positivity) (Real.exp_nonneg _)
    have hbr := neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrad hB)
      (inv_nonneg.mpr (Nat.cast_nonneg (m*p))))
    have hsc := mul_le_mul_of_nonneg_right (hscore p hp)
      (show 0 ≤ amplitude N (m*p) from ZetaRieszCosineCarrier.factorial_envelope_nonneg _ _)
    rw [amplitude_radial hmp N] at hsc
    rw [re_residual_atom,weight,amplitude_radial hmp N]
    have hbr' : -((B*V/(m : ℝ))*(p : ℝ)⁻¹) ≤
        -B*((Real.exp (-Real.log (m*p : ℕ)/2)*(Real.log (m*p : ℕ))^N/N.factorial)*
          ((m*p : ℕ) : ℝ)⁻¹) := by
      simpa only [Nat.cast_mul,mul_inv_rev,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,
        neg_mul,mul_neg] using hbr
    exact (hbr'.trans hsc).trans_eq (by ring)
  have hmass : (∑ p ∈ S, (p : ℝ)⁻¹) ≤
      (10001/10000 : ℝ)*h/(t-Real.log m) := by
    apply le_trans _ (hN (t-Real.log m) ha).2
    exact Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  calc
    _ ≤ -((B*V/(m : ℝ))*(∑ p ∈ S, (p : ℝ)⁻¹)) :=
      neg_le_neg (mul_le_mul_of_nonneg_left hmass (div_nonneg (mul_nonneg hB hV) hmR.le))
    _ = ∑ p ∈ S, -((B*V/(m : ℝ))*(p : ℝ)⁻¹) := by
      rw [Finset.mul_sum,Finset.sum_neg_distrib]
    _ ≤ ∑ p ∈ S,
        (residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re :=
      Finset.sum_le_sum hpoint
    _ = _ := (Complex.re_sum _ _).symm


/-- All three obstructions in the ordered positive four-prime coefficient
remain in this common upper cap. -/
def fourWindowCap (L v h t : ℝ) (q r : ℕ) : ℝ :=
  min (Real.log r) (max 0 (min (L-v)
    (min (t+h-L-Real.log q) (v+t+2*h-2*L))))

/-- The adverse cap is nonnegative, including its inactive chambers. -/
theorem fourWindowCap_nonneg (L v h t : ℝ) (q r : ℕ) :
    0 ≤ fourWindowCap L v h t q r :=
  le_min (Real.log_natCast_nonneg r) (le_max_left _ _)

/-- A common upper bound for the positive coefficient keeps its exact
four-prime cap, instead of paying the norm of the whole signed response. -/
theorem four_positive_window_upper {p q a r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hr : r.Prime)
    (hrA : r < a) (haQ : a < q) (hqP : q < p)
    (hs : Squarefree (p*(q*(a*r)))) {L v h t : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log (p*(q*(a*r)) : ℕ))
    (hLlo : 2*Real.log (p*(q*(a*r)) : ℕ) ≤ 3*L)
    (hpl : v ≤ Real.log p) (hpu : Real.log p ≤ v+h)
    (hT : Real.log (p*(q*(a*r)) : ℕ) ≤ t+h) :
    max 0 (SquarefreeVaughanLogSource.coefficient L (p*(q*(a*r)))).re ≤
      ((t+h)/L)*fourWindowCap L v h t q r := by
  rw [ZetaRieszOrderedCapacity.positive_four_eq_cap hp hq ha hr hrA haQ hqP hs hL hLhi hLlo]
  apply mul_le_mul (div_le_div_of_nonneg_right hT hL.le)
  · apply min_le_min le_rfl
    apply max_le_max le_rfl
    apply min_le_min (by linarith)
    apply min_le_min <;> linarith
  · exact le_min (Real.log_natCast_nonneg r) (le_max_left _ _)
  · exact div_nonneg (by linarith [Real.log_natCast_nonneg (p*(q*(a*r)))]) hL.le

/-- The actual phase on the full cofactor-dependent interval is bounded
by a fixed upper negative-cosine envelope, including zero crossings. -/
theorem cofactor_phase_upper {m p : ℕ} (hm : m ≠ 0) {t h y : ℝ}
    (hh : 0 ≤ h) (hp : p ∈ logPrimes (t-Real.log m) h) :
    -Real.cos (y*Real.log (m*p : ℕ)) ≤ max 0 (-Real.cos (y*t))+|y| * h := by
  have hb := product_log_bounds hm hp
  have he : |y*Real.log (m*p : ℕ)-y*t| ≤ |y| * h := by
    rw [← mul_sub,abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg y)
    rw [abs_of_nonneg (by linarith [hb.2.1] : 0 ≤ Real.log (m*p : ℕ)-t)]
    linarith [hb.2.2]
  exact (le_max_right 0 _).trans (ZetaRieszPhaseBudget.negative_phase_enclosure
    (mul_nonneg (abs_nonneg y) hh) he).2

/-- Allocation never enlarges the adverse positive-coefficient debit.
The favorable negative-coefficient part is kept signed. -/
theorem negative_phase_score_floor (A : Finset ℕ) (N n : ℕ) {L y U V : ℝ}
    (hU : 0 ≤ U)
    (hc : max 0 (SquarefreeVaughanLogSource.coefficient L n).re ≤ U)
    (hcos : Real.cos (y*Real.log n) ≤ 0)
    (hv : -Real.cos (y*Real.log n) ≤ V) :
    -(U*V) ≤ (1-boundedShare A N n)*
      ((SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n)) := by
  have hw := boundedShare_bounds A N n
  have hw0 : 0 ≤ 1-boundedShare A N n := by linarith
  have hw1 : 1-boundedShare A N n ≤ 1 := by linarith
  have hcost := mul_le_mul hc hv (neg_nonneg.mpr hcos) hU
  have hsign : max 0 (SquarefreeVaughanLogSource.coefficient L n).re*
      Real.cos (y*Real.log n) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_max_left _ _) hcos
  have h₁ := mul_le_mul_of_nonpos_right hw1 hsign
  have h₂ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonpos_right (le_max_right 0 (SquarefreeVaughanLogSource.coefficient L n).re) hcos) hw0
  have he : max 0 (SquarefreeVaughanLogSource.coefficient L n).re*
      Real.cos (y*Real.log n) ≤ (1-boundedShare A N n)*
      ((SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n)) := by
    have h₁' := h₁
    rw [one_mul] at h₁'
    exact h₁'.trans h₂
  have hh := neg_le_neg hcost
  simp only [mul_neg,neg_neg] at hh
  exact hh.trans he


private theorem squarefree_four_of_order {p q a r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hr : r.Prime)
    (hqp : q < p) (haq : a < q) (hra : r < a) : Squarefree (p*(q*(a*r))) := by
  have cpq : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hp hq]; omega)
  have cpa : p.Coprime a := hp.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hp ha]; omega)
  have cpr : p.Coprime r := hp.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hp hr]; omega)
  have cqa : q.Coprime a := hq.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hq ha]; omega)
  have cqr : q.Coprime r := hq.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hq hr]; omega)
  have car : a.Coprime r := ha.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq ha hr]; omega)
  exact Nat.squarefree_mul_iff.mpr ⟨cpq.mul_right (cpa.mul_right cpr),hp.squarefree,
    Nat.squarefree_mul_iff.mpr ⟨cqa.mul_right cqr,hq.squarefree,
      Nat.squarefree_mul_iff.mpr ⟨car,ha.squarefree,hr.squarefree⟩⟩⟩

/-- The negative-cosine four-prime population has an explicit upper
debit with every coefficient cap retained. It applies to any literal
subselection, so the support and sign masks need not be enlarged. -/
theorem eventually_four_cofactor_floor {h α : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ (A S : Finset ℕ) (q a r : ℕ) (t L y : ℝ),
      q.Prime → a.Prime → r.Prime → a < q → r < a →
      let m := q*(a*r)
      let v := t-Real.log m
      0 < L → L ≤ t → 2*(t+h) ≤ 3*L → α*N ≤ v → Real.log q ≤ v →
      S ⊆ logPrimes v h → (∀ p ∈ S, Real.cos (y*Real.log (m*p : ℕ)) ≤ 0) →
      -(((((t+h)/L)*fourWindowCap L v h t q r*(max 0 (-Real.cos (y*t))+|y| * h))*
          (Real.exp (-t/2)*(t+h)^N/N.factorial)/(m : ℝ))*
        ((10001/10000 : ℝ)*h/v)) ≤
      (∑ p ∈ S,
        residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re := by
  filter_upwards [eventually_cofactor_floor hh hhu hα]
    with N hN A S q a r t L y hq ha hr haq hra
  dsimp only
  intro hL hLt hTcut hv hqv hS hcos
  let m := q*(a*r)
  have hm : m ≠ 0 := mul_ne_zero hq.ne_zero (mul_ne_zero ha.ne_zero hr.ne_zero)
  have ht : 0 < t := hL.trans_le hLt
  apply hN m t L y _ A S hm hv (by
    exact mul_nonneg (mul_nonneg (div_nonneg (by linarith) hL.le)
      (fourWindowCap_nonneg _ _ _ _ _ _))
      (add_nonneg (le_max_left _ _) (mul_nonneg (abs_nonneg y) hh.le))) hS
  intro p hp
  have hb := logPrimes_bounds (hS hp)
  have hqp : q < p := by
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hq.pos)
      (by exact_mod_cast hb.1.pos)).mp (hqv.trans_lt hb.2.1)
  have hs := squarefree_four_of_order hb.1 hq ha hr hqp haq hra
  have he : m*p = p*(q*(a*r)) := Nat.mul_comm _ _
  have hprod := product_log_bounds hm (hS hp)
  have hc := four_positive_window_upper hb.1 hq ha hr hra haq hqp hs hL
    (show L ≤ Real.log (p*(q*(a*r)) : ℕ) by rw [← he]; linarith [hprod.2.1])
    (show 2*Real.log (p*(q*(a*r)) : ℕ) ≤ 3*L by rw [← he]; linarith [hprod.2.2])
    hb.2.1.le hb.2.2 (show Real.log (p*(q*(a*r)) : ℕ) ≤ t+h by
      rw [← he]; exact hprod.2.2)
  rw [← he] at hc
  exact negative_phase_score_floor A N (m*p)
    (mul_nonneg (div_nonneg (by linarith) hL.le) (fourWindowCap_nonneg _ _ _ _ _ _))
    hc (hcos p hp) (cofactor_phase_upper hm hh.le (hS hp))


/-- The full ordered positive-coefficient cap on a macroscopic cofactor
cell. Coordinates are the least, middle and second-largest prime logs. -/
def boxCap (L t h : ℝ) (lo hi : Fin 3 → ℝ) : ℝ :=
  min (hi 0) (max 0 (min (L-t+∑ i, hi i)
    (min (t+h-L-lo 2) (2*t-(∑ i, lo i)+2*h-2*L))))

/-- The upper debit cap is nonnegative on actual positive log cells. -/
theorem boxCap_nonneg (L t h : ℝ) {lo hi : Fin 3 → ℝ} (hhi : 0 ≤ hi 0) :
    0 ≤ boxCap L t h lo hi := le_min hhi (le_max_left _ _)

private theorem product_three (p : Fin 3 → ℕ) :
    ∏ i, p i = p 2*(p 1*p 0) := by
  simp only [Fin.prod_univ_three]
  ring

private theorem tuple_bounds {lo H : Fin 3 → ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i))) :
    (∀ i, (p i).Prime) ∧ (∏ i, p i) ≠ 0 ∧
      (∑ i, lo i) ≤ Real.log (∏ i, p i : ℕ) ∧
      Real.log (∏ i, p i : ℕ) ≤ ∑ i, (lo i+H i) := by
  have hpr (i : Fin 3) := (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1
  have he : Real.log (∏ i, p i : ℕ) = ∑ i, Real.log (p i) := by
    rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hpr i).ne_zero)]
  refine ⟨hpr,Finset.prod_ne_zero_iff.mpr (fun i _ => (hpr i).ne_zero),?_,?_⟩
  · rw [he]
    exact Finset.sum_le_sum (fun i _ => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).2.1.le)
  · rw [he]
    exact Finset.sum_le_sum (fun i _ => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).2.2)

private theorem tuple_ordered {lo H : Fin 3 → ℝ}
    (horder : ∀ i j, i < j → lo i+H i ≤ lo j) {p : Fin 3 → ℕ}
    (hp : p ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i))) :
    p 0 < p 1 ∧ p 1 < p 2 := by
  have hh (i j : Fin 3) (hij : i < j) : p i < p j := by
    have hl := logPrimes_bounds (Fintype.mem_piFinset.mp hp i)
    have hu := logPrimes_bounds (Fintype.mem_piFinset.mp hp j)
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hl.1.pos)
      (by exact_mod_cast hu.1.pos)).mp (hl.2.2.trans_lt ((horder i j hij).trans_lt hu.2.1))
  exact ⟨hh 0 1 (by decide),hh 1 2 (by decide)⟩

/-- The three exact coefficient obstructions are bounded across an entire
outer-prime cell without discarding any of them. -/
theorem windowCap_le_boxCap {L t h : ℝ} {lo H : Fin 3 → ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i))) :
    fourWindowCap L (t-Real.log (∏ i, p i : ℕ)) h t (p 2) (p 0) ≤
      boxCap L t h lo (fun i => lo i+H i) := by
  have hb := tuple_bounds hp
  have hl (i : Fin 3) := logPrimes_bounds (Fintype.mem_piFinset.mp hp i)
  unfold fourWindowCap boxCap
  apply min_le_min (hl 0).2.2
  apply max_le_max le_rfl
  apply min_le_min
  · linarith [hb.2.2.2]
  · apply min_le_min
    · linarith [(hl 2).2.1]
    · linarith [hb.2.2.1]

private theorem cofactor_reciprocal_eq {lo H : Fin 3 → ℝ}
    (horder : ∀ i j, i < j → lo i+H i ≤ lo j) :
    (∑ m ∈ (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
        (fun p => (∏ i, p i : ℕ)), (m : ℝ)⁻¹) =
      ∑ p ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i)), ∏ i, (p i : ℝ)⁻¹ := by
  rw [Finset.sum_image (ordered_macro_product_injective horder)]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.cast_prod,Finset.prod_inv_distrib]

/-- A whole adverse four-prime cell costs at most 501/500 of its explicit
Darboux debit. Any original support or phase subselection remains literal;
only negative-cosine labels are charged, and positive credits are retained. -/
theorem eventually_four_cell_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 3 → ℝ) (A : Finset ℕ)
      (S : ℕ → Finset ℕ) (L t y : ℝ),
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∀ i j, i < j → lo i+H i ≤ lo j) → 0 < L → L ≤ t → 2*(t+h) ≤ 3*L →
      α*N ≤ t-(∑ i, (lo i+H i)) → lo 2+H 2 ≤ t-(∑ i, (lo i+H i)) →
      let M := (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image (fun p => (∏ i, p i : ℕ))
      (∀ m ∈ M, S m ⊆ logPrimes (t-Real.log m) h) →
      (∀ m ∈ M, ∀ p ∈ S m, Real.cos (y*Real.log (m*p : ℕ)) ≤ 0) →
      -((501/500 : ℝ)*((t+h)/L)*boxCap L t h lo (fun i => lo i+H i)*
        (max 0 (-Real.cos (y*t))+|y| * h)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
        (h/(t-∑ i, (lo i+H i)))*(∏ i, H i/lo i)) ≤
      (∑ n ∈ M.biUnion (fun m => (S m).image (fun p => m*p)),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_four_cofactor_floor hh hhu hα,
    eventually_macro_tuple_bounds hα hβ (by decide : 3 ≤ 4),
    eventually_ge_atTop (1 : ℕ)] with N hbound hmass hN lo H A S L t y
      hlo hH horder hL hLt hTcut hmin hqp
  dsimp only
  intro hS hcos
  let T := Fintype.piFinset (fun i => logPrimes (lo i) (H i))
  let M := T.image (fun p => (∏ i, p i : ℕ))
  let C := boxCap L t h lo (fun i => lo i+H i)
  let vmin := t-∑ i, (lo i+H i)
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  let Z := (10001/10000 : ℝ)*((t+h)/L)*(max 0 (-Real.cos (y*t))+|y| * h)*V*h
  let B := Z*(C/vmin)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo0 (i : Fin 3) : 0 < lo i := by nlinarith [hlo i]
  have hH0 (i : Fin 3) : 0 < H i := by nlinarith [hH i]
  have ht : 0 < t := hL.trans_le hLt
  have hvmin : 0 < vmin := by dsimp [vmin]; nlinarith
  have hC : 0 ≤ C := boxCap_nonneg L t h (by linarith [hlo0 0,hH0 0])
  have hφ : 0 ≤ max 0 (-Real.cos (y*t))+|y| * h :=
    add_nonneg (le_max_left _ _) (mul_nonneg (abs_nonneg y) hh.le)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hB : 0 ≤ B := mul_nonneg hZ (div_nonneg hC hvmin.le)
  have hm : ∀ m ∈ M, m ≠ 0 := by
    intro m hm'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm'
    exact (tuple_bounds hp).2.1
  have hdata (p : Fin 3 → ℕ) (hp : p ∈ T) :
      α*N ≤ t-Real.log (∏ i, p i : ℕ) ∧
      Real.log (p 2) ≤ t-Real.log (∏ i, p i : ℕ) := by
    have hb := tuple_bounds hp
    exact ⟨by linarith [hb.2.2.2],by
      linarith [(logPrimes_bounds (Fintype.mem_piFinset.mp hp 2)).2.2,hb.2.2.2]⟩
  have hpoint (m : ℕ) (hm' : m ∈ M) :
      -(B*(m : ℝ)⁻¹) ≤ (∑ p ∈ S m, f (m*p)).re := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm'
    have hb := tuple_bounds hp
    have ho := tuple_ordered horder hp
    have hd := hdata p hp
    have he := product_three p
    have hlow := hbound A (S (∏ i, p i)) (p 2) (p 1) (p 0) t L y
      (hb.1 2) (hb.1 1) (hb.1 0) ho.2 ho.1 hL hLt hTcut
      (by simpa only [← he] using hd.1) (by simpa only [← he] using hd.2)
      (by simpa only [← he] using hS _ hm') (by simpa only [← he] using hcos _ hm')
    rw [← he] at hlow
    have hv0 : 0 < t-Real.log (∏ i, p i : ℕ) := by nlinarith [hd.1]
    have hcap := windowCap_le_boxCap (L := L) (t := t) (h := h) hp
    have hratio :
        fourWindowCap L (t-Real.log (∏ i, p i : ℕ)) h t (p 2) (p 0)/
          (t-Real.log (∏ i, p i : ℕ)) ≤ C/vmin := by
      exact (div_le_div_of_nonneg_right hcap hv0.le).trans
        (div_le_div_of_nonneg_left hC hvmin (by dsimp [vmin]; linarith [hb.2.2.2]))
    have hscale := neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hZ)
      (inv_nonneg.mpr (Nat.cast_nonneg (∏ i, p i))))
    apply hscale.trans
    calc
      _ = -(((((t+h)/L)*fourWindowCap L (t-Real.log (∏ i, p i : ℕ)) h t (p 2) (p 0)*
          (max 0 (-Real.cos (y*t))+|y| * h))*(Real.exp (-t/2)*(t+h)^N/N.factorial)/
          ((∏ i, p i : ℕ) : ℝ))*((10001/10000 : ℝ)*h/(t-Real.log (∏ i, p i : ℕ)))) := by
        dsimp [Z,V]
        ring
      _ ≤ _ := hlow
  have hP : ∀ m ∈ M, ∀ p ∈ S m,
      p.Prime ∧ ∀ r : ℕ, r.Prime → r ∣ m → r < p := by
    intro m hm' p hp
    have hpB := logPrimes_bounds (hS m hm' hp)
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm'
    have hb := tuple_bounds hv
    have ho := tuple_ordered horder hv
    have hd := hdata v hv
    have hqp' : v 2 < p := by
      exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (hb.1 2).pos)
        (by exact_mod_cast hpB.1.pos)).mp (hd.2.trans_lt hpB.2.1)
    refine ⟨hpB.1,?_⟩
    intro r hr hrd
    rw [product_three v] at hrd
    rcases hr.dvd_mul.mp hrd with hrq | hrar
    · have he := (Nat.prime_dvd_prime_iff_eq hr (hb.1 2)).mp hrq
      omega
    rcases hr.dvd_mul.mp hrar with hra | hrr
    · have he := (Nat.prime_dvd_prime_iff_eq hr (hb.1 1)).mp hra
      omega
    · have he := (Nat.prime_dvd_prime_iff_eq hr (hb.1 0)).mp hrr
      omega
  have hpop : (∑ m ∈ M, (m : ℝ)⁻¹) ≤ (1001/1000 : ℝ)*(∏ i, H i/lo i) := by
    rw [cofactor_reciprocal_eq horder]
    exact (hmass lo H hlo hH).2
  have hmain : -(B*((1001/1000 : ℝ)*(∏ i, H i/lo i))) ≤
      (∑ n ∈ M.biUnion (fun m => (S m).image (fun p => m*p)), f n).re := by
    apply (neg_le_neg (mul_le_mul_of_nonneg_left hpop hB)).trans
    rw [Finset.mul_sum,← Finset.sum_neg_distrib,sum_owned_products M S f hm hP,Complex.re_sum]
    exact Finset.sum_le_sum hpoint
  have hprod : 0 ≤ ∏ i, H i/lo i :=
    Finset.prod_nonneg (fun i _ => div_nonneg (hH0 i).le (hlo0 i).le)
  have hfactor := neg_le_neg (mul_le_mul_of_nonneg_right
    (by norm_num : (10001/10000 : ℝ)*(1001/1000) ≤ 501/500)
    (show 0 ≤ ((t+h)/L)*C*(max 0 (-Real.cos (y*t))+|y| * h)*V*(h/vmin)*
      (∏ i, H i/lo i) by positivity))
  apply le_trans _ hmain
  convert hfactor using 1 <;> dsimp [B,Z,V,C,vmin] <;> ring


/-- The actual adverse last-prime selection. The original carrier support,
positive coefficient and negative cosine are all retained as literal masks. -/
def adversePrimes (S : Finset ℕ) (L t h y : ℝ) (m : ℕ) : Finset ℕ :=
  (logPrimes (t-Real.log m) h).filter (fun p =>
    m*p ∈ S ∧ 0 < (SquarefreeVaughanLogSource.coefficient L (m*p)).re ∧
      Real.cos (y*Real.log (m*p : ℕ)) ≤ 0)

/-- The selected adverse four-prime population, with unique largest-prime
ownership and the entire original support predicate. -/
def adverseCell (S : Finset ℕ) (L t h y : ℝ) (lo H : Fin 3 → ℝ) : Finset ℕ :=
  ((Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
    (fun p => (∏ i, p i : ℕ))).biUnion
      (fun m => (adversePrimes S L t h y m).image (fun p => m*p))

/-- The explicit Darboux debit includes the upper counting cost 501/500,
the literal radial kernel and the common phase envelope. -/
def cellDebit (N : ℕ) (L t h y : ℝ) (lo H : Fin 3 → ℝ) : ℝ :=
  (501/500 : ℝ)*((t+h)/L)*boxCap L t h lo (fun i => lo i+H i)*
    (max 0 (-Real.cos (y*t))+|y| * h)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
    (h/(t-∑ i, (lo i+H i)))*(∏ i, H i/lo i)

/-- No element outside the original finite carrier is introduced. -/
theorem adverseCell_subset (S : Finset ℕ) (L t h y : ℝ) (lo H : Fin 3 → ℝ) :
    adverseCell S L t h y lo H ⊆ S := by
  intro n hn
  obtain ⟨m,_hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  exact (Finset.mem_filter.mp hp).2.1

/-- Every selected atom is adverse. Overlapping debit covers can therefore
only overpay; they cannot create fictitious favorable credit. -/
theorem adverseCell_atom_nonpos (S A : Finset ℕ) (N : ℕ) (L t h y : ℝ)
    (lo H : Fin 3 → ℝ) {n : ℕ} (hn : n ∈ adverseCell S L t h y lo H) :
    (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤ 0 := by
  obtain ⟨m,_hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hsign := (Finset.mem_filter.mp hp).2.2
  rw [re_residual_atom]
  exact mul_nonpos_of_nonneg_of_nonpos (weight_nonneg A N _)
    (mul_nonpos_of_nonneg_of_nonpos hsign.1.le hsign.2)

/-- The adverse cell has exactly four prime factors, independently of any
phase or hypothetical zero. -/
theorem adverseCell_count (S : Finset ℕ) (L t h y : ℝ) {lo H : Fin 3 → ℝ}
    (horder : ∀ i j, i < j → lo i+H i ≤ lo j)
    (hqp : lo 2+H 2 ≤ t-(∑ i, (lo i+H i)))
    {n : ℕ} (hn : n ∈ adverseCell S L t h y lo H) : n.primeFactors.card = 4 := by
  obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hpB := logPrimes_bounds (Finset.mem_filter.mp hp).1
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  have hb := tuple_bounds hv
  have ho := tuple_ordered horder hv
  have hqp' : v 2 < p := by
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (hb.1 2).pos)
      (by exact_mod_cast hpB.1.pos)).mp (show Real.log (v 2) < Real.log p by
        linarith [(logPrimes_bounds (Fintype.mem_piFinset.mp hv 2)).2.2,hb.2.2.2,hpB.2.1])
  rw [product_three v]
  have he : ((v 2*(v 1*v 0))*p).primeFactors = {p,v 2,v 1,v 0} := by
    simp [Nat.primeFactors_mul,hpB.1.ne_zero,(hb.1 0).ne_zero,(hb.1 1).ne_zero,
      (hb.1 2).ne_zero,hpB.1.primeFactors,(hb.1 0).primeFactors,(hb.1 1).primeFactors,
      (hb.1 2).primeFactors,Finset.insert_comm]
    ext x
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  simp [he,hqp'.ne',ho.2.ne',ho.1.ne',(ho.2.trans hqp').ne',
    (ho.1.trans ho.2).ne',(ho.1.trans (ho.2.trans hqp')).ne']

/-- Counting and the exact coefficient caps give a floor for the literal
adverse cell, without an assumed signed arithmetic estimate. -/
theorem eventually_adverse_cell_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 3 → ℝ) (A S : Finset ℕ) (L t y : ℝ),
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∀ i j, i < j → lo i+H i ≤ lo j) → 0 < L → L ≤ t → 2*(t+h) ≤ 3*L →
      α*N ≤ t-(∑ i, (lo i+H i)) → lo 2+H 2 ≤ t-(∑ i, (lo i+H i)) →
      -cellDebit N L t h y lo H ≤
      (∑ n ∈ adverseCell S L t h y lo H,
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_four_cell_floor hh hhu hα hβ]
    with N hN lo H A S L t y hlo hH horder hL hLt hTcut hmin hqp
  exact hN lo H A (adversePrimes S L t h y) L t y hlo hH horder hL hLt hTcut hmin hqp
    (fun _ _ => Finset.filter_subset _ _) (fun _ _ _ hp => (Finset.mem_filter.mp hp).2.2.2)

/-- The moving literal length satisfies the four-prime coefficient chamber
uniformly throughout each selected core phase interval. -/
theorem eventually_core_length_chamber {u h : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      SquarefreeVaughanLogSource.length u N ≤ t ∧
        2*(t+h) ≤ 3*SquarefreeVaughanLogSource.length u N := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 137/200) hroom
  filter_upwards [hlength,eventually_ge_atTop (2 : ℕ)] with N hL hN t htlo hthi
  have hupper := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  constructor <;> nlinarith [Real.log_two_lt_d9]

/-- An independent adverse-cell floor inside the actual core, keeping all
unselected labels signed. The current moment, moving length, allocation,
positive coefficient, negative phase and original masks remain literal. -/
theorem eventually_four_cell_core_floor {u h α β : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ j : ℕ in atTop, ∀ (lo H : Fin 3 → ℝ) (t y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D := adverseCell S L t h y lo H
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∀ i j, i < j → lo i+H i ≤ lo j) →
      α*N ≤ t-(∑ i, (lo i+H i)) → lo 2+H 2 ≤ t-(∑ i, (lo i+H i)) →
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (∑ n ∈ S\D,
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        cellDebit N L t h y lo H ≤ (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (eventually_adverse_cell_floor hh hhu hα hβ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_length_chamber hu hU)] with j hbound hlength lo H t y
  dsimp only
  intro hlo hH horder hmin hqp htlo hthi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hch := hlength t htlo hthi
  have hfloor := hbound lo H A S L t y hlo hH horder
    (SquarefreeVaughanLogSource.length_pos u N) hch.1 hch.2 hmin hqp
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) (adverseCell_subset S L t h y lo H))
  rw [Complex.add_re] at he
  change _ ≤ (∑ n ∈ S, f n).re
  linarith


/-- Every positive four-prime coefficient has a uniform gap between its
largest and second-largest prime in the literal core cutoff chamber. -/
theorem positive_four_top_gap {p q a r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hr : r.Prime)
    (hra : r < a) (haq : a < q) (hqp : q < p)
    (hs : Squarefree (p*(q*(a*r)))) {L : ℝ} (hL : 0 < L)
    (hLt : L ≤ Real.log (p*(q*(a*r)) : ℕ))
    (hTc : 2*Real.log (p*(q*(a*r)) : ℕ) ≤ 3*L)
    (hcut : (693/1015 : ℝ)*Real.log (p*(q*(a*r)) : ℕ) ≤ L)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L (p*(q*(a*r)))).re) :
    (7/145 : ℝ)*Real.log (p*(q*(a*r)) : ℕ) < Real.log p-Real.log q := by
  have hg := ZetaRieszOrderedCapacity.positive_four_geometry hp hq ha hr hra haq hqp
    hs hL hLt hTc hpos
  linarith [hg.1,hg.2.1]

/-- The largest-prime ordering boundary has no adverse negative-cosine
contribution at all. The exact coefficient sign pays it pointwise. -/
theorem re_four_nonneg_of_top_gap (A : Finset ℕ) (N : ℕ) {p q a r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hr : r.Prime)
    (hra : r < a) (haq : a < q) (hqp : q < p)
    (hs : Squarefree (p*(q*(a*r)))) {L y : ℝ} (hL : 0 < L)
    (hLt : L ≤ Real.log (p*(q*(a*r)) : ℕ))
    (hTc : 2*Real.log (p*(q*(a*r)) : ℕ) ≤ 3*L)
    (hcut : (693/1015 : ℝ)*Real.log (p*(q*(a*r)) : ℕ) ≤ L)
    (hgap : Real.log p-Real.log q ≤ (7/145 : ℝ)*Real.log (p*(q*(a*r)) : ℕ))
    (hcos : Real.cos (y*Real.log (p*(q*(a*r)) : ℕ)) ≤ 0) :
    0 ≤ (residualCoefficient A L N (p*(q*(a*r)))*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(a*r)))).re := by
  have hc : (SquarefreeVaughanLogSource.coefficient L (p*(q*(a*r)))).re ≤ 0 := by
    by_contra hn
    exact (not_lt_of_ge hgap) (positive_four_top_gap hp hq ha hr hra haq hqp hs
      hL hLt hTc hcut (lt_of_not_ge hn))
  rw [re_residual_atom]
  exact mul_nonneg (weight_nonneg A N _) (mul_nonneg_of_nonpos_of_nonpos hc hcos)

/-- Actual prime ordering can be retained as a last-prime mask. No
separation between the whole final-prime interval and the cofactor is needed
for the adverse signed floor. -/
theorem eventually_ordered_cofactor_floor {h α : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ (A S : Finset ℕ) (q a r : ℕ) (t L y : ℝ),
      q.Prime → a.Prime → r.Prime → a < q → r < a →
      let m := q*(a*r)
      let v := t-Real.log m
      0 < L → L ≤ t → 2*(t+h) ≤ 3*L → α*N ≤ v →
      S ⊆ logPrimes v h → (∀ p ∈ S, q < p) → (∀ p ∈ S, Real.cos (y*Real.log (m*p : ℕ)) ≤ 0) →
      -(((((t+h)/L)*fourWindowCap L v h t q r*(max 0 (-Real.cos (y*t))+|y| * h))*
          (Real.exp (-t/2)*(t+h)^N/N.factorial)/(m : ℝ))*
        ((10001/10000 : ℝ)*h/v)) ≤
      (∑ p ∈ S,
        residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re := by
  filter_upwards [eventually_cofactor_floor hh hhu hα]
    with N hN A S q a r t L y hq ha hr haq hra
  dsimp only
  intro hL hLt hTcut hv hS hqpS hcos
  let m := q*(a*r)
  have hm : m ≠ 0 := mul_ne_zero hq.ne_zero (mul_ne_zero ha.ne_zero hr.ne_zero)
  have ht : 0 < t := hL.trans_le hLt
  apply hN m t L y _ A S hm hv (by
    exact mul_nonneg (mul_nonneg (div_nonneg (by linarith) hL.le)
      (fourWindowCap_nonneg _ _ _ _ _ _))
      (add_nonneg (le_max_left _ _) (mul_nonneg (abs_nonneg y) hh.le))) hS
  intro p hp
  have hb := logPrimes_bounds (hS hp)
  have hqp : q < p := hqpS p hp
  have hs := squarefree_four_of_order hb.1 hq ha hr hqp haq hra
  have he : m*p = p*(q*(a*r)) := Nat.mul_comm _ _
  have hprod := product_log_bounds hm (hS hp)
  have hc := four_positive_window_upper hb.1 hq ha hr hra haq hqp hs hL
    (show L ≤ Real.log (p*(q*(a*r)) : ℕ) by rw [← he]; linarith [hprod.2.1])
    (show 2*Real.log (p*(q*(a*r)) : ℕ) ≤ 3*L by rw [← he]; linarith [hprod.2.2])
    hb.2.1.le hb.2.2 (show Real.log (p*(q*(a*r)) : ℕ) ≤ t+h by
      rw [← he]; exact hprod.2.2)
  rw [← he] at hc
  exact negative_phase_score_floor A N (m*p)
    (mul_nonneg (div_nonneg (by linarith) hL.le) (fourWindowCap_nonneg _ _ _ _ _ _))
    hc (hcos p hp) (cofactor_phase_upper hm hh.le (hS hp))


/-- Strictly ordered tuples in possibly overlapping cofactor log windows.
This includes cells crossing either middle-prime ordering boundary. -/
def orderedTuples (lo H : Fin 3 → ℝ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).filter
    (fun p => p 0 < p 1 ∧ p 1 < p 2)

/-- The original adverse selection with literal largest-prime ownership. -/
def boundaryPrimes (S : Finset ℕ) (L t h y : ℝ) (m : ℕ) : Finset ℕ :=
  (adversePrimes S L t h y m).filter (fun p => ∀ q ∈ m.primeFactors, q < p)

/-- An adverse cell with all order crossings retained through exact
ordering predicates, rather than omitted by endpoint separation. -/
def boundaryCell (S : Finset ℕ) (L t h y : ℝ) (lo H : Fin 3 → ℝ) : Finset ℕ :=
  ((orderedTuples lo H).image (fun p => (∏ i, p i : ℕ))).biUnion
    (fun m => (boundaryPrimes S L t h y m).image (fun p => m*p))

private theorem strictMono_three {v : Fin 3 → ℕ} (h : v 0 < v 1 ∧ v 1 < v 2) :
    StrictMono v := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact h.1
  · exact h.2

private theorem orderedTuples_product_injective (lo H : Fin 3 → ℝ) :
    Set.InjOn (fun p : Fin 3 → ℕ => ∏ i, p i) (orderedTuples lo H : Set _) := by
  intro p hp q hq he
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  exact ordered_prime_product_eq (tuple_bounds hp'.1).1 (tuple_bounds hq'.1).1
    (strictMono_three hp'.2) (strictMono_three hq'.2) he

/-- Harmonic upper counting keeps every ordered tuple in a crossing cell.
Dropping ordering enlarges only this nonnegative upper population budget. -/
theorem ordered_cofactor_reciprocal_le (lo H : Fin 3 → ℝ) :
    (∑ m ∈ (orderedTuples lo H).image (fun p => (∏ i, p i : ℕ)), (m : ℝ)⁻¹) ≤
      ∑ p ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i)), ∏ i, (p i : ℝ)⁻¹ := by
  rw [Finset.sum_image (orderedTuples_product_injective lo H)]
  have he : (∑ p ∈ orderedTuples lo H, ((∏ i, p i : ℕ) : ℝ)⁻¹) =
      ∑ p ∈ orderedTuples lo H, ∏ i, (p i : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_prod,Finset.prod_inv_distrib]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg (p i))))

/-- Every crossing-cell label is in the original finite support. -/
theorem boundaryCell_subset (S : Finset ℕ) (L t h y : ℝ) (lo H : Fin 3 → ℝ) :
    boundaryCell S L t h y lo H ⊆ S := by
  intro n hn
  obtain ⟨m,_hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1

/-- All selected crossing-cell atoms are nonpositive, so upper covers may
overlap without spending a favorable supply twice. -/
theorem boundaryCell_atom_nonpos (S A : Finset ℕ) (N : ℕ) (L t h y : ℝ)
    (lo H : Fin 3 → ℝ) {n : ℕ} (hn : n ∈ boundaryCell S L t h y lo H) :
    (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤ 0 := by
  obtain ⟨m,_hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hsign := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
  rw [re_residual_atom]
  exact mul_nonpos_of_nonneg_of_nonpos (weight_nonneg A N _)
    (mul_nonpos_of_nonneg_of_nonpos hsign.1.le hsign.2)



private theorem eventually_ordered_cell_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 3 → ℝ) (A : Finset ℕ)
      (S : ℕ → Finset ℕ) (L t y : ℝ),
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      0 < L → L ≤ t → 2*(t+h) ≤ 3*L →
      α*N ≤ t-(∑ i, (lo i+H i)) →
      let M := (orderedTuples lo H).image (fun p => (∏ i, p i : ℕ))
      (∀ m ∈ M, S m ⊆ logPrimes (t-Real.log m) h) →
      (∀ m ∈ M, ∀ p ∈ S m, ∀ q ∈ m.primeFactors, q < p) →
      (∀ m ∈ M, ∀ p ∈ S m, Real.cos (y*Real.log (m*p : ℕ)) ≤ 0) →
      -((501/500 : ℝ)*((t+h)/L)*boxCap L t h lo (fun i => lo i+H i)*
        (max 0 (-Real.cos (y*t))+|y| * h)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
        (h/(t-∑ i, (lo i+H i)))*(∏ i, H i/lo i)) ≤
      (∑ n ∈ M.biUnion (fun m => (S m).image (fun p => m*p)),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_ordered_cofactor_floor hh hhu hα,
    eventually_macro_tuple_bounds hα hβ (by decide : 3 ≤ 4),
    eventually_ge_atTop (1 : ℕ)] with N hbound hmass hN lo H A S L t y
      hlo hH hL hLt hTcut hmin
  dsimp only
  intro hS howner hcos
  let T := orderedTuples lo H
  let M := T.image (fun p => (∏ i, p i : ℕ))
  let C := boxCap L t h lo (fun i => lo i+H i)
  let vmin := t-∑ i, (lo i+H i)
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  let Z := (10001/10000 : ℝ)*((t+h)/L)*(max 0 (-Real.cos (y*t))+|y| * h)*V*h
  let B := Z*(C/vmin)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo0 (i : Fin 3) : 0 < lo i := by nlinarith [hlo i]
  have hH0 (i : Fin 3) : 0 < H i := by nlinarith [hH i]
  have ht : 0 < t := hL.trans_le hLt
  have hvmin : 0 < vmin := by dsimp [vmin]; nlinarith
  have hC : 0 ≤ C := boxCap_nonneg L t h (by linarith [hlo0 0,hH0 0])
  have hφ : 0 ≤ max 0 (-Real.cos (y*t))+|y| * h :=
    add_nonneg (le_max_left _ _) (mul_nonneg (abs_nonneg y) hh.le)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hB : 0 ≤ B := mul_nonneg hZ (div_nonneg hC hvmin.le)
  have hm : ∀ m ∈ M, m ≠ 0 := by
    intro m hm'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm'
    exact (tuple_bounds (Finset.mem_filter.mp hp).1).2.1
  have hdata (p : Fin 3 → ℕ) (hp : p ∈ T) :
      α*N ≤ t-Real.log (∏ i, p i : ℕ) := by
    have hb := tuple_bounds (Finset.mem_filter.mp hp).1
    linarith [hb.2.2.2]
  have hpoint (m : ℕ) (hm' : m ∈ M) :
      -(B*(m : ℝ)⁻¹) ≤ (∑ p ∈ S m, f (m*p)).re := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm'
    have hp0 := (Finset.mem_filter.mp hp).1
    have hb := tuple_bounds hp0
    have ho := (Finset.mem_filter.mp hp).2
    have hd := hdata p hp
    have he := product_three p
    have hlow := hbound A (S (∏ i, p i)) (p 2) (p 1) (p 0) t L y
      (hb.1 2) (hb.1 1) (hb.1 0) ho.2 ho.1 hL hLt hTcut
      (by simpa only [← he] using hd)
      (by simpa only [← he] using hS _ hm') (by
        intro q hq
        have hq' : q ∈ S (∏ i, p i) := by simpa only [he] using hq
        exact howner _ hm' q hq' (p 2) (Nat.mem_primeFactors.mpr
          ⟨hb.1 2,Finset.dvd_prod_of_mem _ (Finset.mem_univ 2),hb.2.1⟩))
      (by simpa only [← he] using hcos _ hm')
    rw [← he] at hlow
    have hv0 : 0 < t-Real.log (∏ i, p i : ℕ) := by nlinarith [hd]
    have hcap := windowCap_le_boxCap (L := L) (t := t) (h := h) hp0
    have hratio :
        fourWindowCap L (t-Real.log (∏ i, p i : ℕ)) h t (p 2) (p 0)/
          (t-Real.log (∏ i, p i : ℕ)) ≤ C/vmin := by
      exact (div_le_div_of_nonneg_right hcap hv0.le).trans
        (div_le_div_of_nonneg_left hC hvmin (by dsimp [vmin]; linarith [hb.2.2.2]))
    have hscale := neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hZ)
      (inv_nonneg.mpr (Nat.cast_nonneg (∏ i, p i))))
    apply hscale.trans
    calc
      _ = -(((((t+h)/L)*fourWindowCap L (t-Real.log (∏ i, p i : ℕ)) h t (p 2) (p 0)*
          (max 0 (-Real.cos (y*t))+|y| * h))*(Real.exp (-t/2)*(t+h)^N/N.factorial)/
          ((∏ i, p i : ℕ) : ℝ))*((10001/10000 : ℝ)*h/(t-Real.log (∏ i, p i : ℕ)))) := by
        dsimp [Z,V]
        ring
      _ ≤ _ := hlow
  have hP : ∀ m ∈ M, ∀ p ∈ S m,
      p.Prime ∧ ∀ r : ℕ, r.Prime → r ∣ m → r < p := by
    intro m hm' p hp
    refine ⟨(logPrimes_bounds (hS m hm' hp)).1,?_⟩
    intro r hr hrd
    exact howner m hm' p hp r (Nat.mem_primeFactors.mpr ⟨hr,hrd,hm m hm'⟩)
  have hpop : (∑ m ∈ M, (m : ℝ)⁻¹) ≤ (1001/1000 : ℝ)*(∏ i, H i/lo i) := by
    exact (ordered_cofactor_reciprocal_le lo H).trans (hmass lo H hlo hH).2
  have hmain : -(B*((1001/1000 : ℝ)*(∏ i, H i/lo i))) ≤
      (∑ n ∈ M.biUnion (fun m => (S m).image (fun p => m*p)), f n).re := by
    apply (neg_le_neg (mul_le_mul_of_nonneg_left hpop hB)).trans
    rw [Finset.mul_sum,← Finset.sum_neg_distrib,sum_owned_products M S f hm hP,Complex.re_sum]
    exact Finset.sum_le_sum hpoint
  have hprod : 0 ≤ ∏ i, H i/lo i :=
    Finset.prod_nonneg (fun i _ => div_nonneg (hH0 i).le (hlo0 i).le)
  have hfactor := neg_le_neg (mul_le_mul_of_nonneg_right
    (by norm_num : (10001/10000 : ℝ)*(1001/1000) ≤ 501/500)
    (show 0 ≤ ((t+h)/L)*C*(max 0 (-Real.cos (y*t))+|y| * h)*V*(h/vmin)*
      (∏ i, H i/lo i) by positivity))
  apply le_trans _ hmain
  convert hfactor using 1 <;> dsimp [B,Z,V,C,vmin] <;> ring


/-- The same explicit debit bounds an entire cell crossing prime-order
boundaries. Every original adverse atom and its exact ordering mask is
retained; no interval-separation hypothesis or boundary error is required. -/
theorem eventually_boundary_cell_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 3 → ℝ) (A S : Finset ℕ) (L t y : ℝ),
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      0 < L → L ≤ t → 2*(t+h) ≤ 3*L →
      α*N ≤ t-(∑ i, (lo i+H i)) →
      -cellDebit N L t h y lo H ≤
      (∑ n ∈ boundaryCell S L t h y lo H,
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_ordered_cell_floor hh hhu hα hβ]
    with N hN lo H A S L t y hlo hH hL hLt hTcut hmin
  exact hN lo H A (boundaryPrimes S L t h y) L t y hlo hH hL hLt hTcut hmin
    (fun _ _ _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
    (fun _ _ _ hp => (Finset.mem_filter.mp hp).2)
    (fun _ _ _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.2)


/-- Crossing-cell labels have exactly four prime factors; the literal
ordering predicates, not endpoint separation, establish distinctness. -/
theorem boundaryCell_count (S : Finset ℕ) (L t h y : ℝ) {lo H : Fin 3 → ℝ}
    {n : ℕ} (hn : n ∈ boundaryCell S L t h y lo H) : n.primeFactors.card = 4 := by
  obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hpB := logPrimes_bounds (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  have hb := tuple_bounds (Finset.mem_filter.mp hv).1
  have ho := (Finset.mem_filter.mp hv).2
  have hqp' : v 2 < p := (Finset.mem_filter.mp hp).2 (v 2)
    (Nat.mem_primeFactors.mpr
      ⟨hb.1 2,Finset.dvd_prod_of_mem _ (Finset.mem_univ 2),hb.2.1⟩)
  rw [product_three v]
  have he : ((v 2*(v 1*v 0))*p).primeFactors = {p,v 2,v 1,v 0} := by
    simp [Nat.primeFactors_mul,hpB.1.ne_zero,(hb.1 0).ne_zero,(hb.1 1).ne_zero,
      (hb.1 2).ne_zero,hpB.1.primeFactors,(hb.1 0).primeFactors,(hb.1 1).primeFactors,
      (hb.1 2).primeFactors,Finset.insert_comm]
    ext x
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  simp [he,hqp'.ne',ho.2.ne',ho.1.ne',(ho.2.trans hqp').ne',
    (ho.1.trans ho.2).ne',(ho.1.trans (ho.2.trans hqp')).ne']

/-- Every adverse ordered four-prime product in the three log windows is
retained, even when the windows cross an ordering face. -/
theorem mem_boundaryCell (S : Finset ℕ) (L t h y : ℝ) (lo H : Fin 3 → ℝ)
    {v : Fin 3 → ℕ} {p : ℕ}
    (hv : v ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i)))
    (ho : v 0 < v 1 ∧ v 1 < v 2) (hp : p.Prime) (hqp : v 2 < p)
    (hS : (∏ i, v i)*p ∈ S)
    (hTlo : t < Real.log ((∏ i, v i)*p : ℕ))
    (hThi : Real.log ((∏ i, v i)*p : ℕ) ≤ t+h)
    (hc : 0 < (SquarefreeVaughanLogSource.coefficient L ((∏ i, v i)*p)).re)
    (hcos : Real.cos (y*Real.log ((∏ i, v i)*p : ℕ)) ≤ 0) :
    (∏ i, v i)*p ∈ boundaryCell S L t h y lo H := by
  have hb := tuple_bounds hv
  refine Finset.mem_biUnion.mpr ⟨∏ i, v i,
    Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,ho⟩,rfl⟩,
    Finset.mem_image.mpr ⟨p,?_,rfl⟩⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨(mem_logPrimes_iff _ _ _).mpr ⟨hp,?_,?_⟩,hS,hc,hcos⟩
    all_goals
      have he : Real.log ((∏ i, v i)*p : ℕ) = Real.log (∏ i, v i : ℕ)+Real.log p := by
        rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.2.1) (by exact_mod_cast hp.ne_zero)]
      linarith
  · intro q hq
    obtain ⟨hqP,hqd,_⟩ := Nat.mem_primeFactors.mp hq
    rw [product_three v] at hqd
    rcases hqP.dvd_mul.mp hqd with hqv | hqv
    · have he := (Nat.prime_dvd_prime_iff_eq hqP (hb.1 2)).mp hqv
      omega
    rcases hqP.dvd_mul.mp hqv with hqv | hqv
    · have he := (Nat.prime_dvd_prime_iff_eq hqP (hb.1 1)).mp hqv
      omega
    · have he := (Nat.prime_dvd_prime_iff_eq hqP (hb.1 0)).mp hqv
      omega

/-- A squarefree integer with four prime factors has its unique increasing
prime tuple. This supplies ordered cell membership without a factorization
hypothesis on a selected part of the carrier. -/
theorem exists_ordered_four_factorization {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) :
    ∃ v : Fin 4 → ℕ, (∀ i, (v i).Prime) ∧ StrictMono v ∧ n = ∏ i, v i := by
  let v := n.primeFactors.orderEmbOfFin hc
  refine ⟨v,fun i => (Nat.mem_primeFactors.mp (n.primeFactors.orderEmbOfFin_mem hc i)).1,
    v.strictMono,?_⟩
  have he := n.primeFactors.image_orderEmbOfFin_univ hc
  rw [← Nat.prod_primeFactors_of_squarefree hs,← he,Finset.prod_image]
  exact fun _ _ _ _ h => v.injective h

end
end RiemannGaussian.ZetaRieszFourPrimeCells
