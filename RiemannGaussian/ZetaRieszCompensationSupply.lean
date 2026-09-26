/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCompensation
import RiemannGaussian.ZetaRieszAllowancePrimeBoxes
import RiemannGaussian.ZetaRieszPrimeIntervals

/-!
# Actual prime supply in an opposing five-prime box

The fixed logarithmic slopes are 0.04, 0.10, 0.22, 0.54, 1.10.
Every label has the exact original coefficient `-log(n)*log(minFac n)/L`.
The prime number theorem counts actual labels in fixed-width log boxes.
This supplies an opposing population, not a joint phased-carrier floor.
-/

namespace RiemannGaussian.ZetaRieszCompensationSupply
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszParityPacket

/-- The coordinates are in increasing prime order. -/
def slope (i : Fin 5) : ℝ :=
  if i = 0 then 1/25 else if i = 1 then 1/10 else if i = 2 then 11/50
  else if i = 3 then 27/50 else 11/10

/-- Only the largest-prime interval receives the bounded translation. -/
def start (N : ℕ) (v : ℝ) (i : Fin 5) : ℝ :=
  slope i*N + if i = 4 then v else 0

/-- Actual ordinary-prime choices in the five disjoint log intervals. -/
def tuples (N : ℕ) (h v : ℝ) : Finset (Fin 5 → ℕ) :=
  Fintype.piFinset (fun i => logPrimes (start N v i) h)

/-- Distinct integers, with no incidence multiplicity. -/
def products (N : ℕ) (h v : ℝ) : Finset ℕ :=
  (tuples N h v).image (fun p => ∏ i, p i)

theorem slope_pos (i : Fin 5) : 0 < slope i := by
  fin_cases i <;> norm_num [slope, Fin.ext_iff]

theorem slope_gap {i j : Fin 5} (hij : i < j) : slope i+1/1000 < slope j := by
  fin_cases i <;> fin_cases j <;> norm_num [slope, Fin.ext_iff] at *

theorem tuple_bounds {N : ℕ} {h v : ℝ} {p : Fin 5 → ℕ}
    (hp : p ∈ tuples N h v) (i : Fin 5) :
    (p i).Prime ∧ start N v i < Real.log (p i) ∧
      Real.log (p i) ≤ start N v i+h :=
  logPrimes_bounds (Fintype.mem_piFinset.mp hp i)

/-- The finite boxes are disjoint, even across two different tuples. -/
theorem coordinate_order {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p q : Fin 5 → ℕ} (hp : p ∈ tuples N h v) (hq : q ∈ tuples N h v)
    {i j : Fin 5} (hij : i < j) : p i < q j := by
  apply logPrimes_order (a := start N v i) (b := start N v j) _
    (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hq j)
  have hgap := mul_lt_mul_of_pos_right (slope_gap hij)
    (show (0 : ℝ) < N by exact_mod_cast hN)
  dsimp [start]
  split_ifs <;> nlinarith

theorem product_injective {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000) :
    Set.InjOn (fun p : Fin 5 → ℕ => ∏ i, p i) (tuples N h v : Set _) := by
  intro p hp q hq he
  dsimp only at he
  funext i
  have hpi := (tuple_bounds hp i).1
  have hd : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j, _, hj⟩ := (hpi.prime.dvd_finsetProd_iff q).mp hd
  have heq := (Nat.prime_dvd_prime_iff_eq hpi (tuple_bounds hq j).1).mp hj
  have hij : i = j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((coordinate_order hN hv hwidth hp hq hij).ne heq)
    · exact hij
    · exact False.elim ((coordinate_order hN hv hwidth hq hp hij).ne heq.symm)
  simpa only [hij] using heq

theorem products_card {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000) :
    (products N h v).card = ∏ i, (logPrimes (start N v i) h).card := by
  rw [products, Finset.card_image_of_injOn (product_injective hN hv hwidth)]
  simp [tuples]

theorem tuple_squarefree {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p : Fin 5 → ℕ} (hp : p ∈ tuples N h v) : Squarefree (∏ i, p i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    apply Nat.coprime_iff_isRelPrime.mp
    apply (tuple_bounds hp i).1.coprime_iff_not_dvd.mpr
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq (tuple_bounds hp i).1
      (tuple_bounds hp j).1).mp hd
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact (coordinate_order hN hv hwidth hp hp hh).ne he
    · exact (coordinate_order hN hv hwidth hp hp hh).ne he.symm
  · intro i _
    exact (tuple_bounds hp i).1.squarefree

theorem tuple_log {N : ℕ} {h v : ℝ} {p : Fin 5 → ℕ}
    (hp : p ∈ tuples N h v) : Real.log (∏ i, p i : ℕ) = ∑ i, Real.log (p i) := by
  rw [Nat.cast_prod, Real.log_prod]
  intro i _
  exact_mod_cast (tuple_bounds hp i).1.ne_zero

theorem tuple_log_bounds {N : ℕ} {h v : ℝ} {p : Fin 5 → ℕ}
    (hp : p ∈ tuples N h v) :
    2*(N : ℝ)+v < Real.log (∏ i, p i : ℕ) ∧
      Real.log (∏ i, p i : ℕ) ≤ 2*(N : ℝ)+v+5*h := by
  have hl := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin 5)))
    (fun i _ => (tuple_bounds hp i).2.1.le)
    ⟨0, Finset.mem_univ _, (tuple_bounds hp 0).2.1⟩
  have hu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
    (fun i _ => (tuple_bounds hp i).2.2)
  rw [tuple_log hp]
  simp only [Fin.sum_univ_five] at hl hu ⊢
  norm_num [start,slope,Fin.ext_iff] at hl hu
  constructor <;> linarith

theorem tuple_primeFactors {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p : Fin 5 → ℕ} (hp : p ∈ tuples N h v) :
    (∏ i, p i).primeFactors = Finset.univ.image p := by
  have hi : Function.Injective p :=
    (show StrictMono p from fun _ _ hij => coordinate_order hN hv hwidth hp hp hij).injective
  have he := Finset.prod_image (f := fun n : ℕ => n) (s := Finset.univ) hi.injOn
  rw [← he]
  apply Nat.primeFactors_prod
  intro a ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  exact (tuple_bounds hp i).1

/-- Canonical extremes and exact count: the box has no repeated prime factors. -/
theorem tuple_extremes {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p : Fin 5 → ℕ} (hp : p ∈ tuples N h v) :
    (∏ i, p i).primeFactors.card = 5 ∧
      ZetaRieszPrimeEndpoint.largestPrime (∏ i, p i) = p 4 ∧
      (∏ i, p i).minFac = p 0 := by
  have hm : StrictMono p := fun _ _ hij => coordinate_order hN hv hwidth hp hp hij
  have hf := tuple_primeFactors hN hv hwidth hp
  have hs := tuple_squarefree hN hv hwidth hp
  have hn1 : 1 < ∏ i, p i := by
    apply (tuple_bounds hp 0).1.one_lt.trans_le
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero)
      (Finset.dvd_prod_of_mem p (Finset.mem_univ 0))
  refine ⟨?_,?_,?_⟩
  · rw [hf,Finset.card_image_of_injective _ hm.injective]
    simp
  · apply ZetaRieszPrimeIntervals.largestPrime_eq_of_max
    · rw [hf]; exact Finset.mem_image.mpr ⟨4,Finset.mem_univ _,rfl⟩
    · intro a ha
      rw [hf] at ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact hm.monotone (by omega)
  · apply le_antisymm
    · exact Nat.minFac_le_of_dvd (tuple_bounds hp 0).1.two_le
        (Finset.dvd_prod_of_mem p (Finset.mem_univ 0))
    · have hr := (Nat.minFac_prime hn1.ne').mem_primeFactors
        (Nat.minFac_dvd (∏ i, p i)) hs.ne_zero
      rw [hf] at hr
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
      rw [← hi]
      exact hm.monotone (Fin.zero_le i)

/-- This box is strictly inside the existing factorial concentration region. -/
theorem tuple_fullParityBox {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p : Fin 5 → ℕ} (hp : p ∈ tuples N h v) : FullParityBox (∏ i, p i) := by
  have hs := tuple_squarefree hN hv hwidth hp
  obtain ⟨hk,hP,hr⟩ := tuple_extremes hN hv hwidth hp
  obtain ⟨hl,hu⟩ := tuple_log_bounds hp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have b0 := tuple_bounds hp 0
  have b4 := tuple_bounds hp 4
  norm_num [start,slope,Fin.ext_iff] at b0 b4
  have hn1 : 1 < ∏ i, p i := by
    exact_mod_cast (Real.log_pos_iff (Nat.cast_nonneg _)).mp (by linarith :
      0 < Real.log (∏ i, p i : ℕ))
  refine ⟨hs,hn1,by omega,?_,?_,?_,?_,?_⟩
  · rw [hP,tuple_primeFactors hN hv hwidth hp]
    exact Finset.mem_image.mpr ⟨4,Finset.mem_univ _,rfl⟩
  all_goals first | rw [hP] | rw [hr]
  all_goals linarith

/-- The response is exactly a full least-prime logarithm, not just nonpositive. -/
theorem tuple_coefficient {N : ℕ} (hN : 0 < N) {h v L : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    (hLlo : (137/100 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    {p : Fin 5 → ℕ} (hp : p ∈ tuples N h v) :
    SquarefreeVaughanLogSource.coefficient L (∏ i, p i) =
      ((-(Real.log (∏ i, p i : ℕ)/L)*Real.log (p 0) : ℝ) : ℂ) := by
  have hb (i : Fin 5) := tuple_bounds hp i
  have b0 := hb 0; have b1 := hb 1; have b2 := hb 2
  have b3 := hb 3; have b4 := hb 4
  norm_num [start, slope, Fin.ext_iff, Matrix.cons_val] at b0 b1 b2 b3 b4
  have he : (∏ i, p i) = p 4*(p 3*(p 2*(p 1*p 0))) := by
    simp [Fin.prod_univ_succ]; ring
  have hlog : Real.log (p 3*(p 2*(p 1*p 0)) : ℕ) =
      Real.log (p 3)+Real.log (p 2)+Real.log (p 1)+Real.log (p 0) := by
    simp only [Nat.cast_mul]
    rw [Real.log_mul (by exact_mod_cast b3.1.ne_zero)
        (mul_ne_zero (by exact_mod_cast b2.1.ne_zero)
          (mul_ne_zero (by exact_mod_cast b1.1.ne_zero) (by exact_mod_cast b0.1.ne_zero))),
      Real.log_mul (by exact_mod_cast b2.1.ne_zero)
        (mul_ne_zero (by exact_mod_cast b1.1.ne_zero) (by exact_mod_cast b0.1.ne_zero)),
      Real.log_mul (by exact_mod_cast b1.1.ne_zero) (by exact_mod_cast b0.1.ne_zero)]
    ring
  have hg : QuintupleGeometry L (∏ i, p i) (p 4) (p 3) (p 2) (p 1) (p 0) := by
    refine ⟨b4.1,b3.1,b2.1,b1.1,b0.1,?_,?_,?_,?_,he,
      tuple_squarefree hN hv hwidth hp,?_,?_,?_⟩
    · exact coordinate_order hN hv hwidth hp hp (by decide : (3 : Fin 5) < 4)
    · exact coordinate_order hN hv hwidth hp hp (by decide : (2 : Fin 5) < 3)
    · exact coordinate_order hN hv hwidth hp hp (by decide : (1 : Fin 5) < 2)
    · exact coordinate_order hN hv hwidth hp hp (by decide : (0 : Fin 5) < 1)
    · rw [hlog]; linarith
    · linarith
    · dsimp [HingeRegion]
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      exact ⟨by linarith, by linarith, by linarith⟩
  rw [quintuple_coefficient hg, threeHinge_second (Real.log_natCast_nonneg _)]
  · push_cast; ring
  · linarith
  · linarith
  · linarith
  · linarith

/-- A fixed explicit opposing charge at every actual label of the box. -/
theorem tuple_coefficient_le {N : ℕ} (hN : 0 < N) {h v L : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    (hLlo : (137/100 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    {p : Fin 5 → ℕ} (hp : p ∈ tuples N h v) :
    (SquarefreeVaughanLogSource.coefficient L (∏ i, p i)).re ≤ -(2/35 : ℝ)*N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := by linarith
  have hb (i : Fin 5) := (tuple_bounds hp i).2.1
  have hsum : 2*(N : ℝ) ≤ Real.log (∏ i, p i : ℕ) := by
    rw [tuple_log hp]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hb i).le)
    simp only [Fin.sum_univ_five] at h ⊢
    norm_num [start,slope,Fin.ext_iff] at h ⊢
    linarith
  have hr : (N : ℝ)/25 ≤ Real.log (p 0) := by
    have h := hb 0
    norm_num [start,slope,Fin.ext_iff,Matrix.cons_val] at h
    linarith
  have hratio : (10/7 : ℝ) ≤ Real.log (∏ i, p i : ℕ)/L := by
    apply (le_div_iff₀ hL).mpr
    linarith
  rw [tuple_coefficient hN hv hwidth hLlo hLhi hp, Complex.ofReal_re]
  have hh := mul_le_mul hratio hr (by positivity : (0 : ℝ) ≤ N/25)
    (div_nonneg (Real.log_natCast_nonneg _) hL.le)
  nlinarith

/-- The five boxes contain exponentially many distinct actual integers.
No continuum density or phase approximation is used in this count. -/
theorem eventually_products_card_lower {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ C →
      c*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^5 ≤ (products N h v).card := by
  have hi (i : Fin 5) := eventually_logPrimes_card_lower_slope (slope_pos i) hh hC
  choose c hc he using hi
  refine ⟨∏ i, c i, Finset.prod_pos (fun i _ => hc i), ?_⟩
  filter_upwards [Filter.eventually_all.mpr he, eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1000*(h+C))]
    with N hcounts hN hsize v hv hvC
  have hw : h+v ≤ (N : ℝ)/1000 := by linarith
  rw [products_card hN hv hw, Nat.cast_prod]
  have hj (i : Fin 5) : c i*Real.exp (slope i*N)/((N : ℝ)+1) ≤
      ((logPrimes (start N v i) h).card : ℝ) := by
    apply hcounts i
    · dsimp [start]; split_ifs <;> linarith
    · dsimp [start]; split_ifs <;> linarith
  have hprod := Finset.prod_le_prod
    (s := (Finset.univ : Finset (Fin 5)))
    (fun i _ => div_nonneg (mul_nonneg (hc i).le (Real.exp_pos _).le) (by positivity))
    (fun i _ => hj i)
  have hex : (∏ i : Fin 5, Real.exp (slope i*N)) = Real.exp (2*(N : ℝ)) := by
    rw [← Real.exp_sum, ← Finset.sum_mul]
    simp only [Fin.sum_univ_five]
    norm_num [slope,Fin.ext_iff]
  simpa only [Finset.prod_div_distrib, Finset.prod_mul_distrib, hex,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

/-- A bounded translation makes the exact product phase favorable.
The log width depends only on the fixed height and never shrinks with N. -/
theorem exists_negative_phase_window {y : ℝ} (hy : y ≠ 0) :
    ∃ h C : ℝ, 0 < h ∧ 0 ≤ C ∧ ∀ b : ℝ, ∃ v : ℝ,
      0 ≤ v ∧ v ≤ C ∧ ∀ t : ℝ, b+v ≤ t → t ≤ b+v+5*h →
        Real.cos (y*t) ≤ -(1/2 : ℝ) := by
  let z := |y|
  have hz : 0 < z := abs_pos.mpr hy
  obtain ⟨h,C,hh,hC,hphase⟩ := exists_positive_phase_boxes z
  refine ⟨3*h/5,3*C,by positivity,by positivity,?_⟩
  intro b
  obtain ⟨a,ha,hau,hcos⟩ := hphase ((b+Real.pi/z-3*h)/3)
  let v := 3*a+3*h-Real.pi/z-b
  refine ⟨v,by dsimp [v]; linarith,by dsimp [v]; linarith,?_⟩
  intro t ht htu
  have hc := hcos (t+Real.pi/z) (by dsimp [v] at ht; linarith)
    (by dsimp [v] at htu; linarith)
  have he : z*(t+Real.pi/z) = z*t+Real.pi := by field_simp
  rw [he,Real.cos_add_pi] at hc
  have hec : Real.cos (z*t) = Real.cos (y*t) := by
    dsimp [z]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_mul,Real.cos_neg]
  rw [hec] at hc
  linarith

/-- The exact original factorial selection retains at least half the mass
uniformly on this box. No allocation is replaced by its limit. -/
theorem eventually_weight_lower : ∀ᶠ N : ℕ in atTop,
    ∀ h v : ℝ, 0 ≤ v → h+v ≤ (N : ℝ)/1000 →
      ∀ p ∈ tuples N h v, (1/2 : ℝ) ≤ ZetaRieszJointBoundary.weight N (∏ i, p i) := by
  have ht : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)/6000)) atTop (𝓝 0) := by
    have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const
      (by norm_num : (0 : ℝ) < 6000)
    simpa only [neg_div,Function.comp_def] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
  filter_upwards [eventually_ge_atTop 1,ht.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1/12)] with N hN hsmall h v hv hw p hp
  have hb := tuple_fullParityBox hN hv hw hp
  rw [ZetaRieszJointBoundary.weight_eq_rectangle hb]
  have he := ZetaRieszParityOrderTail.rectangleMass_add_omitted hb N
  have hu := (ZetaRieszParityOrderTail.rectangleOmittedMass_bounds hb N).2
  linarith

/-- Actual phased atoms are positive in the translated box, with the
original factorial rectangle retained. This is a subfamily estimate. -/
theorem box_atom_lower {N : ℕ} (hN : 35 ≤ N) {h v C L y : ℝ}
    (_hh : 0 ≤ h) (hv : 0 ≤ v) (hvC : v ≤ C)
    (hwidth : h+v ≤ (N : ℝ)/1000)
    (hLlo : (137/100 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    {p : Fin 5 → ℕ} (hp : p ∈ tuples N h v)
    (hw : (1/2 : ℝ) ≤ ZetaRieszJointBoundary.weight N (∏ i, p i))
    (hcos : Real.cos (y*Real.log (∏ i, p i : ℕ)) ≤ -(1/2 : ℝ)) :
    Real.exp (-(3/2 : ℝ)*(2*N+C+5*h))*(2*N)^N/N.factorial/4 ≤
      (((ZetaRieszJointBoundary.weight N (∏ i, p i) : ℝ) : ℂ)*
        (SquarefreeVaughanLogSource.coefficient L (∏ i, p i)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ i, p i))).re := by
  have hN0 : 0 < N := by omega
  have hc := tuple_coefficient_le hN0 hv hwidth hLlo hLhi hp
  have hNR : (35 : ℝ) ≤ N := by exact_mod_cast hN
  have hc1 : (SquarefreeVaughanLogSource.coefficient L (∏ i, p i)).re ≤ -1 := by linarith
  have hamp := ZetaRieszCosineCarrier.factorial_envelope_nonneg N (∏ i, p i)
  have hpC : (1/2 : ℝ) ≤ (SquarefreeVaughanLogSource.coefficient L (∏ i, p i)).re *
      Real.cos (y*Real.log (∏ i, p i : ℕ)) := by nlinarith
  have hm := mul_le_mul hw hpC (by norm_num : (0 : ℝ) ≤ 1/2) (by linarith :
    0 ≤ ZetaRieszJointBoundary.weight N (∏ i, p i))
  have he := mul_le_mul_of_nonneg_right hm hamp
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    zetaPrimeLogKernel, ← SquarefreeEulerQuadratic.primeFilterKernel_one,
    ZetaRieszCosineCarrier.re_coefficient_filter_one]
  have hl := tuple_log_bounds hp
  have hlog : 2*(N : ℝ) ≤ Real.log (∏ i, p i : ℕ) := by linarith [hl.1]
  have ha : Real.exp (-(3/2 : ℝ)*(2*N+C+5*h))*(2*N)^N/N.factorial ≤
      Real.exp (-(3/2 : ℝ)*Real.log (∏ i, p i : ℕ))*
        (Real.log (∏ i, p i : ℕ))^N/N.factorial := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact Real.exp_le_exp.mpr (by linarith [hl.2])
    · exact pow_le_pow_left₀ (by positivity) hlog N
    · positivity
    · positivity
  nlinarith

/-- The original factorial normalization of a fixed-width five-prime
box has the same exponential rate 2u as the dangerous mass. -/
theorem box_scalar_lower {u c D : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) :
    (u*c*Real.exp (-(3/2 : ℝ)*D)/24)*(2*u)^N/((N : ℝ)+1)^6 ≤
      u^(N+1)*((c*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^5)*
        (Real.exp (-(3/2 : ℝ)*(2*N+D))*(2*N)^N/N.factorial/4)) := by
  have hs := PrimeWindow.local_monomial_lower hN (by norm_num : (0 : ℝ) ≤ 2)
  norm_num [PrimeWindow.localGrowth] at hs
  rw [show -(2*(N : ℝ))/2 = -(N : ℝ) by ring] at hs
  have hs' : (2 : ℝ)^N/(6*((N : ℝ)+1)) ≤
      Real.exp (-(N : ℝ))*(2*N)^N/N.factorial := by
    apply le_trans _ hs
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have he : Real.exp (2*(N : ℝ))*Real.exp (-(3/2 : ℝ)*(2*N+D)) =
      Real.exp (-(3/2 : ℝ)*D)*Real.exp (-(N : ℝ)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  let k := u^(N+1)*c*Real.exp (-(3/2 : ℝ)*D)/(4*((N : ℝ)+1)^5)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  calc
    _ = k*((2 : ℝ)^N/(6*((N : ℝ)+1))) := by
      dsimp [k]
      rw [mul_pow,pow_succ]
      field_simp
      ring
    _ ≤ k*(Real.exp (-(N : ℝ))*(2*N)^N/N.factorial) :=
      mul_le_mul_of_nonneg_left hs' hk
    _ = _ := by
      dsimp [k]
      calc
        _ = (u^(N+1)*c/(4*((N : ℝ)+1)^5))*
          (Real.exp (-(3/2 : ℝ)*D)*Real.exp (-(N : ℝ)))*
          ((2*N)^N/N.factorial) := by ring
        _ = _ := by rw [← he]; field_simp

/-- Independent positive supply, with actual primes, full product phase
and the original rectangle weight. It does not estimate the complement. -/
theorem eventually_positive_box_supply {u y : ℝ} (hu : 0 < u) (hy : y ≠ 0) :
    ∃ h C k : ℝ, 0 < h ∧ 0 ≤ C ∧ 0 < k ∧
      ∀ᶠ N : ℕ in atTop, ∀ L : ℝ,
        (137/100 : ℝ)*N ≤ L → L ≤ (7/5 : ℝ)*N →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
          k*(2*u)^N/((N : ℝ)+1)^6 ≤
            ((u : ℂ)^(N+1)*∑ n ∈ products N h v,
              ((ZetaRieszJointBoundary.weight N n : ℝ) : ℂ)*
                (SquarefreeVaughanLogSource.coefficient L n*
                  zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re := by
  obtain ⟨h,C,hh,hC,hphase⟩ := exists_negative_phase_window hy
  obtain ⟨c,hc,hcount⟩ := eventually_products_card_lower hh hC
  let D := C+5*h
  let k := u*c*Real.exp (-(3/2 : ℝ)*D)/24
  refine ⟨h,C,k,hh,hC,by dsimp [k]; positivity,?_⟩
  filter_upwards [hcount,eventually_weight_lower,eventually_ge_atTop 35,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1000*(h+C))]
    with N hcount hweight hN hsize L hLlo hLhi
  obtain ⟨v,hv,hvC,hcos⟩ := hphase (2*(N : ℝ))
  have hw : h+v ≤ (N : ℝ)/1000 := by linarith
  refine ⟨v,hv,hvC,?_⟩
  let Q := Real.exp (-(3/2 : ℝ)*(2*N+D))*(2*N)^N/N.factorial/4
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsum : (products N h v).card*Q ≤
      (∑ n ∈ products N h v, ((ZetaRieszJointBoundary.weight N n : ℝ) : ℂ)*
        (SquarefreeVaughanLogSource.coefficient L n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re := by
    rw [Complex.re_sum,← nsmul_eq_mul,← Finset.sum_const]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hl := tuple_log_bounds hp
    simpa only [Q,D,add_assoc] using box_atom_lower hN hh.le hv hvC hw hLlo hLhi hp
      (hweight h v hv hw p hp) (hcos _ hl.1.le hl.2)
  have hcountN := hcount v hv hvC
  have hproduct := mul_le_mul_of_nonneg_right hcountN hQ
  have hscaled := mul_le_mul_of_nonneg_left (hproduct.trans hsum) (pow_nonneg hu.le (N+1))
  have hscalar := box_scalar_lower hu.le hc.le (D := D) (show 1 ≤ N by omega)
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  exact hscalar.trans hscaled

/-- The same actual integers survive every current support mask. The two
explicit size conditions are discharged eventually for the literal length. -/
theorem products_subset_lowSupport (j : ℕ) (hj : 32 ≤ j) {u h v : ℝ}
    (hu : 1/2 < u) (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hv : 0 ≤ v) (hwidth : h+v ≤ (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)/1000)
    (hL : (137/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hsmall : 2*Real.log (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) <
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)/25) :
    products (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) h v ⊆
      ZetaRieszLeastVariation.lowSupport u
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  have hN : 0 < N := by dsimp [N,ZetaRieszPrimeCountFrequency.dyadicMomentOrder,
    ZetaRieszPrimeCountFrequency.dyadicPrimeCount]; positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 5 < K := by
    have hh : (2 : ℕ)^3 ≤ 2^(j+3) := Nat.pow_le_pow_right (by decide) (by omega)
    dsimp [K,ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    norm_num at hh
    omega
  intro n hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hb := tuple_fullParityBox hN hv hwidth hp
  obtain ⟨hk,hP,hr⟩ := tuple_extremes hN hv hwidth hp
  have hf := tuple_primeFactors hN hv hwidth hp
  have ht : 0 < Real.log (∏ i, p i : ℕ) :=
    Real.log_pos (by exact_mod_cast hb.nontrivial)
  obtain ⟨hlo,hhi⟩ := tuple_log_bounds hp
  have hwindow : (39/20 : ℝ)*N < Real.log (∏ i, p i : ℕ) ∧
      Real.log (∏ i, p i : ℕ) ≤ (203/100 : ℝ)*N := by constructor <;> linarith
  have hpCap : ∀ q ∈ (∏ i, p i).primeFactors, Real.log q ≤ (5/4 : ℝ)*N := by
    intro q hq
    rw [hf] at hq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    have hi := (tuple_bounds hp i).2.2
    have hs : slope i ≤ (11/10 : ℝ) := by fin_cases i <;> norm_num [slope,Fin.ext_iff]
    have hmul := mul_le_mul_of_nonneg_right hs hNR.le
    dsimp [start] at hi
    split_ifs at hi <;> linarith
  have hpA : ∀ q ∈ (∏ i, p i).primeFactors,
      q ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    apply (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N q).mpr
    refine ⟨hqp,?_,?_⟩
    · have hh : (N : ℝ)/25 < Real.log q := by
        rw [hf] at hq
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
        have hi := (tuple_bounds hp i).2.1
        have hs : (1/25 : ℝ) ≤ slope i := by fin_cases i <;> norm_num [slope,Fin.ext_iff]
        have hmul := mul_le_mul_of_nonneg_right hs hNR.le
        dsimp [start] at hi
        split_ifs at hi <;> linarith
      have hl : Real.log (N^2 : ℕ) < Real.log q := by
        rw [Nat.cast_pow,Real.log_pow]
        change 2*Real.log N < _
        exact hsmall.trans hh
      exact_mod_cast (Real.log_lt_log_iff (by positivity : (0 : ℝ) < (N^2 : ℕ)) hq0).mp hl
    · have hlog : Real.log q < SquarefreeVaughanLogSource.length u N :=
        lt_of_le_of_lt (hpCap q hq) (by dsimp [N] at *; linarith)
      have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
          SquarefreeVaughanLogSource.length u N := by
        simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
      exact_mod_cast (Real.log_lt_log_iff hq0 (by positivity)).mp (he ▸ hlog)
  have hdom (q : ℕ) (hq : q ∈ (∏ i, p i).primeFactors) :
      Real.log q < (13/20 : ℝ)*Real.log (∏ i, p i : ℕ) := by
    nlinarith [hpCap q hq,hwindow.1]
  have hmem := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (huU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le) (by dsimp [N] at *; linarith)
    ((ZetaRieszJointAllocation.mem_literalWindow N _).mpr
      (by constructor <;> nlinarith [hwindow.1,hwindow.2])) hb.squarefree
    hb.count_lower (by rw [hk]; exact hK)
    (fun q hq => ((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N q).mp (hpA q hq)).2.2)
  have hcancel : (∏ i, p i) ∉ ZetaRieszJointAllocation.cancellingSector u N K := by
    intro hc
    obtain ⟨_,_,_,_,_,q,hq,_,_,_,hhi⟩ := Finset.mem_filter.mp hc
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hlogs : Real.log ((∏ i, p i)/q : ℕ) = Real.log (∏ i, p i : ℕ)-Real.log q := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hq) (by exact_mod_cast hqp.ne_zero),
        Real.log_div (by exact_mod_cast hb.squarefree.ne_zero) (by exact_mod_cast hqp.ne_zero)]
    have hh := (div_le_iff₀ ht).mp hhi
    rw [hlogs] at hh
    nlinarith [hdom q hq]
  have hret : (∏ i, p i) ∈ ZetaRieszMaskSupport.retainedBand u N K :=
    Finset.mem_sdiff.mpr ⟨hmem,hcancel⟩
  have hnd : (∏ i, p i) ∈ ZetaRieszDominantAllocation.nondominantBand u N K := by
    refine Finset.mem_sdiff.mpr ⟨hret,?_⟩
    intro hd
    obtain ⟨_,_,_,_,q,hq,_,_,hlarge⟩ := Finset.mem_filter.mp hd
    exact (hdom q hq).not_ge hlarge
  have hcore : (∏ i, p i) ∈ coreBand u N K :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hnd,by constructor <;> nlinarith [hwindow.1,hwindow.2]⟩,hwindow⟩
  have hfull : (∏ i, p i) ∈ ZetaRieszLeastBoundary.fullBand u N K :=
    Finset.mem_filter.mpr ⟨hcore,hb.squarefree,hb.nontrivial,hb.count_lower,hb.largest_mem,hpA⟩
  have hinter : ZetaRieszLeastBoundary.interior (∏ i, p i) := by
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · apply (lt_div_iff₀ ht).mpr; linarith [hb.largest_lower]
    · apply (div_lt_iff₀ ht).mpr; linarith [hb.largest_upper]
    · apply (lt_div_iff₀ ht).mpr; linarith [hb.least_lower]
    · apply (div_lt_iff₀ ht).mpr; linarith [hb.least_upper]
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hfull,hinter⟩,by rw [hk]; decide⟩

/-- On the unchanged cofinal schedule there is genuine, positively phased
five-prime supply inside the retained support. The constant and starting
index are existential. The rest of the signed carrier is not bounded. -/
theorem eventually_retained_positive_supply {u y : ℝ}
    (hu : 1/2 < u) (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : y ≠ 0) :
    ∃ h C k : ℝ, 0 < h ∧ 0 ≤ C ∧ 0 < k ∧ ∀ᶠ j : ℕ in atTop,
      ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
        products (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) h v ⊆
          ZetaRieszLeastVariation.lowSupport u
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
            (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) ∧
        k*(2*u)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
            ((ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)+1)^6 ≤
          ((u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
            ∑ n ∈ products (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) h v,
              ((ZetaRieszJointBoundary.weight
                (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n : ℝ) : ℂ)*
                ZetaRieszLeastVariation.carrierAtom u y
                  (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n).re := by
  have hu0 : 0 < u := by linarith
  obtain ⟨h,C,k,hh,hC,hk,hsupply⟩ := eventually_positive_box_supply hu0 hy
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    huU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
    (by norm_num : (0 : ℝ) ≤ 137/200) hroom
  have hlogs : Tendsto (fun N : ℕ => 2*Real.log N/(N : ℝ)) atTop (𝓝 0) := by
    have hl := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def,pow_one,one_mul,add_zero,mul_div_assoc,mul_zero]
      using hl.const_mul 2
  have hsize : ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 1000*(h+C) ≤ (N : ℝ) ∧ 2*Real.log N < (N : ℝ)/25 := by
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1000*(h+C)),
      hlogs.eventually_lt_const (by norm_num : (0 : ℝ) < 1/25)] with N hN hwidth hlog
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    refine ⟨hN,hwidth,?_⟩
    have hh := (div_lt_iff₀ hNR).mp hlog
    linarith
  refine ⟨h,C,k,hh,hC,hk,?_⟩
  filter_upwards [eventually_ge_atTop 32,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hsupply,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hL,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hsize]
    with j hj hsupply hL hsize
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  have hlo : (137/100 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by
    dsimp [N]; nlinarith [hL]
  have hhi : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    have hl := ZetaRieszHeadOrders.length_le_two_log_two hu.le hsize.1
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨v,hv,hvC,hbound⟩ := hsupply (SquarefreeVaughanLogSource.length u N) hlo hhi
  refine ⟨v,hv,hvC,products_subset_lowSupport j hj hu huU hv ?_ hlo hsize.2.2,?_⟩
  · dsimp [N] at *
    linarith [hsize.2.1]
  · exact hbound

end
end RiemannGaussian.ZetaRieszCompensationSupply
