/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoreExtensions
import RiemannGaussian.ZetaRieszCompensationSupply
import RiemannGaussian.ZetaRieszJointPhaseCredit

/-!
# Actual four-prime compensation for a balanced triple box

All selections below are finite subfamilies of the existing core. Their
purpose is a signed comparison retaining the whole complementary sum.
Prime intervals have fixed logarithmic width; no phase-density transport,
cofactor completion or exponentially thin prime interval is used.
-/

namespace RiemannGaussian.ZetaRieszQuadrupleCompensation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation
open ZetaRieszOneSidedArithmetic ZetaRieszAllowanceComplement
open ZetaRieszReflectedLinear

/-- The two independent log translations stay inside one fixed chamber. -/
def grid (N : ℕ) (h : ℝ) : Finset ℕ := Finset.range ⌊(N : ℝ)/(1000*h)⌋₊

/-- Four separated slopes; two translations are balanced in the last leg. -/
def start (N : ℕ) (h v : ℝ) (i j : ℕ) (a : Fin 4) : ℝ :=
  if a = 0 then (11/25 : ℝ)*N+i*h
  else if a = 1 then (12/25 : ℝ)*N+j*h
  else if a = 2 then (13/25 : ℝ)*N
  else (14/25 : ℝ)*N-(i+j)*h+v

/-- The literal four-prime choices in a single translated box. -/
def tuples (N : ℕ) (h v : ℝ) (i j : ℕ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset (fun a => logPrimes (start N h v i j a) h)

/-- Products are actual integer labels, not a continuum sample. -/
def products (N : ℕ) (h v : ℝ) (i j : ℕ) : Finset ℕ :=
  (tuples N h v i j).image (fun p => ∏ a, p a)

/-- A positive supply whose allocated credit may be spent only once. -/
def supply (N : ℕ) (h v : ℝ) : Finset ℕ :=
  ((grid N h).product (grid N h)).biUnion (fun ij => products N h v ij.1 ij.2)

theorem grid_bound {N i : ℕ} {h : ℝ} (hh : 0 < h) (hi : i ∈ grid N h) :
    (i : ℝ)*h < (N : ℝ)/1000 := by
  have ht : (i : ℝ) < (N : ℝ)/(1000*h) :=
    (Nat.cast_lt.mpr (Finset.mem_range.mp hi)).trans_le (Nat.floor_le (by positivity))
  have hm := (lt_div_iff₀ (by positivity : 0 < 1000*h)).mp ht
  nlinarith

theorem tuple_bounds {N i j : ℕ} {h v : ℝ} {p : Fin 4 → ℕ}
    (hp : p ∈ tuples N h v i j) (a : Fin 4) :
    (p a).Prime ∧ start N h v i j a < Real.log (p a) ∧
      Real.log (p a) ≤ start N h v i j a+h :=
  logPrimes_bounds (Fintype.mem_piFinset.mp hp a)

theorem start_bounds {N i j : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000) (a : Fin 4) :
    (43/100 : ℝ)*N ≤ start N h v i j a ∧
      start N h v i j a+h ≤ (57/100 : ℝ)*N := by
  have hbi := grid_bound hh hi
  have hbj := grid_bound hh hj
  have hih := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hh.le
  have hjh := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh.le
  have hn := Nat.cast_nonneg (α := ℝ) N
  fin_cases a <;> norm_num [start, Fin.ext_iff] <;> constructor <;> linarith

/-- Coordinate intervals are ordered even across different grid boxes. -/
theorem coordinate_order {N i j i' j' : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hi' : i' ∈ grid N h) (hj' : j' ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p q : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j) (hq : q ∈ tuples N h v i' j')
    {a b : Fin 4} (hab : a < b) : p a < q b := by
  apply logPrimes_order (a := start N h v i j a) (b := start N h v i' j' b) _
    (Fintype.mem_piFinset.mp hp a) (Fintype.mem_piFinset.mp hq b)
  have hbi := grid_bound hh hi
  have hbj := grid_bound hh hj
  have hbi' := grid_bound hh hi'
  have hbj' := grid_bound hh hj'
  have hih := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hh.le
  have hjh := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh.le
  have hih' := mul_nonneg (Nat.cast_nonneg (α := ℝ) i') hh.le
  have hjh' := mul_nonneg (Nat.cast_nonneg (α := ℝ) j') hh.le
  fin_cases a <;> fin_cases b
  all_goals try norm_num at hab
  all_goals norm_num [start, Fin.ext_iff]
  all_goals linarith

/-- Prime factorization prevents any collision between the four coordinates. -/
theorem tuple_eq_of_product_eq {N i j i' j' : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hi' : i' ∈ grid N h) (hj' : j' ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p q : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j) (hq : q ∈ tuples N h v i' j')
    (he : (∏ a, p a) = ∏ a, q a) : p = q := by
  funext a
  have hpa := (tuple_bounds hp a).1
  have hd : p a ∣ ∏ b, q b := by rw [← he]; exact Finset.dvd_prod_of_mem p (Finset.mem_univ a)
  obtain ⟨b,_,hb⟩ := (hpa.prime.dvd_finsetProd_iff q).mp hd
  have heq := (Nat.prime_dvd_prime_iff_eq hpa (tuple_bounds hq b).1).mp hb
  have hab : a = b := by
    rcases lt_trichotomy a b with hab | hab | hab
    · exact False.elim ((coordinate_order hh hi hj hi' hj' hv hw hp hq hab).ne heq)
    · exact hab
    · exact False.elim ((coordinate_order hh hi' hj' hi hj hv hw hq hp hab).ne heq.symm)
  simpa only [hab] using heq

theorem products_card {N i j : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000) :
    (products N h v i j).card = ∏ a, (logPrimes (start N h v i j a) h).card := by
  rw [products, Finset.card_image_of_injOn (fun p hp q hq he =>
    tuple_eq_of_product_eq hh hi hj hi hj hv hw hp hq he)]
  simp [tuples]

theorem tuple_squarefree {N i j : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j) : Squarefree (∏ a, p a) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a _ b _ hab
    apply Nat.coprime_iff_isRelPrime.mp
    apply (tuple_bounds hp a).1.coprime_iff_not_dvd.mpr
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq (tuple_bounds hp a).1 (tuple_bounds hp b).1).mp hd
    rcases lt_or_gt_of_ne hab with ht | ht
    · exact (coordinate_order hh hi hj hi hj hv hw hp hp ht).ne he
    · exact (coordinate_order hh hi hj hi hj hv hw hp hp ht).ne he.symm
  · intro a _
    exact (tuple_bounds hp a).1.squarefree

theorem tuple_log {N i j : ℕ} {h v : ℝ} {p : Fin 4 → ℕ}
    (hp : p ∈ tuples N h v i j) : Real.log (∏ a, p a : ℕ) = ∑ a, Real.log (p a) := by
  rw [Nat.cast_prod, Real.log_prod]
  intro a _
  exact_mod_cast (tuple_bounds hp a).1.ne_zero

theorem tuple_log_bounds {N i j : ℕ} {h v : ℝ} {p : Fin 4 → ℕ}
    (hp : p ∈ tuples N h v i j) :
    2*(N : ℝ)+v < Real.log (∏ a, p a : ℕ) ∧
      Real.log (∏ a, p a : ℕ) ≤ 2*(N : ℝ)+v+4*h := by
  have hl := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin 4)))
    (fun a _ => (tuple_bounds hp a).2.1.le)
    ⟨0,Finset.mem_univ _,(tuple_bounds hp 0).2.1⟩
  have hu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
    (fun a _ => (tuple_bounds hp a).2.2)
  rw [tuple_log hp]
  simp only [Fin.sum_univ_four] at hl hu ⊢
  norm_num [start,Fin.ext_iff] at hl hu
  constructor <;> linarith

theorem tuple_primeFactors {N i j : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j) :
    (∏ a, p a).primeFactors = Finset.univ.image p := by
  have hinj : Function.Injective p :=
    (show StrictMono p from fun _ _ hab => coordinate_order hh hi hj hi hj hv hw hp hp hab).injective
  rw [← Finset.prod_image (f := fun n : ℕ => n) (s := Finset.univ) hinj.injOn]
  apply Nat.primeFactors_prod
  intro a ha
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
  exact (tuple_bounds hp b).1

theorem tuple_count {N i j : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j) :
    (∏ a, p a).primeFactors.card = 4 := by
  rw [tuple_primeFactors hh hi hj hv hw hp, Finset.card_image_of_injective _
    (show StrictMono p from fun _ _ hab => coordinate_order hh hi hj hi hj hv hw hp hp hab).injective]
  simp

/-- Every actual box label lies in the already evaluated reflected class. -/
theorem tuple_linear {N i j : ℕ} {h v L : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j) : LinearClass L (∏ a, p a) := by
  have hl := tuple_log_bounds hp
  have hn := Nat.cast_nonneg (α := ℝ) N
  refine ⟨tuple_squarefree hh hi hj hv hw hp,by rw [tuple_count hh hi hj hv hw hp]; norm_num,
    by linarith [hl.1],?_⟩
  intro q hq
  rw [tuple_primeFactors hh hi hj hv hw hp] at hq
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
  have hs := start_bounds hh hi hj hv hw a
  have hb := tuple_bounds hp a
  constructor <;> linarith [hl.1,hl.2]

/-- On this chamber the original coefficient is uniformly negative. -/
theorem tuple_coefficient_le {N i j : ℕ} {h v L : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    (hL0 : 0 < L) (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j) :
    (SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re ≤ -(N : ℝ)/20 := by
  have ht := tuple_log_bounds hp
  have hclass := tuple_linear hh hi hj hv hw hL hLu hp
  rw [coefficient_eq_linear hclass, Complex.ofReal_re,
    linearCoefficient_four hclass (tuple_count hh hi hj hv hw hp)]
  have hratio : 1 ≤ Real.log (∏ a, p a : ℕ)/L := by
    apply (le_div_iff₀ hL0).mpr
    linarith [ht.1]
  have hgap : 2*Real.log (∏ a, p a : ℕ)-3*L ≤ -(N : ℝ)/20 := by linarith [ht.2]
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hm := mul_le_mul_of_nonpos_right hratio (show 2*Real.log (∏ a, p a : ℕ)-3*L ≤ 0 by linarith)
  linarith

private theorem interval_index_eq {h b t : ℝ} (hh : 0 < h) {i j : ℕ}
    (hi : b+(i : ℝ)*h < t) (hi' : t ≤ b+(i : ℝ)*h+h)
    (hj : b+(j : ℝ)*h < t) (hj' : t ≤ b+(j : ℝ)*h+h) : i = j := by
  have stop (i j : ℕ) (hl : b+(j : ℝ)*h < t) (hu : t ≤ b+(i : ℝ)*h+h)
      (hij : i < j) : False := by
    have hr : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
    nlinarith [mul_le_mul_of_nonneg_right hr hh.le]
  rcases lt_trichotomy i j with ht | ht | ht
  · exact False.elim (stop i j hj hi' ht)
  · exact ht
  · exact False.elim (stop j i hi hj' ht)

/-- No integer can spend its positive contribution in two different boxes. -/
theorem products_disjoint {N : ℕ} {h v : ℝ} (hh : 0 < h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000) :
    (((grid N h).product (grid N h) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ij => products N h v ij.1 ij.2) := by
  intro ij hij kl hkl hne
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
  obtain ⟨hk,hl⟩ := Finset.mem_product.mp hkl
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn
  obtain ⟨q,hq,hqn⟩ := Finset.mem_image.mp hn'
  have he := tuple_eq_of_product_eq hh hi hj hk hl hv hw hp hq (hpn.trans hqn.symm)
  subst q
  have bp := tuple_bounds hp 0
  have bq := tuple_bounds hq 0
  have cp := tuple_bounds hp 1
  have cq := tuple_bounds hq 1
  norm_num [start,Fin.ext_iff] at bp bq cp cq
  have he0 := interval_index_eq hh bp.2.1 bp.2.2 bq.2.1 bq.2.2
  have he1 := interval_index_eq hh cp.2.1 cp.2.2 cq.2.1 cq.2.2
  exact hne (Prod.ext he0 he1)

/-- Actual prime counts are uniform throughout the required moving band.
The fixed-width PNT supplies a lower bound, not a signed density replacement. -/
theorem eventually_interval_card_lower {h : ℝ} (hh : 0 < h) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ a : ℝ,
      (N : ℝ)/3 ≤ a → a ≤ N →
      c*Real.exp a/((N : ℝ)+1) ≤ ((logPrimes a h).card : ℝ) := by
  let d := (Real.exp h-1)/2
  have hd : 0 < d := by dsimp [d]; linarith [Real.one_lt_exp_iff.mpr hh]
  refine ⟨d/(1+h),div_pos hd (by positivity),?_⟩
  have hm := (PrimeWindow.theta_interval_div_tendsto (Real.exp_pos h)).eventually_const_lt
    (show d < Real.exp h-1 by dsimp [d]; linarith [Real.one_lt_exp_iff.mpr hh])
  obtain ⟨X,hX⟩ := eventually_atTop.mp hm
  have hx : Tendsto (fun N : ℕ => Real.exp ((N : ℝ)/3)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num))
  filter_upwards [hx.eventually_ge_atTop X] with N hN a ha hau
  have he : Real.exp ((N : ℝ)/3) ≤ Real.exp a := Real.exp_le_exp.mpr ha
  have hl := (lt_div_iff₀ (Real.exp_pos a)).mp (hX (Real.exp a) (hN.trans he))
  rw [← PrimeWindow.sum_log_primesInWindow (Real.exp_pos a).le (Real.one_le_exp_iff.mpr hh.le)] at hl
  have hs : (∑ p ∈ logPrimes a h, Real.log p) ≤
      (logPrimes a h).card*((1+h)*((N : ℝ)+1)) := by
    calc
      _ ≤ ∑ _p ∈ logPrimes a h, (1+h)*((N : ℝ)+1) := Finset.sum_le_sum (fun p hp => by
        have hb := (logPrimes_bounds hp).2.2
        nlinarith [Nat.cast_nonneg (α := ℝ) N, mul_nonneg hh.le (Nat.cast_nonneg (α := ℝ) N)])
      _ = _ := by simp
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ)+1)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 1+h)).mpr
  change d*Real.exp a < ∑ p ∈ logPrimes a h, Real.log p at hl
  linarith

/-- The two-dimensional union gains two powers of the moment order.
All labels are distinct actual products of four ordinary primes. -/
theorem eventually_supply_card_lower {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ C →
      c*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^2 ≤ (supply N h v).card := by
  obtain ⟨c,hc,hcounts⟩ := eventually_interval_card_lower hh
  refine ⟨c^4/(4000*h)^2,by positivity,?_⟩
  filter_upwards [hcounts,eventually_ge_atTop (1 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (4000*(h+C))]
    with N hcount hN hsize v hv hvC
  have hw : h+v ≤ (N : ℝ)/1000 := by linarith
  have hc0 := Nat.cast_nonneg (α := ℝ) N
  have hc1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let M := ⌊(N : ℝ)/(1000*h)⌋₊
  have hfloor : (N : ℝ)/(1000*h) < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hM : ((N : ℝ)+1)/(4000*h) ≤ M := by
    apply (div_le_iff₀ (by positivity : 0 < 4000*h)).mpr
    have ht := (div_lt_iff₀ (by positivity : 0 < 1000*h)).mp hfloor
    nlinarith
  have hbox (ij : ℕ × ℕ) (hij : ij ∈ (grid N h).product (grid N h)) :
      c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4 ≤ (products N h v ij.1 ij.2).card := by
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
    rw [products_card hh hi hj hv hw, Nat.cast_prod]
    have he (a : Fin 4) : c*Real.exp (start N h v ij.1 ij.2 a)/((N : ℝ)+1) ≤
        ((logPrimes (start N h v ij.1 ij.2 a) h).card : ℝ) := by
      have hs := start_bounds hh hi hj hv hw a
      exact hcount _ (by linarith) (by linarith)
    have hp := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 4)))
      (fun a _ => by positivity : ∀ a ∈ (Finset.univ : Finset (Fin 4)),
        0 ≤ c*Real.exp (start N h v ij.1 ij.2 a)/((N : ℝ)+1))
      (fun a _ => he a)
    have hex : (∏ a : Fin 4, Real.exp (start N h v ij.1 ij.2 a)) =
        Real.exp (2*(N : ℝ)+v) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Fin.sum_univ_four]
      norm_num [start,Fin.ext_iff]
      ring
    simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib,hex,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hp
    exact le_trans (by gcongr; linarith :
      c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4 ≤
        c^4*Real.exp (2*(N : ℝ)+v)/((N : ℝ)+1)^4) hp
  have hs := Finset.sum_le_sum hbox
  rw [Finset.sum_const, nsmul_eq_mul] at hs
  have hcard : (supply N h v).card =
      ∑ ij ∈ (grid N h).product (grid N h), (products N h v ij.1 ij.2).card :=
    Finset.card_biUnion (products_disjoint hh hv hw)
  rw [hcard,Nat.cast_sum]
  apply le_trans ?_ hs
  simp only [Finset.product_eq_sprod,Finset.card_product,grid,Finset.card_range,Nat.cast_mul]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ((N : ℝ)+1)/(4000*h)) hM 2
  have hm := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4 by positivity)
  calc
    _ = (((N : ℝ)+1)/(4000*h))^2*
        (c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4) := by field_simp
    _ ≤ (M : ℝ)^2*(c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4) := hm
    _ = _ := by dsimp only [M]; ring

/-- A scalar comparison weight, evaluated at the unchanged radial saddle. -/
def saddleEnvelope (N : ℕ) : ℝ :=
  Real.exp (-3*(N : ℝ))*(2*(N : ℝ))^N/N.factorial

theorem saddleEnvelope_nonneg (N : ℕ) : 0 ≤ saddleEnvelope N := by
  unfold saddleEnvelope
  positivity

theorem saddleEnvelope_pos {N : ℕ} (hN : 0 < N) : 0 < saddleEnvelope N := by
  unfold saddleEnvelope
  positivity

/-- The original allocated atom is positive on the selected phase window. -/
theorem tuple_atom_lower (A : Finset ℕ) {N i j : ℕ} {h v C L y : ℝ}
    (hh : 0 < h) (hi : i ∈ grid N h) (hj : j ∈ grid N h)
    (hv : 0 ≤ v) (hvC : v ≤ C) (hw : h+v ≤ (N : ℝ)/1000)
    (hL0 : 0 < L) (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hshare : (1/2 : ℝ) ≤ 1-4*Real.exp (-(N : ℝ)/64))
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j)
    (hcos : Real.cos (y*Real.log (∏ a, p a : ℕ)) ≤ -(1/2 : ℝ)) :
    (N : ℝ)/80*Real.exp (-(3/2 : ℝ)*(C+4*h))*saddleEnvelope N ≤
      (residualCoefficient A L N (∏ a, p a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ a, p a)).re := by
  have ht := tuple_log_bounds hp
  have hs := tuple_squarefree hh hi hj hv hw hp
  have hk := tuple_count hh hi hj hv hw hp
  have hn1 : 1 < ∏ a, p a := by
    apply (tuple_bounds hp 0).1.one_lt.trans_le
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Finset.dvd_prod_of_mem p (Finset.mem_univ 0))
  have hbal : ∀ q ∈ (∏ a, p a).primeFactors, Real.log q ≤ Real.log (∏ a, p a : ℕ)/2 := by
    intro q hq
    rw [tuple_primeFactors hh hi hj hv hw hp] at hq
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
    have hb := tuple_bounds hp a
    have hst := start_bounds hh hi hj hv hw a
    linarith [ht.1,Nat.cast_nonneg (α := ℝ) N]
  have hwgt := balanced_weight_lower A N hs hn1 hbal
  rw [hk] at hwgt
  norm_num only [Nat.cast_ofNat] at hwgt
  have hamp := ZetaRieszCosineCarrier.factorial_envelope_nonneg N (∏ a, p a)
  change 0 ≤ amplitude N (∏ a, p a) at hamp
  have hhalf : amplitude N (∏ a, p a)/2 ≤ weight A N (∏ a, p a) := by nlinarith
  have hc := tuple_coefficient_le hh hi hj hv hw hL0 hL hLu hp
  have hprod : (N : ℝ)/40 ≤ (SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re*
      Real.cos (y*Real.log (∏ a, p a : ℕ)) := by
    have hneg := mul_nonneg (show 0 ≤ -Real.cos (y*Real.log (∏ a, p a : ℕ))-1/2 by linarith)
      (show 0 ≤ -(SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re by
        linarith [Nat.cast_nonneg (α := ℝ) N])
    nlinarith
  rw [re_residual_atom]
  have hmain := mul_le_mul hhalf hprod (by positivity : 0 ≤ (N : ℝ)/40) (weight_nonneg A N _)
  have ha : Real.exp (-(3/2 : ℝ)*(C+4*h))*saddleEnvelope N ≤ amplitude N (∏ a, p a) := by
    unfold amplitude saddleEnvelope
    rw [← mul_div_assoc,← mul_assoc,← Real.exp_add]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      linarith [ht.2]
    · apply pow_le_pow_left₀ (by positivity)
      linarith [ht.1]
    · positivity
    · positivity
  calc
    _ = (N : ℝ)/80*(Real.exp (-(3/2 : ℝ)*(C+4*h))*saddleEnvelope N) := by ring
    _ ≤ (N : ℝ)/80*amplitude N (∏ a, p a) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = amplitude N (∏ a, p a)/2*((N : ℝ)/40) := by ring
    _ ≤ _ := hmain

/-- The positive supply has a quantitative signed lower bound, with its
original allocation and full complex phase retained. -/
theorem eventually_supply_real_lower {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (v L y : ℝ),
      0 ≤ v → v ≤ C → 0 < L → (137/100 : ℝ)*N ≤ L → L ≤ (7/5 : ℝ)*N →
      (∀ t : ℝ, 2*N+v ≤ t → t ≤ 2*N+v+4*h → Real.cos (y*t) ≤ -(1/2 : ℝ)) →
      c*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^2*saddleEnvelope N ≤
        (∑ n ∈ supply N h v, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨c,hc,hcard⟩ := eventually_supply_card_lower hh hC
  refine ⟨c/80*Real.exp (-(3/2 : ℝ)*(C+4*h)),by positivity,?_⟩
  have ht : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)/64)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 64))
  filter_upwards [hcard,ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1/8),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1000*(h+C))]
    with N hcN hsmall hsize A v L y hv hvC hL0 hL hLu hphase
  have hw : h+v ≤ (N : ℝ)/1000 := by linarith
  have ha (n : ℕ) (hn : n ∈ supply N h v) :
      (N : ℝ)/80*Real.exp (-(3/2 : ℝ)*(C+4*h))*saddleEnvelope N ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    obtain ⟨ij,hij,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hb := tuple_log_bounds hp
    exact tuple_atom_lower A hh hi hj hv hvC hw hL0 hL hLu (by linarith) hp
      (hphase _ hb.1.le hb.2)
  have hsum := Finset.sum_le_sum ha
  rw [Finset.sum_const,nsmul_eq_mul,← Complex.re_sum] at hsum
  have hscale := mul_le_mul_of_nonneg_right (hcN v hv hvC)
    (show 0 ≤ (N : ℝ)/80*Real.exp (-(3/2 : ℝ)*(C+4*h))*saddleEnvelope N by
      positivity [saddleEnvelope_nonneg N])
  exact (le_of_eq (by ring)).trans (hscale.trans hsum)

/-- An elementary upper count for the actual interval, using Chebyshev. -/
theorem interval_card_upper {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    ((logPrimes a h).card : ℝ) ≤ Real.log 4*Real.exp (a+h)/a := by
  have hs : a*(logPrimes a h).card ≤ ∑ p ∈ logPrimes a h, Real.log p := by
    calc
      _ = ∑ _p ∈ logPrimes a h, a := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun p hp => (logPrimes_bounds hp).2.1.le)
  have he := PrimeWindow.sum_log_primesInWindow (Real.exp_pos a).le
    (Real.one_le_exp_iff.mpr hh)
  change (∑ p ∈ logPrimes a h, Real.log p) = _ at he
  rw [he] at hs
  have ht := Chebyshev.theta_le_log4_mul_x (Real.exp_nonneg (a+h))
  rw [Real.exp_add, mul_comm (Real.exp a) (Real.exp h)] at ht
  apply (le_div_iff₀ ha).mpr
  rw [Real.exp_add,mul_comm (Real.exp a) (Real.exp h)]
  nlinarith [Chebyshev.theta_nonneg (Real.exp a)]

/-- All translates of one fixed-width balanced triple box have this
actual-prime upper count. No estimate for a signed density error is used. -/
theorem triple_card_upper {N : ℕ} (hN : 1 ≤ N) {a h C : ℝ}
    (hh : 0 ≤ h) (ha : (2/3 : ℝ)*N ≤ a) (hau : a ≤ (2/3 : ℝ)*N+C) :
    ((tripleProducts a h).card : ℝ) ≤
      (3*Real.log 4*Real.exp (C+3*h))^3*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let c := 3*Real.log 4*Real.exp (C+3*h)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hb (b : ℝ) (hba : a ≤ b) (hbu : b ≤ a+2*h) :
      ((logPrimes b h).card : ℝ) ≤ c*Real.exp ((2/3 : ℝ)*N)/((N : ℝ)+1) := by
    have hbp : 0 < b := by linarith
    have hbnd := interval_card_upper hbp hh
    have hq : ((N : ℝ)+1)/3 ≤ b := by linarith
    calc
      _ ≤ Real.log 4*Real.exp (b+h)/b := hbnd
      _ ≤ Real.log 4*Real.exp ((2/3 : ℝ)*N+C+3*h)/b :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)) hbp.le
      _ ≤ Real.log 4*Real.exp ((2/3 : ℝ)*N+C+3*h)/(((N : ℝ)+1)/3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hq
      _ = _ := by
        dsimp only [c]
        rw [show (2/3 : ℝ)*N+C+3*h = (C+3*h)+(2/3 : ℝ)*N by ring,Real.exp_add]
        field_simp
  have hp := hb a le_rfl (by linarith)
  have hq := hb (a+h) (by linarith) (by linarith)
  have hr := hb (a+2*h) (by linarith) le_rfl
  rw [tripleProducts_card hh,Nat.cast_mul,Nat.cast_mul]
  have ht := mul_le_mul (mul_le_mul hp hq (Nat.cast_nonneg _) (by positivity))
    hr (Nat.cast_nonneg _) (by positivity)
  have he : Real.exp ((2/3 : ℝ)*N)^3 = Real.exp (2*(N : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ (c*Real.exp ((2/3 : ℝ)*N)/((N : ℝ)+1))^3 := ht.trans_eq (by ring)
    _ = _ := by rw [div_pow,mul_pow,he]

/-- Fixed-width radial variation has a bounded factorial cost. -/
theorem amplitude_le_saddle {N n : ℕ} (hN : 0 < N) {D : ℝ}
    (hlo : 2*(N : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2*(N : ℝ)+D) :
    amplitude N n ≤ Real.exp (D/2)*saddleEnvelope N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : Real.log n/(2*(N : ℝ)) ≤ Real.exp (D/(2*(N : ℝ))) := by
    have he := Real.add_one_le_exp (D/(2*(N : ℝ)))
    have hr : Real.log n/(2*(N : ℝ)) ≤ 1+D/(2*(N : ℝ)) := by
      apply (div_le_iff₀ (by positivity)).mpr
      field_simp
      nlinarith
    linarith
  have hp := pow_le_pow_left₀ (div_nonneg (Real.log_natCast_nonneg _) (by positivity)) hratio N
  rw [div_pow,← Real.exp_nat_mul] at hp
  have he : (N : ℝ)*(D/(2*N)) = D/2 := by field_simp
  rw [he,div_le_iff₀ (by positivity : 0 < (2*(N : ℝ))^N)] at hp
  unfold amplitude saddleEnvelope
  have hExp : Real.exp (-(3/2 : ℝ)*Real.log n) ≤ Real.exp (-3*(N : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h := div_le_div_of_nonneg_right
    (mul_le_mul hExp hp (pow_nonneg (Real.log_natCast_nonneg _) _) (Real.exp_nonneg _))
    (show 0 ≤ (N.factorial : ℝ) by positivity)
  exact h.trans_eq (by ring)

/-- The original residual atom on any three-prime label has an explicit
upper modulus. This debit is used only when the opposing supply pays it. -/
theorem triple_atom_norm_upper (A : Finset ℕ) {N n : ℕ} (hN : 0 < N)
    {L D y : ℝ} (hL0 : 0 < L) (hL : (N : ℝ) ≤ L)
    (hs : Squarefree n) (hk : n.primeFactors.card = 3)
    (hDN : D ≤ N)
    (hlo : 2*(N : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2*(N : ℝ)+D) :
    ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      3*(N : ℝ)*Real.exp (D/2)*saddleEnvelope N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := ZetaRieszSperner.norm_coefficient_le_allowance hL0 n
  rw [ZetaRieszSperner.middleLayerAllowance,if_pos ⟨hs,by omega⟩,hk] at hb
  norm_num at hb
  have hratio : Real.log n/L ≤ 3 := (div_le_iff₀ hL0).mpr (by linarith)
  have hcost : ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ 3*(N : ℝ) := by
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_right hratio
      (show 0 ≤ Real.log n/3 by positivity)
    nlinarith
  have hker : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ = amplitude N n := by
    rw [norm_zetaPrimeLogKernel]
    norm_num [zetaPrimeExpWeight,amplitude]
    ring
  rw [norm_mul,hker]
  have hc := (ZetaRieszJointCountFloor.norm_residual_le A L N n).trans hcost
  have he := amplitude_le_saddle hN hlo hhi
  exact (mul_le_mul hc he (by unfold amplitude; positivity) (by positivity)).trans_eq (by ring)

/-- A whole actual triple box has one more denominator power than the
two-coordinate four-prime supply. The bound holds at every phase height. -/
theorem eventually_triple_box_norm_upper {h C : ℝ} (hh : 0 ≤ h) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (a L y : ℝ),
      (2/3 : ℝ)*N ≤ a → a ≤ (2/3 : ℝ)*N+C → 0 < L → (N : ℝ) ≤ L →
      ‖∑ n ∈ tripleProducts a h, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        B*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3*saddleEnvelope N := by
  let D := 3*C+6*h
  let B := 3*(3*Real.log 4*Real.exp (C+3*h))^3*Real.exp (D/2)
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop D]
    with N hN hDN A a L y ha hau hL0 hL
  have hbound := norm_sum_le (tripleProducts a h) (fun n =>
    residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
  have hs : (∑ n ∈ tripleProducts a h, ‖residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      (tripleProducts a h).card*(3*(N : ℝ)*Real.exp (D/2)*saddleEnvelope N) := by
    rw [← nsmul_eq_mul,← Finset.sum_const]
    apply Finset.sum_le_sum
    intro n hn
    have ht := tripleProducts_bounds hh hn
    exact triple_atom_norm_upper A (by omega) hL0 hL ht.1 ht.2.1
      hDN (by linarith [ht.2.2.1]) (by dsimp [D]; linarith [ht.2.2.2.1])
  have hc := mul_le_mul_of_nonneg_right (triple_card_upper hN hh ha hau)
    (show 0 ≤ 3*(N : ℝ)*Real.exp (D/2)*saddleEnvelope N by positivity [saddleEnvelope_nonneg N])
  exact (hbound.trans hs).trans (hc.trans_eq (by dsimp [B]; ring))

/-- A whole actual balanced triple box is paid by a disjoint four-prime
population. This is a signed inequality, not a completion or density model.
The supply may be consumed only once in a larger carrier ledger. -/
theorem eventually_joint_box_nonneg {y hT CT : ℝ} (hy : y ≠ 0) (hhT : 0 ≤ hT) :
    ∃ h C : ℝ, 0 < h ∧ 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (A : Finset ℕ) (a L : ℝ),
      (2/3 : ℝ)*N ≤ a → a ≤ (2/3 : ℝ)*N+CT →
      0 < L → (137/100 : ℝ)*N ≤ L → L ≤ (7/5 : ℝ)*N →
      ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
        0 ≤ ((∑ n ∈ tripleProducts a hT, residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
          ∑ n ∈ supply N h v, residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨h,C,hh,hC,hphase⟩ := ZetaRieszCompensationSupply.exists_negative_phase_window hy
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_real_lower hh hC
  obtain ⟨B,hB,htriple⟩ := eventually_triple_box_norm_upper (C := CT) hhT
  refine ⟨h,C,hh,hC,?_⟩
  filter_upwards [hsupply,htriple,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (B/c)]
    with N hs ht hsize A a L ha hau hL0 hL hLu
  obtain ⟨v,hv,hvC,hcos⟩ := hphase (2*(N : ℝ))
  refine ⟨v,hv,hvC,?_⟩
  have hpos := hs A v L y hv hvC hL0 hL hLu
    (fun t hlo hhi => hcos t hlo (by linarith))
  have hneg := ht A a L y ha hau hL0 (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hB' : B ≤ c*((N : ℝ)+1) := by
    have hd := (div_le_iff₀ hc).mp hsize
    nlinarith
  have hp : B*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3*saddleEnvelope N ≤
      c*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^2*saddleEnvelope N := by
    have hm := mul_le_mul_of_nonneg_right hB'
      (show 0 ≤ (N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3*saddleEnvelope N by
        positivity [saddleEnvelope_nonneg N])
    calc
      _ = B*((N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3*saddleEnvelope N) := by ring
      _ ≤ c*((N : ℝ)+1)*((N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3*saddleEnvelope N) := hm
      _ = _ := by field_simp
  have hr := Complex.re_le_norm (-(∑ n ∈ tripleProducts a hT,
    residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n))
  rw [Complex.neg_re,norm_neg] at hr
  rw [Complex.add_re]
  linarith

/-- Only a vanishing fraction of the genuine positive supply is needed
to pay a whole fixed-width triple box. This is a relative spending cap,
not a source-normalized error estimate. -/
theorem eventually_spending_bound {y hT CT : ℝ} (hy : y ≠ 0) (hhT : 0 ≤ hT) :
    ∃ h C B : ℝ, 0 < h ∧ 0 ≤ C ∧ 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (A : Finset ℕ) (a L : ℝ),
      (2/3 : ℝ)*N ≤ a → a ≤ (2/3 : ℝ)*N+CT →
      0 < L → (137/100 : ℝ)*N ≤ L → L ≤ (7/5 : ℝ)*N →
      ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
        0 < (∑ n ∈ supply N h v, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
        ‖∑ n ∈ tripleProducts a hT, residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
          B/((N : ℝ)+1)*(∑ n ∈ supply N h v, residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨h,C,hh,hC,hphase⟩ := ZetaRieszCompensationSupply.exists_negative_phase_window hy
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_real_lower hh hC
  obtain ⟨B,hB,htriple⟩ := eventually_triple_box_norm_upper (C := CT) hhT
  refine ⟨h,C,B/c,hh,hC,div_pos hB hc,?_⟩
  filter_upwards [hsupply,htriple,eventually_ge_atTop (1 : ℕ)]
    with N hs ht hN A a L ha hau hL0 hL hLu
  obtain ⟨v,hv,hvC,hcos⟩ := hphase (2*(N : ℝ))
  have hpos := hs A v L y hv hvC hL0 hL hLu
    (fun t hlo hhi => hcos t hlo (by linarith))
  have hneg := ht A a L y ha hau hL0 (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  refine ⟨v,hv,hvC,lt_of_lt_of_le (by positivity [saddleEnvelope_pos (show 0 < N by omega)]) hpos,?_⟩
  calc
    _ ≤ B*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3*saddleEnvelope N := hneg
    _ = (B/c)/((N : ℝ)+1)*
        (c*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^2*saddleEnvelope N) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hpos (by positivity)

/-- Spend precisely the adverse real part, preserving all unused positive
credit. Dropping an oversized supply instead would recreate clipping loss. -/
theorem signed_spending {X Y W : ℂ} {q : ℝ} (hY : 0 < Y.re)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (h : ‖X‖ ≤ q*Y.re) :
    let θ := max (-X.re) 0/Y.re
    0 ≤ θ ∧ θ ≤ q ∧ θ ≤ 1 ∧
      (W+(X+Y)).re = W.re+max X.re 0+(1-θ)*Y.re := by
  dsimp only
  have hneg := Complex.re_le_norm (-X)
  rw [Complex.neg_re,norm_neg] at hneg
  have hθ : max (-X.re) 0/Y.re ≤ q := by
    apply (div_le_iff₀ hY).mpr
    exact max_le (hneg.trans h) (mul_nonneg hq hY.le)
  refine ⟨div_nonneg (le_max_right _ _) hY.le,hθ,hθ.trans hq1,?_⟩
  have hid : X.re = max X.re 0-max (-X.re) 0 := by
    by_cases hx : 0 ≤ X.re
    · rw [max_eq_left hx,max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)]; ring
  simp only [Complex.add_re]
  rw [sub_mul,div_mul_cancel₀ _ hY.ne']
  linarith

open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszMaskSupport

/-- Every supply label is in the original core, with its original count,
physical and nondominant masks. No externally completed labels are added. -/
theorem eventually_supply_in_core {u h C : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ C →
      supply (dyadicMomentOrder j) h v ⊆
        coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hlen := eventually_length_lower (by linarith : 0 < u) hsource.le
  have horders : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually hlen,horders.eventually_ge_atTop (1000*(h+C))]
    with j hj hL hsize v hv hvC n hn
  obtain ⟨ij,hij,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hi,hj'⟩ := Finset.mem_product.mp hij
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  let N := dyadicMomentOrder j
  have hw : h+v ≤ (N : ℝ)/1000 := by dsimp [N]; linarith
  have hs := tuple_squarefree hh hi hj' hv hw hp
  have hk := tuple_count hh hi hj' hv hw hp
  have hb := tuple_log_bounds hp
  have hN : (0 : ℝ) < N := by dsimp [N]; linarith
  have hwin : (39/20 : ℝ)*N < Real.log (∏ a, p a : ℕ) ∧
      Real.log (∏ a, p a : ℕ) ≤ (203/100 : ℝ)*N := by
    constructor <;> linarith [hb.1,hb.2]
  have hK : 4 < dyadicPrimeCount j := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (show 3 ≤ j+3 by omega)
    norm_num at h
    exact lt_of_lt_of_le (by norm_num : (4 : ℕ) < 8) h
  have hcore := balanced_mem_nondominant j hj hu hsource.le hL hs
    ((mem_literalWindow _ _).mpr ⟨by linarith [hwin.1],by linarith [hwin.2]⟩)
    (by omega) (by rw [hk]; exact hK) (by
      intro q hq
      rw [tuple_primeFactors hh hi hj' hv hw hp] at hq
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
      have hb' := tuple_bounds hp a
      have hst := start_bounds hh hi hj' hv hw a
      linarith [hb.1])
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hcore,by constructor <;> linarith [hwin.1,hwin.2]⟩,hwin⟩

/-- The two paid classes are disjoint by their exact prime counts. -/
theorem triple_supply_disjoint {N : ℕ} {a hT h v : ℝ} (hhT : 0 ≤ hT)
    (hh : 0 < h) (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000) :
    Disjoint (tripleProducts a hT) (supply N h v) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hc := (tripleProducts_bounds hhT hn).2.1
  obtain ⟨ij,hij,hn'⟩ := Finset.mem_biUnion.mp hn'
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn'
  have hc' := tuple_count hh hi hj hv hw hp
  rw [hpn] at hc'
  omega

/-- The actual core admits deletion of the paid triple/four-prime pair
with zero lower-bound cost. The entire remaining signed carrier is kept.
This is not a floor for that complement or for the whole core. -/
theorem eventually_re_core_ge_without_box {u y hT CT : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : y ≠ 0) (hhT : 0 ≤ hT) (hCT : 0 ≤ CT) :
    ∃ h C : ℝ, 0 < h ∧ 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      (2/3 : ℝ)*dyadicMomentOrder j ≤ a → a ≤ (2/3 : ℝ)*dyadicMomentOrder j+CT →
      ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
        (((u : ℂ)^(dyadicMomentOrder j+1))*
          ∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)\
              (tripleProducts a hT ∪ supply (dyadicMomentOrder j) h v),
            residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
              (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
              zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re ≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*
            coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  obtain ⟨h,C,hh,hC,hpay⟩ := eventually_joint_box_nonneg (CT := CT) hy hhT
  refine ⟨h,C,hh,hC,?_⟩
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    eventually_supply_in_core hu hU hh hC,
    ZetaRieszJointPhaseCredit.eventually_boxes_in_core hu hU hhT hCT,
    tendsto_dyadicMomentOrder.eventually hL,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 2),
    hord.eventually_ge_atTop (1000*(h+C))]
    with j hj hs ht hL hN hsize a ha hau
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hLu : L ≤ (7/5 : ℝ)*N := by
    have he := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    dsimp only [L,N]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]
  obtain ⟨v,hv,hvC,hpaid⟩ := hj A a L ha hau (SquarefreeVaughanLogSource.length_pos _ _)
    (by dsimp [L,N]; linarith [hL]) hLu
  refine ⟨v,hv,hvC,?_⟩
  have hw : h+v ≤ (N : ℝ)/1000 := by dsimp [N]; linarith
  have hd := triple_supply_disjoint (a := a) hhT hh hv hw
  have hsub : tripleProducts a hT ∪ supply N h v ⊆ coreBand u N (dyadicPrimeCount j) :=
    Finset.union_subset (ht a ha hau).2.2 (hs v hv hvC)
  have he := Finset.sum_sdiff (f := f) hsub
  rw [Finset.sum_union hd] at he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re] at hre
  have hc : (∑ n ∈ coreBand u N (dyadicPrimeCount j)\(tripleProducts a hT ∪ supply N h v), f n).re ≤
      (∑ n ∈ coreBand u N (dyadicPrimeCount j), f n).re := by
    change 0 ≤ (∑ n ∈ tripleProducts a hT, f n).re+(∑ n ∈ supply N h v, f n).re at hpaid
    linarith
  have hm := mul_le_mul_of_nonneg_left hc (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  simpa only [coreResponse,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using hm

/-- Exact spending inside the original core. Only the adverse real part of
the triple box is paid; its positive part, all unused four-prime credit,
and the entire signed complement remain in the source ledger. The cap
`B/(N+1)` is relative and must not be treated as a vanishing absolute error. -/
theorem eventually_core_spending {u y hT CT : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : y ≠ 0) (hhT : 0 ≤ hT) (hCT : 0 ≤ CT) :
    ∃ h C B : ℝ, 0 < h ∧ 0 ≤ C ∧ 0 < B ∧ ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      (2/3 : ℝ)*dyadicMomentOrder j ≤ a → a ≤ (2/3 : ℝ)*dyadicMomentOrder j+CT →
      ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let X := ∑ n ∈ tripleProducts a hT, f n
        let Y := ∑ n ∈ supply N h v, f n
        let W := ∑ n ∈ coreBand u N (dyadicPrimeCount j)\
          (tripleProducts a hT ∪ supply N h v), f n
        let θ := max (-X.re) 0/Y.re
        0 < Y.re ∧ 0 ≤ θ ∧ θ ≤ B/((N : ℝ)+1) ∧ θ ≤ 1 ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re =
            u^(N+1)*(W.re+max X.re 0+(1-θ)*Y.re) := by
  obtain ⟨h,C,B,hh,hC,hB,hpay⟩ := eventually_spending_bound (CT := CT) hy hhT
  refine ⟨h,C,B,hh,hC,hB,?_⟩
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    eventually_supply_in_core hu hU hh hC,
    ZetaRieszJointPhaseCredit.eventually_boxes_in_core hu hU hhT hCT,
    tendsto_dyadicMomentOrder.eventually hL,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 2),
    hord.eventually_ge_atTop (1000*(h+C)),hord.eventually_ge_atTop B]
    with j hj hs ht hL hN hsize hBsize a ha hau
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hLu : L ≤ (7/5 : ℝ)*N := by
    have he := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    dsimp only [L,N]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]
  obtain ⟨v,hv,hvC,hY,hpay⟩ := hj A a L ha hau (SquarefreeVaughanLogSource.length_pos _ _)
    (by dsimp [L,N]; linarith [hL]) hLu
  refine ⟨v,hv,hvC,?_⟩
  let X := ∑ n ∈ tripleProducts a hT, f n
  let Y := ∑ n ∈ supply N h v, f n
  let W := ∑ n ∈ coreBand u N (dyadicPrimeCount j)\
    (tripleProducts a hT ∪ supply N h v), f n
  let θ := max (-X.re) 0/Y.re
  change 0 < Y.re ∧ 0 ≤ θ ∧ θ ≤ B/((N : ℝ)+1) ∧ θ ≤ 1 ∧
    ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re =
      u^(N+1)*(W.re+max X.re 0+(1-θ)*Y.re)
  have hq : B/((N : ℝ)+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    dsimp [N]
    linarith
  obtain ⟨hθ,hθB,hθ1,hledger⟩ := signed_spending (X := X) (Y := Y) (W := W)
    hY (by positivity) hq hpay
  refine ⟨hY,hθ,hθB,hθ1,?_⟩
  have hw : h+v ≤ (N : ℝ)/1000 := by dsimp [N]; linarith
  have hd := triple_supply_disjoint (a := a) hhT hh hv hw
  have hsub : tripleProducts a hT ∪ supply N h v ⊆ coreBand u N (dyadicPrimeCount j) :=
    Finset.union_subset (ht a ha hau).2.2 (hs v hv hvC)
  have he := Finset.sum_sdiff (f := f) hsub
  rw [Finset.sum_union hd] at he
  have he' : coreResponse u y N (dyadicPrimeCount j) = W+(X+Y) := he.symm
  rw [he']
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using congrArg (fun t : ℝ => u^(N+1)*t) hledger

/-- The spending cap tends to zero on the unchanged original schedule.
This does not say that the amount spent tends to zero at source scale. -/
theorem tendsto_spending_cap (B : ℝ) :
    Tendsto (fun j => B/((dyadicMomentOrder j : ℝ)+1)) atTop (𝓝 0) := by
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder)
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
    (tendsto_inv_atTop_zero.comp hord).const_mul B

end
end RiemannGaussian.ZetaRieszQuadrupleCompensation
