/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszQuadrupleCompensation

/-!
# Three-dimensional prime supply for a growing balanced triple region

The finite selections below are used directly in a signed spending
inequality. They keep the literal residual coefficient, moving length,
allocation, phase, and complementary core response.
-/

namespace RiemannGaussian.ZetaRieszBandCompensation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation
open ZetaRieszOneSidedArithmetic ZetaRieszAllowanceComplement
open ZetaRieszReflectedLinear

/-- All three translations remain in the same fixed-sign chamber. -/
def grid (N : ℕ) (h : ℝ) : Finset ℕ := Finset.range ⌊(N : ℝ)/(125*h)⌋₊

/-- The indices of the three free prime-log translations. -/
def cells (N : ℕ) (h : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (grid N h).product ((grid N h).product (grid N h))

/-- Four separated slopes; three translations are balanced in the last leg. -/
def start (N : ℕ) (h v : ℝ) (i j k : ℕ) (a : Fin 4) : ℝ :=
  if a = 0 then (11/25 : ℝ)*N+i*h
  else if a = 1 then (12/25 : ℝ)*N+j*h
  else if a = 2 then (13/25 : ℝ)*N+k*h
  else (14/25 : ℝ)*N-(i+j+k)*h+v

/-- The literal four-prime choices in a single translated box. -/
def tuples (N : ℕ) (h v : ℝ) (i j k : ℕ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset (fun a => logPrimes (start N h v i j k a) h)

/-- Products are actual integer labels, not a continuum sample. -/
def products (N : ℕ) (h v : ℝ) (i j k : ℕ) : Finset ℕ :=
  (tuples N h v i j k).image (fun p => ∏ a, p a)

/-- A positive supply whose allocated credit may be spent only once. -/
def supply (N : ℕ) (h v : ℝ) : Finset ℕ :=
  (cells N h).biUnion (fun ijk => products N h v ijk.1 ijk.2.1 ijk.2.2)

theorem grid_bound {N i : ℕ} {h : ℝ} (hh : 0 < h) (hi : i ∈ grid N h) :
    (i : ℝ)*h < (N : ℝ)/125 := by
  have ht : (i : ℝ) < (N : ℝ)/(125*h) :=
    (Nat.cast_lt.mpr (Finset.mem_range.mp hi)).trans_le (Nat.floor_le (by positivity))
  have hm := (lt_div_iff₀ (by positivity : 0 < 125*h)).mp ht
  nlinarith

theorem tuple_bounds {N i j k : ℕ} {h v : ℝ} {p : Fin 4 → ℕ}
    (hp : p ∈ tuples N h v i j k) (a : Fin 4) :
    (p a).Prime ∧ start N h v i j k a < Real.log (p a) ∧
      Real.log (p a) ≤ start N h v i j k a+h :=
  logPrimes_bounds (Fintype.mem_piFinset.mp hp a)

theorem start_bounds {N i j k : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000) (a : Fin 4) :
    (43/100 : ℝ)*N ≤ start N h v i j k a ∧
      start N h v i j k a+h ≤ (57/100 : ℝ)*N := by
  have hbi := grid_bound hh hi
  have hbj := grid_bound hh hj
  have hbk := grid_bound hh hk
  have hih := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hh.le
  have hjh := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh.le
  have hkh := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh.le
  have hn := Nat.cast_nonneg (α := ℝ) N
  fin_cases a <;> norm_num [start, Fin.ext_iff] <;> constructor <;> linarith

/-- Coordinate intervals are ordered even across different grid boxes. -/
theorem coordinate_order {N i j k i' j' k' : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hi' : i' ∈ grid N h) (hj' : j' ∈ grid N h) (hk' : k' ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p q : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j k) (hq : q ∈ tuples N h v i' j' k')
    {a b : Fin 4} (hab : a < b) : p a < q b := by
  apply logPrimes_order (a := start N h v i j k a) (b := start N h v i' j' k' b) _
    (Fintype.mem_piFinset.mp hp a) (Fintype.mem_piFinset.mp hq b)
  have hbi := grid_bound hh hi
  have hbj := grid_bound hh hj
  have hbk := grid_bound hh hk
  have hbi' := grid_bound hh hi'
  have hbj' := grid_bound hh hj'
  have hbk' := grid_bound hh hk'
  have hih := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hh.le
  have hjh := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh.le
  have hkh := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh.le
  have hih' := mul_nonneg (Nat.cast_nonneg (α := ℝ) i') hh.le
  have hjh' := mul_nonneg (Nat.cast_nonneg (α := ℝ) j') hh.le
  have hkh' := mul_nonneg (Nat.cast_nonneg (α := ℝ) k') hh.le
  fin_cases a <;> fin_cases b
  all_goals try norm_num at hab
  all_goals norm_num [start, Fin.ext_iff]
  all_goals linarith

/-- Prime factorization prevents any collision between the four coordinates. -/
theorem tuple_eq_of_product_eq {N i j k i' j' k' : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hi' : i' ∈ grid N h) (hj' : j' ∈ grid N h) (hk' : k' ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p q : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j k) (hq : q ∈ tuples N h v i' j' k')
    (he : (∏ a, p a) = ∏ a, q a) : p = q := by
  funext a
  have hpa := (tuple_bounds hp a).1
  have hd : p a ∣ ∏ b, q b := by rw [← he]; exact Finset.dvd_prod_of_mem p (Finset.mem_univ a)
  obtain ⟨b,_,hb⟩ := (hpa.prime.dvd_finsetProd_iff q).mp hd
  have heq := (Nat.prime_dvd_prime_iff_eq hpa (tuple_bounds hq b).1).mp hb
  have hab : a = b := by
    rcases lt_trichotomy a b with hab | hab | hab
    · exact False.elim ((coordinate_order hh hi hj hk hi' hj' hk' hv hw hp hq hab).ne heq)
    · exact hab
    · exact False.elim ((coordinate_order hh hi' hj' hk' hi hj hk hv hw hq hp hab).ne heq.symm)
  simpa only [hab] using heq

theorem products_card {N i j k : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000) :
    (products N h v i j k).card = ∏ a, (logPrimes (start N h v i j k a) h).card := by
  rw [products, Finset.card_image_of_injOn (fun p hp q hq he =>
    tuple_eq_of_product_eq hh hi hj hk hi hj hk hv hw hp hq he)]
  simp [tuples]

theorem tuple_squarefree {N i j k : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j k) : Squarefree (∏ a, p a) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a _ b _ hab
    apply Nat.coprime_iff_isRelPrime.mp
    apply (tuple_bounds hp a).1.coprime_iff_not_dvd.mpr
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq (tuple_bounds hp a).1 (tuple_bounds hp b).1).mp hd
    rcases lt_or_gt_of_ne hab with ht | ht
    · exact (coordinate_order hh hi hj hk hi hj hk hv hw hp hp ht).ne he
    · exact (coordinate_order hh hi hj hk hi hj hk hv hw hp hp ht).ne he.symm
  · intro a _
    exact (tuple_bounds hp a).1.squarefree

theorem tuple_log {N i j k : ℕ} {h v : ℝ} {p : Fin 4 → ℕ}
    (hp : p ∈ tuples N h v i j k) : Real.log (∏ a, p a : ℕ) = ∑ a, Real.log (p a) := by
  rw [Nat.cast_prod, Real.log_prod]
  intro a _
  exact_mod_cast (tuple_bounds hp a).1.ne_zero

theorem tuple_log_bounds {N i j k : ℕ} {h v : ℝ} {p : Fin 4 → ℕ}
    (hp : p ∈ tuples N h v i j k) :
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

theorem tuple_primeFactors {N i j k : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j k) :
    (∏ a, p a).primeFactors = Finset.univ.image p := by
  have hinj : Function.Injective p :=
    (show StrictMono p from fun _ _ hab => coordinate_order hh hi hj hk hi hj hk hv hw hp hp hab).injective
  rw [← Finset.prod_image (f := fun n : ℕ => n) (s := Finset.univ) hinj.injOn]
  apply Nat.primeFactors_prod
  intro a ha
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
  exact (tuple_bounds hp b).1

theorem tuple_count {N i j k : ℕ} {h v : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j k) :
    (∏ a, p a).primeFactors.card = 4 := by
  rw [tuple_primeFactors hh hi hj hk hv hw hp, Finset.card_image_of_injective _
    (show StrictMono p from fun _ _ hab => coordinate_order hh hi hj hk hi hj hk hv hw hp hp hab).injective]
  simp

/-- Every actual box label lies in the already evaluated reflected class. -/
theorem tuple_linear {N i j k : ℕ} {h v L : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j k) : LinearClass L (∏ a, p a) := by
  have hl := tuple_log_bounds hp
  have hn := Nat.cast_nonneg (α := ℝ) N
  refine ⟨tuple_squarefree hh hi hj hk hv hw hp,by rw [tuple_count hh hi hj hk hv hw hp]; norm_num,
    by linarith [hl.1],?_⟩
  intro q hq
  rw [tuple_primeFactors hh hi hj hk hv hw hp] at hq
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
  have hs := start_bounds hh hi hj hk hv hw a
  have hb := tuple_bounds hp a
  constructor <;> linarith [hl.1,hl.2]

/-- On this chamber the original coefficient is uniformly negative. -/
theorem tuple_coefficient_le {N i j k : ℕ} {h v L : ℝ} (hh : 0 < h)
    (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000)
    (hL0 : 0 < L) (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j k) :
    (SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re ≤ -(N : ℝ)/20 := by
  have ht := tuple_log_bounds hp
  have hclass := tuple_linear hh hi hj hk hv hw hL hLu hp
  rw [coefficient_eq_linear hclass, Complex.ofReal_re,
    linearCoefficient_four hclass (tuple_count hh hi hj hk hv hw hp)]
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

/-- Each actual integer appears in at most one supply cell. -/
theorem products_disjoint {N : ℕ} {h v : ℝ} (hh : 0 < h)
    (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000) :
    (cells N h : Set (ℕ × ℕ × ℕ)).PairwiseDisjoint
      (fun ijk => products N h v ijk.1 ijk.2.1 ijk.2.2) := by
  intro ijk hijk abc habc hne
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨ha,hbc⟩ := Finset.mem_product.mp habc
  obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn
  obtain ⟨q,hq,hqn⟩ := Finset.mem_image.mp hn'
  have he := tuple_eq_of_product_eq hh hi hj hk ha hb hc hv hw hp hq (hpn.trans hqn.symm)
  subst q
  have bp := tuple_bounds hp 0
  have bq := tuple_bounds hq 0
  have cp := tuple_bounds hp 1
  have cq := tuple_bounds hq 1
  have dp := tuple_bounds hp 2
  have dq := tuple_bounds hq 2
  norm_num [start,Fin.ext_iff] at bp bq cp cq dp dq
  have he0 := interval_index_eq hh bp.2.1 bp.2.2 bq.2.1 bq.2.2
  have he1 := interval_index_eq hh cp.2.1 cp.2.2 cq.2.1 cq.2.2
  have he2 := interval_index_eq hh dp.2.1 dp.2.2 dq.2.1 dq.2.2
  exact hne (Prod.ext he0 (Prod.ext he1 he2))

/-- The three-dimensional union gains three powers of the moment order.
All labels are distinct actual products of four ordinary primes. -/
theorem eventually_supply_card_lower {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ C →
      c*Real.exp (2*(N : ℝ))/((N : ℝ)+1) ≤ (supply N h v).card := by
  obtain ⟨c,hc,hcounts⟩ := ZetaRieszQuadrupleCompensation.eventually_interval_card_lower hh
  refine ⟨c^4/(500*h)^3,by positivity,?_⟩
  filter_upwards [hcounts,eventually_ge_atTop (1 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (4000*(h+C))]
    with N hcount hN hsize v hv hvC
  have hw : h+v ≤ (N : ℝ)/1000 := by linarith
  have hc0 := Nat.cast_nonneg (α := ℝ) N
  have hc1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let M := ⌊(N : ℝ)/(125*h)⌋₊
  have hfloor : (N : ℝ)/(125*h) < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hM : ((N : ℝ)+1)/(500*h) ≤ M := by
    apply (div_le_iff₀ (by positivity : 0 < 500*h)).mpr
    have ht := (div_lt_iff₀ (by positivity : 0 < 125*h)).mp hfloor
    nlinarith
  have hbox (ij : ℕ × ℕ × ℕ) (hij : ij ∈ cells N h) :
      c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4 ≤ (products N h v ij.1 ij.2.1 ij.2.2).card := by
    obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hij
    obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
    rw [products_card hh hi hj hk hv hw, Nat.cast_prod]
    have he (a : Fin 4) : c*Real.exp (start N h v ij.1 ij.2.1 ij.2.2 a)/((N : ℝ)+1) ≤
        ((logPrimes (start N h v ij.1 ij.2.1 ij.2.2 a) h).card : ℝ) := by
      have hs := start_bounds hh hi hj hk hv hw a
      exact hcount _ (by linarith) (by linarith)
    have hp := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 4)))
      (fun a _ => by positivity : ∀ a ∈ (Finset.univ : Finset (Fin 4)),
        0 ≤ c*Real.exp (start N h v ij.1 ij.2.1 ij.2.2 a)/((N : ℝ)+1))
      (fun a _ => he a)
    have hex : (∏ a : Fin 4, Real.exp (start N h v ij.1 ij.2.1 ij.2.2 a)) =
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
      ∑ ij ∈ cells N h, (products N h v ij.1 ij.2.1 ij.2.2).card :=
    Finset.card_biUnion (products_disjoint hh hv hw)
  rw [hcard,Nat.cast_sum]
  apply le_trans ?_ hs
  simp only [cells,Finset.product_eq_sprod,Finset.card_product,grid,
    Finset.card_range,Nat.cast_mul]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ((N : ℝ)+1)/(500*h)) hM 3
  have hm := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4 by positivity)
  calc
    _ = (((N : ℝ)+1)/(500*h))^3*
        (c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4) := by field_simp
    _ ≤ (M : ℝ)^3*(c^4*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^4) := hm
    _ = _ := by dsimp only [M]; ring

open ZetaRieszQuadrupleCompensation (saddleEnvelope saddleEnvelope_nonneg saddleEnvelope_pos)

/-- The original allocated atom is positive on the selected phase window. -/
theorem tuple_atom_lower (A : Finset ℕ) {N i j k : ℕ} {h v C L y : ℝ}
    (hh : 0 < h) (hi : i ∈ grid N h) (hj : j ∈ grid N h) (hk : k ∈ grid N h)
    (hv : 0 ≤ v) (hvC : v ≤ C) (hw : h+v ≤ (N : ℝ)/1000)
    (hL0 : 0 < L) (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hshare : (1/2 : ℝ) ≤ 1-4*Real.exp (-(N : ℝ)/64))
    {p : Fin 4 → ℕ} (hp : p ∈ tuples N h v i j k)
    (hcos : Real.cos (y*Real.log (∏ a, p a : ℕ)) ≤ -(1/2 : ℝ)) :
    (N : ℝ)/80*Real.exp (-(3/2 : ℝ)*(C+4*h))*saddleEnvelope N ≤
      (residualCoefficient A L N (∏ a, p a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ a, p a)).re := by
  have ht := tuple_log_bounds hp
  have hs := tuple_squarefree hh hi hj hk hv hw hp
  have hcnt := tuple_count hh hi hj hk hv hw hp
  have hn1 : 1 < ∏ a, p a := by
    apply (tuple_bounds hp 0).1.one_lt.trans_le
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Finset.dvd_prod_of_mem p (Finset.mem_univ 0))
  have hbal : ∀ q ∈ (∏ a, p a).primeFactors, Real.log q ≤ Real.log (∏ a, p a : ℕ)/2 := by
    intro q hq
    rw [tuple_primeFactors hh hi hj hk hv hw hp] at hq
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
    have hb := tuple_bounds hp a
    have hst := start_bounds hh hi hj hk hv hw a
    linarith [ht.1,Nat.cast_nonneg (α := ℝ) N]
  have hwgt := balanced_weight_lower A N hs hn1 hbal
  rw [hcnt] at hwgt
  norm_num only [Nat.cast_ofNat] at hwgt
  have hamp := ZetaRieszCosineCarrier.factorial_envelope_nonneg N (∏ a, p a)
  change 0 ≤ amplitude N (∏ a, p a) at hamp
  have hhalf : amplitude N (∏ a, p a)/2 ≤ weight A N (∏ a, p a) := by nlinarith
  have hc := tuple_coefficient_le hh hi hj hk hv hw hL0 hL hLu hp
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
      c*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)*saddleEnvelope N ≤
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
    obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hij
    obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hb := tuple_log_bounds hp
    exact tuple_atom_lower A hh hi hj hk hv hvC hw hL0 hL hLu (by linarith) hp
      (hphase _ hb.1.le hb.2)
  have hsum := Finset.sum_le_sum ha
  rw [Finset.sum_const,nsmul_eq_mul,← Complex.re_sum] at hsum
  have hscale := mul_le_mul_of_nonneg_right (hcN v hv hvC)
    (show 0 ≤ (N : ℝ)/80*Real.exp (-(3/2 : ℝ)*(C+4*h))*saddleEnvelope N by
      positivity [saddleEnvelope_nonneg N])
  exact (le_of_eq (by ring)).trans (hscale.trans hsum)

/-- A literal subset of the existing finite carrier. The total-log
window has width one, while every prime-log window has width `2 η N`.
No completion or replacement of the coefficient is made. -/
def tripleBand (S : Finset ℕ) (N : ℕ) (η : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 3 ∧
    2*(N : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(N : ℝ)+1 ∧
      ∀ p ∈ n.primeFactors, |Real.log p-(2/3 : ℝ)*N| ≤ η*N)

/-- Fixed-width covering cells are used only for an upper count of the
literal triple band; their possible overlaps are not counted as supply. -/
private def coverGrid (N : ℕ) (η : ℝ) : Finset ℕ := Finset.range (⌊2*η*N⌋₊+1)

private def coverStart (N : ℕ) (η : ℝ) (i j : ℕ) (a : Fin 3) : ℝ :=
  if a = 0 then (2/3-η)*N+i-1
  else if a = 1 then (2/3-η)*N+j-1
  else (2/3+2*η)*N-i-j-3

private def coverWidth (a : Fin 3) : ℝ := if a = 2 then 6 else 2

private def coverTuples (N : ℕ) (η : ℝ) (i j : ℕ) : Finset (Fin 3 → ℕ) :=
  Fintype.piFinset (fun a => logPrimes (coverStart N η i j a) (coverWidth a))

private def coverProducts (N : ℕ) (η : ℝ) (i j : ℕ) : Finset ℕ :=
  (coverTuples N η i j).image (fun p => ∏ a, p a)

private theorem coverGrid_bound {N i : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hi : i ∈ coverGrid N η) : (i : ℝ) ≤ 2*η*N := by
  have hh : i ≤ ⌊2*η*N⌋₊ := by simpa only [coverGrid,Finset.mem_range,Nat.lt_add_one_iff] using hi
  exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (by positivity))

private theorem logPrimes_mem {p : ℕ} (hp : p.Prime) {a h : ℝ}
    (hlo : a < Real.log p) (hhi : Real.log p ≤ a+h) : p ∈ logPrimes a h := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
  · apply (Nat.floor_lt (Real.exp_nonneg a)).mpr
    simpa only [Real.exp_log hpR] using Real.exp_lt_exp.mpr hlo
  · apply (Nat.le_floor_iff (mul_nonneg (Real.exp_nonneg h) (Real.exp_nonneg a))).mpr
    simpa only [Real.exp_add,Real.exp_log hpR,mul_comm] using
      Real.exp_le_exp.mpr hhi

/-- Every actual balanced triple enters this finite cover, including
prime logs on the boundaries of the wider band. -/
private theorem tripleBand_subset_cover (S : Finset ℕ) (N : ℕ) (η : ℝ) :
    tripleBand S N η ⊆ ((coverGrid N η).product (coverGrid N η)).biUnion
      (fun ij => coverProducts N η ij.1 ij.2) := by
  intro n hn
  obtain ⟨_,hs,hc,htlo,hthi,hbal⟩ := Finset.mem_filter.mp hn
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,he⟩ := ZetaRieszTriplePrime.exists_three_primes hs hc
  have hplog : |Real.log p-(2/3 : ℝ)*N| ≤ η*N := hbal p
    (Nat.mem_primeFactors.mpr ⟨hp,by rw [he]; exact dvd_mul_right _ _,hs.ne_zero⟩)
  have hqlog : |Real.log q-(2/3 : ℝ)*N| ≤ η*N := hbal q
    (Nat.mem_primeFactors.mpr ⟨hq,by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _,hs.ne_zero⟩)
  have hslog : Real.log n = Real.log p+Real.log q+Real.log r := by
    rw [he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
    ring
  let i := ⌊Real.log p-(2/3-η)*N⌋₊
  let j := ⌊Real.log q-(2/3-η)*N⌋₊
  have hp0 : 0 ≤ Real.log p-(2/3-η)*N := by nlinarith [(abs_le.mp hplog).1]
  have hq0 : 0 ≤ Real.log q-(2/3-η)*N := by nlinarith [(abs_le.mp hqlog).1]
  have hip : (i : ℝ) ≤ Real.log p-(2/3-η)*N := Nat.floor_le hp0
  have hiu : Real.log p-(2/3-η)*N < (i : ℝ)+1 := Nat.lt_floor_add_one _
  have hjp : (j : ℝ) ≤ Real.log q-(2/3-η)*N := Nat.floor_le hq0
  have hju : Real.log q-(2/3-η)*N < (j : ℝ)+1 := Nat.lt_floor_add_one _
  have hi : i ∈ coverGrid N η := by
    apply Finset.mem_range.mpr
    apply Nat.lt_add_one_of_le
    exact Nat.floor_le_floor (by nlinarith [(abs_le.mp hplog).2])
  have hj : j ∈ coverGrid N η := by
    apply Finset.mem_range.mpr
    apply Nat.lt_add_one_of_le
    exact Nat.floor_le_floor (by nlinarith [(abs_le.mp hqlog).2])
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,j),Finset.mem_product.mpr ⟨hi,hj⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨![p,q,r],?_,?_⟩
  · apply Fintype.mem_piFinset.mpr
    intro a
    fin_cases a
    · apply logPrimes_mem hp <;> norm_num [coverStart,coverWidth,Fin.ext_iff] <;> linarith
    · apply logPrimes_mem hq <;> norm_num [coverStart,coverWidth,Fin.ext_iff] <;> linarith
    · apply logPrimes_mem hr <;> norm_num [coverStart,coverWidth,Fin.ext_iff] <;> nlinarith
  · simpa [Fin.prod_univ_succ] using he.symm

private theorem coverStart_bounds {N i j : ℕ} {η : ℝ} (hη : 0 ≤ η) (hηu : η ≤ 1/1000)
    (hN : 20 ≤ N) (hi : i ∈ coverGrid N η) (hj : j ∈ coverGrid N η) (a : Fin 3) :
    (N : ℝ)/3 ≤ coverStart N η i j a ∧ coverStart N η i j a ≤ N := by
  have hib := coverGrid_bound hη hi
  have hjb := coverGrid_bound hη hj
  have hi0 := Nat.cast_nonneg (α := ℝ) i
  have hj0 := Nat.cast_nonneg (α := ℝ) j
  have hN0 := Nat.cast_nonneg (α := ℝ) N
  have hN20 : (20 : ℝ) ≤ N := by exact_mod_cast hN
  have hηN := mul_le_mul_of_nonneg_right hηu hN0
  have hηN0 := mul_nonneg hη hN0
  fin_cases a <;> norm_num [coverStart,Fin.ext_iff] <;> constructor <;> nlinarith

/-- A uniform upper count using only the existing Chebyshev theorem.
It retains the exponential of each cell start, so the three starts
cancel their independent log translations when multiplied. -/
private theorem interval_card_upper_uniform {N : ℕ} (hN : 1 ≤ N) {a h : ℝ}
    (ha : (N : ℝ)/3 ≤ a) (hh : 0 ≤ h) :
    ((logPrimes a h).card : ℝ) ≤ 6*Real.log 4*Real.exp h*Real.exp a/((N : ℝ)+1) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hapos : 0 < a := by linarith
  have hb := ZetaRieszQuadrupleCompensation.interval_card_upper hapos hh
  have hden : ((N : ℝ)+1)/6 ≤ a := by linarith
  calc
    _ ≤ Real.log 4*Real.exp (a+h)/a := hb
    _ ≤ Real.log 4*Real.exp (a+h)/(((N : ℝ)+1)/6) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by rw [Real.exp_add]; field_simp

private theorem coverProducts_card_upper {N i j : ℕ} {η : ℝ}
    (hη : 0 ≤ η) (hηu : η ≤ 1/1000) (hN : 20 ≤ N)
    (hi : i ∈ coverGrid N η) (hj : j ∈ coverGrid N η) :
    ((coverProducts N η i j).card : ℝ) ≤
      (6*Real.log 4)^3*Real.exp 5*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3 := by
  have hc : ((coverProducts N η i j).card : ℝ) ≤
      ((coverTuples N η i j).card : ℝ) := by exact_mod_cast Finset.card_image_le
  have hp := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3)))
    (fun a _ => Nat.cast_nonneg (α := ℝ) ((logPrimes (coverStart N η i j a) (coverWidth a)).card))
    (fun a _ => interval_card_upper_uniform (show 1 ≤ N by omega)
      (coverStart_bounds hη hηu hN hi hj a).1 (by unfold coverWidth; split_ifs <;> norm_num))
  have he : (∏ a : Fin 3, Real.exp (coverWidth a)*Real.exp (coverStart N η i j a)) =
      Real.exp 5*Real.exp (2*(N : ℝ)) := by
    simp_rw [← Real.exp_add]
    rw [← Real.exp_sum]
    congr 1
    simp only [Fin.sum_univ_three]
    norm_num [coverWidth,coverStart,Fin.ext_iff]
    ring
  rw [coverTuples,Fintype.card_piFinset,Nat.cast_prod] at hc
  refine hc.trans (hp.trans_eq ?_)
  simp_rw [mul_assoc (6*Real.log 4)]
  rw [Finset.prod_div_distrib,Finset.prod_mul_distrib,he]
  simp [mul_assoc]

/-- A whole balanced triple band has a quadratic width cost. The width
is proportional to N, not a fixed log box and not a vanishing share band. -/
theorem tripleBand_card_upper (S : Finset ℕ) {N : ℕ} {η : ℝ}
    (hη : 0 < η) (hηu : η ≤ 1/1000) (hN : 20 ≤ N) (hηN : 1 ≤ η*N) :
    ((tripleBand S N η).card : ℝ) ≤
      (9*(6*Real.log 4)^3*Real.exp 5)*η^2*Real.exp (2*(N : ℝ))/((N : ℝ)+1) := by
  have hcover := Finset.card_le_card (tripleBand_subset_cover S N η)
  have hcount := Finset.card_biUnion_le (s := (coverGrid N η).product (coverGrid N η))
    (t := fun ij => coverProducts N η ij.1 ij.2)
  have hsum := Finset.sum_le_sum (s := (coverGrid N η).product (coverGrid N η))
    (fun ij hij => coverProducts_card_upper hη.le hηu hN
      (Finset.mem_product.mp hij).1 (Finset.mem_product.mp hij).2)
  have hs : ((tripleBand S N η).card : ℝ) ≤
      ∑ ij ∈ (coverGrid N η).product (coverGrid N η), ((coverProducts N η ij.1 ij.2).card : ℝ) := by
    exact_mod_cast hcover.trans hcount
  apply (hs.trans hsum).trans
  rw [Finset.sum_const,nsmul_eq_mul,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  have hM : ((coverGrid N η).card : ℝ) ≤ 3*η*((N : ℝ)+1) := by
    simp only [coverGrid,Finset.card_range,Nat.cast_add,Nat.cast_one]
    have hfloor := Nat.floor_le (show 0 ≤ 2*η*N by positivity)
    nlinarith
  have hsq := mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) ((coverGrid N η).card)) hM
  have hm := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ (6*Real.log 4)^3*Real.exp 5*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3 by positivity)
  exact hm.trans_eq (by field_simp; ring)

/-- The quadratic width count bounds the literal triple-band mass.
Only this paid debit is bounded by modulus; its signed complement and
all unused positive supply remain in the eventual spending identity. -/
theorem tripleBand_norm_upper (S A : Finset ℕ) {N : ℕ} {η L : ℝ}
    (hη : 0 < η) (hηu : η ≤ 1/1000) (hN : 20 ≤ N) (hηN : 1 ≤ η*N)
    (hL : 0 < L) (hNL : (N : ℝ) ≤ L) (y : ℝ) :
    ‖∑ n ∈ tripleBand S N η, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (27*(6*Real.log 4)^3*Real.exp (11/2 : ℝ))*η^2*
        (N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)*saddleEnvelope N := by
  have hbound (n : ℕ) (hn : n ∈ tripleBand S N η) :
      ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        3*(N : ℝ)*Real.exp (1/2 : ℝ)*saddleEnvelope N := by
    have hh := (Finset.mem_filter.mp hn).2
    exact ZetaRieszQuadrupleCompensation.triple_atom_norm_upper A (by omega) hL hNL hh.1 hh.2.1
      (by exact_mod_cast (show 1 ≤ N by omega)) hh.2.2.1 hh.2.2.2.1
  have hc := tripleBand_card_upper S hη hηu hN hηN
  have hs := (norm_sum_le _ _).trans (Finset.sum_le_sum hbound)
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 3*(N : ℝ)*Real.exp (1/2 : ℝ)*saddleEnvelope N by positivity [saddleEnvelope_nonneg N])
  apply hs.trans (hm.trans_eq ?_)
  have he : Real.exp 5*Real.exp (1/2 : ℝ) = Real.exp (11/2 : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  calc
    _ = (27*(6*Real.log 4)^3*(Real.exp 5*Real.exp (1/2 : ℝ)))*η^2*
        (N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)*saddleEnvelope N := by ring
    _ = _ := by rw [he]

/-- A fixed positive share-width can be chosen so that its ENTIRE
actual triple band costs at most half the positive supply. Unlike the
previous fixed-width box, every prime-log interval grows linearly with N.
The remaining signed carrier is not estimated or discarded. -/
theorem eventually_band_spending {y : ℝ} (hy : y ≠ 0) :
    ∃ η h C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (L : ℝ),
        0 < L → (137/100 : ℝ)*N ≤ L → L ≤ (7/5 : ℝ)*N →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          0 < (∑ n ∈ supply N h v, f n).re ∧
            ‖∑ n ∈ tripleBand S N η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply N h v, f n).re := by
  obtain ⟨h,C,hh,hC,hphase⟩ := ZetaRieszCompensationSupply.exists_negative_phase_window hy
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_real_lower hh hC
  let B : ℝ := 27*(6*Real.log 4)^3*Real.exp (11/2 : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  let η := min (1/1000 : ℝ) (Real.sqrt (c/(2*B)))
  have hη : 0 < η := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hηu : η ≤ 1/1000 := min_le_left _ _
  have hηcost : B*η^2 ≤ c/2 := by
    have hs := pow_le_pow_left₀ hη.le (min_le_right (1/1000 : ℝ) (Real.sqrt (c/(2*B)))) 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have ht := (le_div_iff₀ (by positivity : 0 < 2*B)).mp hs
    nlinarith
  refine ⟨η,h,C,hη,hηu,hh,hC,?_⟩
  filter_upwards [hsupply,eventually_ge_atTop (20 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1/η)]
    with N hs hN hsize S A L hL0 hL hLu
  have hηN : 1 ≤ η*N := by
    have ht := (div_le_iff₀ hη).mp hsize
    nlinarith
  obtain ⟨v,hv,hvC,hcos⟩ := hphase (2*(N : ℝ))
  have hpos := hs A v L y hv hvC hL0 hL hLu
    (fun t hlo hhi => hcos t hlo (by linarith))
  have hneg := tripleBand_norm_upper S A hη hηu hN hηN hL0
    (by nlinarith [Nat.cast_nonneg (α := ℝ) N]) y
  refine ⟨v,hv,hvC,?_⟩
  dsimp only
  refine ⟨lt_of_lt_of_le (by positivity [saddleEnvelope_pos (show 0 < N by omega)]) hpos,?_⟩
  calc
    _ ≤ B*η^2*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)*saddleEnvelope N := hneg
    _ ≤ (c/2)*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)*saddleEnvelope N := by
      have hh' := mul_le_mul_of_nonneg_right hηcost
        (show 0 ≤ (N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)*saddleEnvelope N by
          positivity [saddleEnvelope_nonneg N])
      convert hh' using 1 <;> first | rfl | ring
    _ = (1/2 : ℝ)*(c*(N : ℝ)*Real.exp (2*(N : ℝ))/((N : ℝ)+1)*saddleEnvelope N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpos (by norm_num)

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
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hij
  obtain ⟨hj',hk'⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  let N := dyadicMomentOrder j
  have hw : h+v ≤ (N : ℝ)/1000 := by dsimp [N]; linarith
  have hs := tuple_squarefree hh hi hj' hk' hv hw hp
  have hk := tuple_count hh hi hj' hk' hv hw hp
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
      rw [tuple_primeFactors hh hi hj' hk' hv hw hp] at hq
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
      have hb' := tuple_bounds hp a
      have hst := start_bounds hh hi hj' hk' hv hw a
      linarith [hb.1])
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hcore,by constructor <;> linarith [hwin.1,hwin.2]⟩,hwin⟩

/-- The paid triple population and the supply are disjoint by their
actual prime counts, independently of the phase or coefficient sign. -/
theorem tripleBand_supply_disjoint (S : Finset ℕ) {N : ℕ} (η : ℝ) {h v : ℝ}
    (hh : 0 < h) (hv : 0 ≤ v) (hw : h+v ≤ (N : ℝ)/1000) :
    Disjoint (tripleBand S N η) (supply N h v) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hthree := (Finset.mem_filter.mp hn).2.2.1
  obtain ⟨ijk,hijk,hn'⟩ := Finset.mem_biUnion.mp hn'
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn'
  have hfour := tuple_count hh hi hj hk hv hw hp
  rw [hpn] at hfour
  omega

/-- Exact spending in the unchanged full core: the growing balanced
triple band is paid by at most half the positive four-prime supply.
All positive triple credit, the other half (or more) of the supply, and
the complete signed complement remain. This is not a floor for that rest. -/
theorem eventually_core_band_spending {u y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : y ≠ 0) :
    ∃ η h C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let X := ∑ n ∈ tripleBand S N η, f n
        let Y := ∑ n ∈ supply N h v, f n
        let W := ∑ n ∈ S\(tripleBand S N η ∪ supply N h v), f n
        let θ := max (-X.re) 0/Y.re
        0 < Y.re ∧ 0 ≤ θ ∧ θ ≤ 1/2 ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re =
            u^(N+1)*(W.re+max X.re 0+(1-θ)*Y.re) := by
  obtain ⟨η,h,C,hη,hηu,hh,hC,hpay⟩ := eventually_band_spending hy
  refine ⟨η,h,C,hη,hηu,hh,hC,?_⟩
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    eventually_supply_in_core hu hU hh hC,
    tendsto_dyadicMomentOrder.eventually hL,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 2),
    hord.eventually_ge_atTop (1000*(h+C))]
    with j hj hs hL hN hsize
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hLu : L ≤ (7/5 : ℝ)*N := by
    have he := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    dsimp only [L,N]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]
  obtain ⟨v,hv,hvC,hY,hpaid⟩ := hj S A L (SquarefreeVaughanLogSource.length_pos _ _)
    (by dsimp [L,N]; linarith [hL]) hLu
  refine ⟨v,hv,hvC,?_⟩
  let X := ∑ n ∈ tripleBand S N η, f n
  let Y := ∑ n ∈ supply N h v, f n
  let W := ∑ n ∈ S\(tripleBand S N η ∪ supply N h v), f n
  let θ := max (-X.re) 0/Y.re
  change 0 < Y.re ∧ 0 ≤ θ ∧ θ ≤ 1/2 ∧
    ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re =
      u^(N+1)*(W.re+max X.re 0+(1-θ)*Y.re)
  obtain ⟨hθ,hθhalf,_hθone,hledger⟩ :=
    ZetaRieszQuadrupleCompensation.signed_spending (X := X) (Y := Y) (W := W)
      hY (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) hpaid
  refine ⟨hY,hθ,hθhalf,?_⟩
  have hw : h+v ≤ (N : ℝ)/1000 := by dsimp [N]; linarith
  have hd := tripleBand_supply_disjoint S η hh hv hw
  have hsub : tripleBand S N η ∪ supply N h v ⊆ S :=
    Finset.union_subset (Finset.filter_subset _ _) (hs v hv hvC)
  have he := Finset.sum_sdiff (f := f) hsub
  rw [Finset.sum_union hd] at he
  have he' : coreResponse u y N (dyadicPrimeCount j) = W+(X+Y) := he.symm
  rw [he']
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using congrArg (fun t : ℝ => u^(N+1)*t) hledger

/-- A direct lower bound for the unchanged core: after paying the entire
triple band, at least half the positive supply and all signed complement
remain. It does not assume or estimate a separate bound for either part. -/
theorem eventually_core_band_floor {u y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : y ≠ 0) :
    ∃ η h C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let X := ∑ n ∈ tripleBand S N η, f n
        let Y := ∑ n ∈ supply N h v, f n
        let W := ∑ n ∈ S\(tripleBand S N η ∪ supply N h v), f n
        u^(N+1)*(W.re+max X.re 0+Y.re/2) ≤
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,C,hη,hηu,hh,hC,hpay⟩ := eventually_core_band_spending hu hU hy
  refine ⟨η,h,C,hη,hηu,hh,hC,?_⟩
  filter_upwards [hpay] with j hj
  obtain ⟨v,hv,hvC,hY,_hθ,hθhalf,he⟩ := hj
  refine ⟨v,hv,hvC,?_⟩
  dsimp only at he hY hθhalf ⊢
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
  nlinarith

/-- Every sufficiently narrow fixed box at the saddle is contained in
the new band once its width `η N` exceeds one quarter. This checks the
selection against the original balanced boxes rather than a model. -/
theorem fixed_box_subset_tripleBand (S : Finset ℕ) {N : ℕ} {η : ℝ}
    (hηN : (1/4 : ℝ) ≤ η*N)
    (hsub : tripleProducts ((2/3 : ℝ)*N) (1/12) ⊆ S) :
    tripleProducts ((2/3 : ℝ)*N) (1/12) ⊆ tripleBand S N η := by
  intro n hn
  have hb := tripleProducts_bounds (by norm_num : (0 : ℝ) ≤ 1/12) hn
  have hc : n.primeFactors.card = 3 := hb.2.1
  have hu (p : ℕ) (hp : p ∈ n.primeFactors) : Real.log p ≤ (2/3 : ℝ)*N+1/4 := by
    have h := hb.2.2.2.2 p hp
    linarith
  apply Finset.mem_filter.mpr
  refine ⟨hsub hn,hb.1,hc,by linarith [hb.2.2.1],by linarith [hb.2.2.2.1],?_⟩
  intro p hp
  have hcard : (n.primeFactors.erase p).card = 2 := by rw [Finset.card_erase_of_mem hp,hc]
  have hs := Finset.sum_le_sum (s := n.primeFactors.erase p)
    (fun q hq => hu q (Finset.mem_of_mem_erase hq))
  rw [Finset.sum_const,nsmul_eq_mul,hcard] at hs
  norm_num only [Nat.cast_ofNat] at hs
  have he := Finset.sum_erase_add n.primeFactors (fun q : ℕ => Real.log q) hp
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hb.1] at he
  apply abs_le.mpr
  constructor <;> linarith [hu p hp,hb.2.2.1]

/-- The actual selected band is eventually nonempty for every fixed
positive width. The proof uses ordinary prime counts and its inclusion
of the original three-prime boxes. -/
theorem eventually_core_tripleBand_nonempty {u η : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hη : 0 < η) :
    ∀ᶠ j : ℕ in atTop,
      (tripleBand (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
        (dyadicMomentOrder j) η).Nonempty := by
  obtain ⟨c,hc,hcount⟩ := eventually_logPrimes_card_lower
    (by norm_num : (0 : ℝ) < 1/12) (by norm_num : (0 : ℝ) ≤ 1/6)
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [tendsto_dyadicMomentOrder.eventually hcount,
    ZetaRieszJointPhaseCredit.eventually_boxes_in_core hu hU
      (by norm_num : (0 : ℝ) ≤ 1/12) (by norm_num : (0 : ℝ) ≤ 0),
    hord.eventually_ge_atTop (1/(4*η))] with j hcounts hcore hsize
  let N := dyadicMomentOrder j
  let a : ℝ := (2/3)*N
  have hprime (b : ℝ) (hb : a ≤ b) (hbu : b ≤ a+1/6) : (logPrimes b (1/12)).Nonempty := by
    have hh := hcounts b hb hbu
    have hp : (0 : ℝ) < (logPrimes b (1/12)).card := lt_of_lt_of_le (by positivity) hh
    exact Finset.card_pos.mp (Nat.cast_pos.mp hp)
  have ht : (tripleProducts a (1/12)).Nonempty := by
    apply Finset.card_pos.mp
    rw [tripleProducts_card (by norm_num : (0 : ℝ) ≤ 1/12)]
    exact Nat.mul_pos
      (Nat.mul_pos (Finset.card_pos.mpr (hprime a le_rfl (by linarith)))
        (Finset.card_pos.mpr (hprime (a+1/12) (by linarith) (by linarith))))
      (Finset.card_pos.mpr (hprime (a+2*(1/12)) (by linarith) (by linarith)))
  have hηN : (1/4 : ℝ) ≤ η*N := by
    have h := (div_le_iff₀ (by positivity : 0 < 4*η)).mp hsize
    dsimp [N]
    nlinarith
  exact ht.mono (fixed_box_subset_tripleBand _ hηN
    (hcore a le_rfl (by dsimp [a,N]; linarith)).2.2)

end
end RiemannGaussian.ZetaRieszBandCompensation
