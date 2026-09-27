/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBandCompensation

/-!
# Signed compensation throughout the radial core

The original moment order is retained while the existing four-prime
supply moves between disjoint radial slabs. Actual interval counts pay
balanced triples in each slab. Every unused credit and the signed rest
remain in one lower bound; no signed prime-density transport is used.
-/

namespace RiemannGaussian.ZetaRieszRadialCompensation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation
open ZetaRieszOneSidedArithmetic ZetaRieszAllowanceComplement
open ZetaRieszReflectedLinear ZetaRieszBandCompensation

/-- The existing supply chamber admits the full required length range. -/
theorem tuple_linear_wide {M i j k : ℕ} {h v L : ℝ} (hh : 0 < h)
    (hi : i ∈ grid M h) (hj : j ∈ grid M h) (hk : k ∈ grid M h)
    (hv : 0 ≤ v) (hw : h+v ≤ (M : ℝ)/1000)
    (hL : (271/200 : ℝ)*M ≤ L) (hLu : L ≤ (143/100 : ℝ)*M)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples M h v i j k) : LinearClass L (∏ a, p a) := by
  have hl := tuple_log_bounds hp
  have hn := Nat.cast_nonneg (α := ℝ) M
  refine ⟨tuple_squarefree hh hi hj hk hv hw hp,by rw [tuple_count hh hi hj hk hv hw hp]; norm_num,
    by linarith [hl.1],?_⟩
  intro q hq
  rw [tuple_primeFactors hh hi hj hk hv hw hp] at hq
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
  have hs := start_bounds hh hi hj hk hv hw a
  have hb := tuple_bounds hp a
  constructor <;> linarith [hl.1,hl.2]

/-- The coefficient stays negative as the radial centre moves across the core. -/
theorem tuple_coefficient_le_wide {M i j k : ℕ} {h v L : ℝ} (hh : 0 < h)
    (hi : i ∈ grid M h) (hj : j ∈ grid M h) (hk : k ∈ grid M h)
    (hv : 0 ≤ v) (hw : h+v ≤ (M : ℝ)/1000)
    (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (hLu : L ≤ (143/100 : ℝ)*M)
    {p : Fin 4 → ℕ} (hp : p ∈ tuples M h v i j k) :
    (SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re ≤ -(M : ℝ)/20 := by
  have ht := tuple_log_bounds hp
  have hclass := tuple_linear_wide hh hi hj hk hv hw hL hLu hp
  rw [coefficient_eq_linear hclass, Complex.ofReal_re,
    linearCoefficient_four hclass (tuple_count hh hi hj hk hv hw hp)]
  have hratio : 1 ≤ Real.log (∏ a, p a : ℕ)/L := by
    apply (le_div_iff₀ hL0).mpr
    linarith [ht.1]
  have hgap : 2*Real.log (∏ a, p a : ℕ)-3*L ≤ -(M : ℝ)/20 := by linarith [ht.2]
  have hn := Nat.cast_nonneg (α := ℝ) M
  have hm := mul_le_mul_of_nonpos_right hratio
    (show 2*Real.log (∏ a, p a : ℕ)-3*L ≤ 0 by linarith)
  linarith

/-- A two-unit slab of actual balanced triples, with disjoint upper endpoints. -/
def slabTriples (S : Finset ℕ) (M : ℕ) (η : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 3 ∧
    2*(M : ℝ) ≤ Real.log n ∧ Real.log n < 2*(M : ℝ)+2 ∧
      ∀ p ∈ n.primeFactors, |Real.log p-(2/3 : ℝ)*M| ≤ η*M)

private def coverGrid (N : ℕ) (η : ℝ) : Finset ℕ := Finset.range (⌊2*η*N⌋₊+1)

private def coverStart (N : ℕ) (η : ℝ) (i j : ℕ) (a : Fin 3) : ℝ :=
  if a = 0 then (2/3-η)*N+i-1
  else if a = 1 then (2/3-η)*N+j-1
  else (2/3+2*η)*N-i-j-3

private def coverWidth (a : Fin 3) : ℝ := if a = 2 then 7 else 2

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
private theorem slabTriples_subset_cover (S : Finset ℕ) (N : ℕ) (η : ℝ) :
    slabTriples S N η ⊆ ((coverGrid N η).product (coverGrid N η)).biUnion
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
      (6*Real.log 4)^3*Real.exp 6*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3 := by
  have hc : ((coverProducts N η i j).card : ℝ) ≤
      ((coverTuples N η i j).card : ℝ) := by exact_mod_cast Finset.card_image_le
  have hp := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3)))
    (fun a _ => Nat.cast_nonneg (α := ℝ) ((logPrimes (coverStart N η i j a) (coverWidth a)).card))
    (fun a _ => interval_card_upper_uniform (show 1 ≤ N by omega)
      (coverStart_bounds hη hηu hN hi hj a).1 (by unfold coverWidth; split_ifs <;> norm_num))
  have he : (∏ a : Fin 3, Real.exp (coverWidth a)*Real.exp (coverStart N η i j a)) =
      Real.exp 6*Real.exp (2*(N : ℝ)) := by
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
theorem slabTriples_card_upper (S : Finset ℕ) {N : ℕ} {η : ℝ}
    (hη : 0 < η) (hηu : η ≤ 1/1000) (hN : 20 ≤ N) (hηN : 1 ≤ η*N) :
    ((slabTriples S N η).card : ℝ) ≤
      (9*(6*Real.log 4)^3*Real.exp 6)*η^2*Real.exp (2*(N : ℝ))/((N : ℝ)+1) := by
  have hcover := Finset.card_le_card (slabTriples_subset_cover S N η)
  have hcount := Finset.card_biUnion_le (s := (coverGrid N η).product (coverGrid N η))
    (t := fun ij => coverProducts N η ij.1 ij.2)
  have hsum := Finset.sum_le_sum (s := (coverGrid N η).product (coverGrid N η))
    (fun ij hij => coverProducts_card_upper hη.le hηu hN
      (Finset.mem_product.mp hij).1 (Finset.mem_product.mp hij).2)
  have hs : ((slabTriples S N η).card : ℝ) ≤
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
    (show 0 ≤ (6*Real.log 4)^3*Real.exp 6*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3 by positivity)
  exact hm.trans_eq (by field_simp; ring)

/-- A short negative-cosine interval exists in every radial cell.
The height assumption holds well below the existing zero-free height. -/
theorem exists_short_negative_window {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/20 ∧ ∀ b : ℝ, ∃ v : ℝ,
      0 ≤ v ∧ v ≤ 1/2 ∧ ∀ t : ℝ, b+v ≤ t → t ≤ b+v+4*h →
        Real.cos (y*t) ≤ -(1/2 : ℝ) := by
  let z := |y|
  have hz : 0 < z := by dsimp [z]; linarith
  let h := 1/(10*(z+1))
  have hh : 0 < h := by dsimp [h]; positivity
  have hhhi : h ≤ 1/20 := by
    dsimp [h]
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [z]
    linarith
  refine ⟨h,hh,hhhi,?_⟩
  intro b
  let k : ℤ := ⌈(z*b-Real.pi)/(2*Real.pi)⌉
  let v := ((k : ℝ)*(2*Real.pi)+Real.pi)/z-b
  have hklo : z*b-Real.pi ≤ (k : ℝ)*(2*Real.pi) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).mp (Int.le_ceil _)
  have hkhi : (k : ℝ)*(2*Real.pi) < z*b-Real.pi+2*Real.pi := by
    have h := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one ((z*b-Real.pi)/(2*Real.pi)))
      (by positivity : (0 : ℝ) < 2*Real.pi)
    simpa only [add_mul,div_mul_cancel₀ _ (by positivity : 2*Real.pi ≠ 0),one_mul] using h
  have hvEq : z*(b+v) = (k : ℝ)*(2*Real.pi)+Real.pi := by dsimp [v]; field_simp; ring
  have hv : 0 ≤ v := by nlinarith
  have hvhi : v ≤ 1/2 := by
    have hpi := Real.pi_lt_four
    have hzy : (16 : ℝ) ≤ z := hy
    nlinarith
  refine ⟨v,hv,hvhi,?_⟩
  intro t ht htu
  have he : Real.cos (z*(b+v)) = -1 := by rw [hvEq,Real.cos_add_pi,Real.cos_int_mul_two_pi]
  have hhphase : 4*z*h ≤ 1/2 := by
    dsimp [h]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hd : |z*t-z*(b+v)| ≤ 1/2 := by
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  have hc := Real.abs_cos_sub_cos_le (z*t) (z*(b+v))
  rw [he] at hc
  have hc' := (le_abs_self (Real.cos (z*t)- -1)).trans (hc.trans hd)
  have hcos : Real.cos (z*t) ≤ -(1/2 : ℝ) := by linarith
  have hec : Real.cos (z*t) = Real.cos (y*t) := by
    dsimp [z]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_mul,Real.cos_neg]
  rwa [hec] at hcos

/-- The original factorial envelope evaluated at the moving radial centre. -/
def radialEnvelope (N M : ℕ) : ℝ := Real.exp (-3*(M : ℝ))*(2*(M : ℝ))^N/N.factorial

theorem radialEnvelope_nonneg (N M : ℕ) : 0 ≤ radialEnvelope N M := by
  unfold radialEnvelope
  positivity

theorem radialEnvelope_pos (N : ℕ) {M : ℕ} (hM : 0 < M) : 0 < radialEnvelope N M := by
  unfold radialEnvelope
  positivity

/-- The actual moment is not replaced by the radial cell index. -/
theorem amplitude_le_radial {N M n : ℕ} (hM : 0 < M) (hNM : N ≤ 2*M)
    (hlo : 2*(M : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2*(M : ℝ)+2) :
    amplitude N n ≤ Real.exp 2*radialEnvelope N M := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hnm : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
  have hratio : Real.log n/(2*(M : ℝ)) ≤ Real.exp (1/(M : ℝ)) := by
    have he := Real.add_one_le_exp (1/(M : ℝ))
    have hr : Real.log n/(2*(M : ℝ)) ≤ 1+1/(M : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      field_simp
      nlinarith
    linarith
  have hp := pow_le_pow_left₀ (div_nonneg (Real.log_natCast_nonneg _) (by positivity)) hratio N
  rw [div_pow,← Real.exp_nat_mul] at hp
  have he : (N : ℝ)*(1/(M : ℝ)) ≤ 2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hm).mpr
    exact hnm
  have hp' : (Real.log n)^N ≤ Real.exp 2*(2*(M : ℝ))^N := by
    have h := hp.trans (Real.exp_le_exp.mpr he)
    exact (div_le_iff₀ (by positivity)).mp h
  unfold amplitude radialEnvelope
  have hExp : Real.exp (-(3/2 : ℝ)*Real.log n) ≤ Real.exp (-3*(M : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  exact (div_le_div_of_nonneg_right
    (mul_le_mul hExp hp' (pow_nonneg (Real.log_natCast_nonneg _) _) (Real.exp_nonneg _))
    (show 0 ≤ (N.factorial : ℝ) by positivity)).trans_eq (by ring)

/-- An upper cost for every actual balanced triple in a two-unit slab. -/
theorem slab_norm_upper (S A : Finset ℕ) {N M : ℕ} {η L : ℝ}
    (hη : 0 < η) (hηu : η ≤ 1/1000) (hM : 20 ≤ M) (hηM : 1 ≤ η*M)
    (hNM : N ≤ 2*M) (hL0 : 0 < L) (hL : (M : ℝ) ≤ L) (y : ℝ) :
    ‖∑ n ∈ slabTriples S M η, residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (27*(6*Real.log 4)^3*Real.exp 8)*η^2*
        (M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  have hbound (n : ℕ) (hn : n ∈ slabTriples S M η) :
      ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        3*(M : ℝ)*Real.exp 2*radialEnvelope N M := by
    obtain ⟨_,hs,hk,hlo,hhi,_⟩ := Finset.mem_filter.mp hn
    have hm : (20 : ℝ) ≤ M := by exact_mod_cast hM
    have hb := ZetaRieszSperner.norm_coefficient_le_allowance hL0 n
    rw [ZetaRieszSperner.middleLayerAllowance,if_pos ⟨hs,by omega⟩,hk] at hb
    norm_num at hb
    have hratio : Real.log n/L ≤ 3 := (div_le_iff₀ hL0).mpr (by linarith)
    have hcost : ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ 3*(M : ℝ) := by
      apply hb.trans
      have ht := mul_le_mul_of_nonneg_right hratio (show 0 ≤ Real.log n/3 by positivity)
      nlinarith
    have hker : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ = amplitude N n := by
      rw [norm_zetaPrimeLogKernel]
      norm_num [zetaPrimeExpWeight,amplitude]
      ring
    rw [norm_mul,hker]
    exact (mul_le_mul ((ZetaRieszJointCountFloor.norm_residual_le A L N n).trans hcost)
      (amplitude_le_radial (by omega) hNM hlo hhi.le)
      (by unfold amplitude; positivity) (by positivity)).trans_eq (by ring)
  have hc := slabTriples_card_upper S hη hηu hM hηM
  have hs := (norm_sum_le _ _).trans (Finset.sum_le_sum hbound)
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 3*(M : ℝ)*Real.exp 2*radialEnvelope N M by positivity [radialEnvelope_nonneg N M])
  apply hs.trans (hm.trans_eq ?_)
  have he : Real.exp 6*Real.exp 2 = Real.exp (8 : ℝ) := by rw [← Real.exp_add]; norm_num
  calc
    _ = (27*(6*Real.log 4)^3*(Real.exp 6*Real.exp 2))*η^2*
        (M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by ring
    _ = _ := by rw [he]

/-- Every phased supply atom keeps a positive fraction of the same moving
radial envelope as the triple debit, without changing its moment order. -/
theorem supply_atom_lower (A : Finset ℕ) {N M i j k : ℕ} {h v L y : ℝ}
    (hh : 0 < h) (hhhi : h ≤ 1/20)
    (hi : i ∈ grid M h) (hj : j ∈ grid M h) (hk : k ∈ grid M h)
    (hv : 0 ≤ v) (hvhi : v ≤ 1/2) (hw : h+v ≤ (M : ℝ)/1000)
    (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (hLu : L ≤ (143/100 : ℝ)*M)
    (hshare : (1/2 : ℝ) ≤ 1-4*Real.exp (-(N : ℝ)/64))
    {p : Fin 4 → ℕ} (hp : p ∈ tuples M h v i j k)
    (hcos : Real.cos (y*Real.log (∏ a, p a : ℕ)) ≤ -(1/2 : ℝ)) :
    (M : ℝ)/80*Real.exp (-3/2 : ℝ)*radialEnvelope N M ≤
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
    linarith [ht.1,Nat.cast_nonneg (α := ℝ) M]
  have hwgt := balanced_weight_lower A N hs hn1 hbal
  rw [hcnt] at hwgt
  norm_num only [Nat.cast_ofNat] at hwgt
  have hamp := ZetaRieszCosineCarrier.factorial_envelope_nonneg N (∏ a, p a)
  change 0 ≤ amplitude N (∏ a, p a) at hamp
  have hhalf : amplitude N (∏ a, p a)/2 ≤ weight A N (∏ a, p a) := by nlinarith
  have hc := tuple_coefficient_le_wide hh hi hj hk hv hw hL0 hL hLu hp
  have hprod : (M : ℝ)/40 ≤ (SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re*
      Real.cos (y*Real.log (∏ a, p a : ℕ)) := by
    have hneg := mul_nonneg (show 0 ≤ -Real.cos (y*Real.log (∏ a, p a : ℕ))-1/2 by linarith)
      (show 0 ≤ -(SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re by
        linarith [Nat.cast_nonneg (α := ℝ) M])
    nlinarith
  rw [re_residual_atom]
  have hmain := mul_le_mul hhalf hprod (by positivity : 0 ≤ (M : ℝ)/40) (weight_nonneg A N _)
  have ha : Real.exp (-3/2 : ℝ)*radialEnvelope N M ≤ amplitude N (∏ a, p a) := by
    unfold amplitude radialEnvelope
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
    _ = (M : ℝ)/80*(Real.exp (-3/2 : ℝ)*radialEnvelope N M) := by ring
    _ ≤ (M : ℝ)/80*amplitude N (∏ a, p a) := mul_le_mul_of_nonneg_left ha (by positivity)
    _ = amplitude N (∏ a, p a)/2*((M : ℝ)/40) := by ring
    _ ≤ _ := hmain

/-- Uniform actual positive supply on every radial slab at the original
moment order. The prime count, allocation and phase are all retained. -/
theorem eventually_supply_lower {h : ℝ} (hh : 0 < h) (hhhi : h ≤ 1/20) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (A : Finset ℕ) (v L y : ℝ),
      N ≤ 2*M → 0 ≤ v → v ≤ 1/2 → 0 < L →
      (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
      (∀ t : ℝ, 2*M+v ≤ t → t ≤ 2*M+v+4*h → Real.cos (y*t) ≤ -(1/2 : ℝ)) →
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (∑ n ∈ supply M h v, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨c,hc,hcards⟩ := eventually_supply_card_lower hh (by norm_num : (0 : ℝ) ≤ 1/2)
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hcards
  refine ⟨c/80*Real.exp (-3/2 : ℝ),by positivity,?_⟩
  have ht : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)/64)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 64))
  filter_upwards [eventually_ge_atTop (2*M0),eventually_ge_atTop (2000 : ℕ),
    ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1/8)]
    with N hN0 hN hsmall M A v L y hNM hv hvhi hL0 hL hLu hphase
  have hcM := hM0 M (by omega) v hv hvhi
  have hMR : (1000 : ℝ) ≤ M := by exact_mod_cast (show 1000 ≤ M by omega)
  have hw : h+v ≤ (M : ℝ)/1000 := by linarith
  have ha (n : ℕ) (hn : n ∈ supply M h v) :
      (M : ℝ)/80*Real.exp (-3/2 : ℝ)*radialEnvelope N M ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    obtain ⟨ijk,hijk,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
    obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hb := tuple_log_bounds hp
    exact supply_atom_lower A hh hhhi hi hj hk hv hvhi hw hL0 hL hLu (by linarith) hp
      (hphase _ hb.1.le hb.2)
  have hsum := Finset.sum_le_sum ha
  rw [Finset.sum_const,nsmul_eq_mul,← Complex.re_sum] at hsum
  have hscale := mul_le_mul_of_nonneg_right hcM
    (show 0 ≤ (M : ℝ)/80*Real.exp (-3/2 : ℝ)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  exact (le_of_eq (by ring)).trans (hscale.trans hsum)

/-- One fixed positive share width is paid uniformly over ALL radial
slabs. The original moment order stays N while the cell centre is 2M. -/
theorem eventually_slabs_spending {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (S A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          0 < (∑ n ∈ supply M h v, f n).re ∧
            ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
  obtain ⟨h,hh,hhhi,hphase⟩ := exists_short_negative_window hy
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_lower hh hhhi
  let B : ℝ := 27*(6*Real.log 4)^3*Real.exp 8
  have hB : 0 < B := by dsimp [B]; positivity
  let η := min (1/1000 : ℝ) (Real.sqrt (c/(2*B)))
  have hη : 0 < η := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hηu : η ≤ 1/1000 := min_le_left _ _
  have hηcost : B*η^2 ≤ c/2 := by
    have hs := pow_le_pow_left₀ hη.le (min_le_right (1/1000 : ℝ) (Real.sqrt (c/(2*B)))) 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have ht := (le_div_iff₀ (by positivity : 0 < 2*B)).mp hs
    nlinarith
  refine ⟨η,h,hη,hηu,hh,hhhi,?_⟩
  filter_upwards [hsupply,eventually_ge_atTop (40 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2/η)]
    with N hs hN hsize M S A L hNM hL0 hL hLu
  have hM : 20 ≤ M := by omega
  have hηM : 1 ≤ η*M := by
    have ht := (div_le_iff₀ hη).mp hsize
    have hnr : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
    nlinarith
  obtain ⟨v,hv,hvhi,hcos⟩ := hphase (2*(M : ℝ))
  have hpos := hs M A v L y hNM hv hvhi hL0 hL hLu hcos
  have hneg := slab_norm_upper S A hη hηu hM hηM hNM hL0
    (by nlinarith [Nat.cast_nonneg (α := ℝ) M]) y
  refine ⟨v,hv,hvhi,?_⟩
  dsimp only
  refine ⟨lt_of_lt_of_le (by positivity [radialEnvelope_pos N (show 0 < M by omega)]) hpos,?_⟩
  calc
    _ ≤ B*η^2*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := hneg
    _ ≤ (c/2)*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
      have ht := mul_le_mul_of_nonneg_right hηcost
        (show 0 ≤ (M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
          positivity [radialEnvelope_nonneg N M])
      convert ht using 1 <;> first | rfl | ring
    _ = (1/2 : ℝ)*(c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpos (by norm_num)
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszMaskSupport

/-- Radial cells whose entire positive supply stays in the original core. -/
def radialIndices (N : ℕ) : Finset ℕ :=
  (Finset.range (2*N+1)).filter (fun M =>
    (39/20 : ℝ)*N < 2*M ∧ 2*(M : ℝ)+1 ≤ (203/100 : ℝ)*N)

/-- The paid population is the union of disjoint actual triple slabs. -/
def radialTriples (S : Finset ℕ) (N : ℕ) (η : ℝ) : Finset ℕ :=
  (radialIndices N).biUnion (fun M => slabTriples S M η)

/-- Each radial cell supplies its own distinct four-prime labels. -/
def radialSupply (N : ℕ) (h : ℝ) (v : ℕ → ℝ) : Finset ℕ :=
  (radialIndices N).biUnion (fun M => supply M h (v M))

/-- Distinct triple slabs do not overlap, including their endpoint convention. -/
theorem slabTriples_disjoint (S : Finset ℕ) (η : ℝ) :
    Pairwise (fun M M' : ℕ => Disjoint (slabTriples S M η) (slabTriples S M' η)) := by
  intro M M' hne
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hb := (Finset.mem_filter.mp hn).2
  have hb' := (Finset.mem_filter.mp hn').2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hr : (M : ℝ)+1 ≤ M' := by exact_mod_cast hlt
    linarith [hb.2.2.2.1,hb'.2.2.1]
  · have hr : (M' : ℝ)+1 ≤ M := by exact_mod_cast hlt
    linarith [hb'.2.2.2.1,hb.2.2.1]

/-- The whole supply stays in a unit radial interval. -/
theorem supply_radial_bounds {M n : ℕ} {h v : ℝ} (hh : h ≤ 1/20)
    (hv : 0 ≤ v) (hvhi : v ≤ 1/2) (hn : n ∈ supply M h v) :
    2*(M : ℝ) < Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+1 := by
  obtain ⟨ijk,_,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hb := tuple_log_bounds hp
  constructor <;> linarith [hb.1,hb.2]

/-- Radial separation prevents spending any four-prime label twice. -/
theorem supply_disjoint {N : ℕ} {h : ℝ} {v : ℕ → ℝ} (hh : h ≤ 1/20)
    (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2) :
    (radialIndices N : Set ℕ).PairwiseDisjoint (fun M => supply M h (v M)) := by
  intro M hM M' hM' hne
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hb := supply_radial_bounds hh (hv M hM).1 (hv M hM).2 hn
  have hb' := supply_radial_bounds hh (hv M' hM').1 (hv M' hM').2 hn'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hr : (M : ℝ)+1 ≤ M' := by exact_mod_cast hlt
    linarith [hb.2,hb'.1]
  · have hr : (M' : ℝ)+1 ≤ M := by exact_mod_cast hlt
    linarith [hb'.2,hb.1]

/-- Actual moving lengths lie in every required radial chamber. -/
theorem eventually_length_on_slabs {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ M ∈ radialIndices N,
      N ≤ 2*M ∧ (271/200 : ℝ)*M ≤ SquarefreeVaughanLogSource.length u N ∧
        SquarefreeVaughanLogSource.length u N ≤ (143/100 : ℝ)*M := by
  have hu0 : 0 < u := by linarith
  have hUr : ZetaRieszWideOwnerAudit.radiusCeiling < Real.exp (-(69/100 : ℝ)) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mp
    have h := Real.log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] : (0 : ℝ) < 2*ZetaRieszWideOwnerAudit.radiusCeiling)
    rw [Real.log_mul (by norm_num) (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])] at h
    dsimp [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    linarith [Real.log_two_gt_d9]
  have hlo := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
    (by norm_num : (0 : ℝ) ≤ 69/100) (hU.trans_lt hUr)
  filter_upwards [hlo,eventually_ge_atTop (2 : ℕ)] with N hlo hN M hM
  obtain ⟨_,hmlo,hmhi⟩ := Finset.mem_filter.mp hM
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hnm : (N : ℝ) ≤ 2*M := by linarith
  have hhi := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
  have hh : SquarefreeVaughanLogSource.length u N ≤ (139/100 : ℝ)*N := by
    nlinarith [Real.log_two_lt_d9]
  refine ⟨by exact_mod_cast hnm,?_,?_⟩ <;> linarith

/-- Every radial supply uses the original physical/count/nondominant masks. -/
theorem eventually_radial_supply_in_core {u h : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hh : 0 < h) (hhhi : h ≤ 1/20) :
    ∀ᶠ j : ℕ in atTop, ∀ M ∈ radialIndices (dyadicMomentOrder j),
      ∀ v : ℝ, 0 ≤ v → v ≤ 1/2 → supply M h v ⊆
        coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hlen := ZetaRieszMaskSupport.eventually_length_lower (by linarith : 0 < u) hsource.le
  filter_upwards [eventually_ge_atTop (32 : ℕ),tendsto_dyadicMomentOrder.eventually hlen,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ))]
    with j hj hL hN M hM v hv hvhi n hn
  let N := dyadicMomentOrder j
  obtain ⟨_,hml,hmu⟩ := Finset.mem_filter.mp hM
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : h+v ≤ (M : ℝ)/1000 := by dsimp [N] at hNR ⊢; linarith
  obtain ⟨ijk,hijk,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj',hk'⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hs := tuple_squarefree hh hi hj' hk' hv hw hp
  have hk := tuple_count hh hi hj' hk' hv hw hp
  have hb := tuple_log_bounds hp
  have hwin : (39/20 : ℝ)*N < Real.log (∏ a, p a : ℕ) ∧
      Real.log (∏ a, p a : ℕ) ≤ (203/100 : ℝ)*N := by
    dsimp [N]
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
      linarith [hb.1,Nat.cast_nonneg (α := ℝ) M])
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hcore,by constructor <;> linarith [hwin.1,hwin.2]⟩,hwin⟩

/-- The positive supplies pay the UNION of all selected radial slabs.
Disjointness of the supplies, not an aggregate density model, pays the sum. -/
theorem union_spending {N : ℕ} {S : Finset ℕ} {f : ℕ → ℂ} {η h : ℝ} {v : ℕ → ℝ}
    (hh : h ≤ 1/20) (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2)
    (hpay : ∀ M ∈ radialIndices N,
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h (v M), f n).re) :
    ‖∑ n ∈ radialTriples S N η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ radialSupply N h v, f n).re := by
  have ht : (radialIndices N : Set ℕ).PairwiseDisjoint (fun M => slabTriples S M η) :=
    fun _ _ _ _ hne => slabTriples_disjoint S η hne
  rw [radialTriples,Finset.sum_biUnion ht,radialSupply,Finset.sum_biUnion (supply_disjoint hh hv)]
  calc
    _ ≤ ∑ M ∈ radialIndices N, ‖∑ n ∈ slabTriples S M η, f n‖ := norm_sum_le _ _
    _ ≤ ∑ M ∈ radialIndices N, (1/2 : ℝ)*(∑ n ∈ supply M h (v M), f n).re :=
      Finset.sum_le_sum hpay
    _ = _ := by rw [← Finset.mul_sum,Complex.re_sum]

/-- The central cell is one of the radial cells eventually. -/
theorem self_mem_radialIndices {N : ℕ} (hN : 40 ≤ N) : N ∈ radialIndices N := by
  have hn : (40 : ℝ) ≤ N := by exact_mod_cast hN
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by constructor <;> linarith⟩

/-- The selected triple and four-prime unions are disjoint as actual labels. -/
theorem unions_disjoint {N : ℕ} (S : Finset ℕ) (η : ℝ) {h : ℝ} {v : ℕ → ℝ}
    (hN : 2000 ≤ N) (hh : 0 < h) (hhhi : h ≤ 1/20)
    (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2) :
    Disjoint (radialTriples S N η) (radialSupply N h v) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
  have hthree := (Finset.mem_filter.mp hn).2.2.1
  obtain ⟨M',hM',hn'⟩ := Finset.mem_biUnion.mp hn'
  have hbounds := (Finset.mem_filter.mp hM').2
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : h+v M' ≤ (M' : ℝ)/1000 := by linarith [(hv M' hM').2]
  obtain ⟨ijk,hijk,hn'⟩ := Finset.mem_biUnion.mp hn'
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn'
  have hfour := tuple_count hh hi hj hk (hv M' hM').1 hw hp
  rw [hpn] at hfour
  omega

/-- A whole radial union is paid with the actual moment order, leaving
at least half the four-prime credit in the same exact signed core ledger. -/
theorem eventually_core_radial_spending {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let X := ∑ n ∈ radialTriples S N η, f n
        let Y := ∑ n ∈ radialSupply N h v, f n
        let W := ∑ n ∈ S\(radialTriples S N η ∪ radialSupply N h v), f n
        let θ := max (-X.re) 0/Y.re
        0 < Y.re ∧ ‖X‖ ≤ (1/2 : ℝ)*Y.re ∧ 0 ≤ θ ∧ θ ≤ 1/2 ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re =
            u^(N+1)*(W.re+max X.re 0+(1-θ)*Y.re) := by
  obtain ⟨η,h,hη,hηu,hh,hhhi,hpay⟩ := eventually_slabs_spending hy
  refine ⟨η,h,hη,hηu,hh,hhhi,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    eventually_radial_supply_in_core hu hU hh hhhi,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ))]
    with j hpay hL hsub hN
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvhi,hY,hpaid⟩ := hpay M S A L (hL M hM).1
        (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
      exact ⟨v,fun _ => ⟨hv,hvhi,hY,hpaid⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvbounds : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  have hY : 0 < (∑ n ∈ radialSupply N h v, f n).re := by
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhhi hvbounds),Complex.re_sum]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hpaid := union_spending hhhi hvbounds (fun M hM => (hv M hM).2.2.2)
  refine ⟨v,hvbounds,?_⟩
  let X := ∑ n ∈ radialTriples S N η, f n
  let Y := ∑ n ∈ radialSupply N h v, f n
  let W := ∑ n ∈ S\(radialTriples S N η ∪ radialSupply N h v), f n
  let θ := max (-X.re) 0/Y.re
  change 0 < Y.re ∧ ‖X‖ ≤ (1/2 : ℝ)*Y.re ∧ 0 ≤ θ ∧ θ ≤ 1/2 ∧
    ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re =
      u^(N+1)*(W.re+max X.re 0+(1-θ)*Y.re)
  obtain ⟨hθ,hθhalf,_hθone,hledger⟩ :=
    ZetaRieszQuadrupleCompensation.signed_spending (X := X) (Y := Y) (W := W)
      hY (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) hpaid
  refine ⟨hY,hpaid,hθ,hθhalf,?_⟩
  have hd := unions_disjoint S η hN hh hhhi hvbounds
  have hs : radialTriples S N η ∪ radialSupply N h v ⊆ S := by
    apply Finset.union_subset
    · intro n hn
      obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
      exact (Finset.mem_filter.mp hn).1
    · intro n hn
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hsub M hM (v M) (hvbounds M hM).1 (hvbounds M hM).2 hn
  have he := Finset.sum_sdiff (f := f) hs
  rw [Finset.sum_union hd] at he
  have he' : coreResponse u y N (dyadicPrimeCount j) = W+(X+Y) := he.symm
  rw [he']
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using congrArg (fun t : ℝ => u^(N+1)*t) hledger
/-- A fixed balanced share band of the ORIGINAL support at every radius.
It is not restricted to a unit total-log interval. -/
def balancedTriples (S : Finset ℕ) (N : ℕ) (η : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 3 ∧
    ∀ p ∈ n.primeFactors, |Real.log p-Real.log n/3| ≤ η*N/4)

/-- The fully radial balanced band is eventually nonempty in the
actual core, for every fixed positive width. -/
theorem eventually_core_balanced_nonempty {u η : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hη : 0 < η) :
    ∀ᶠ j : ℕ in atTop,
      (balancedTriples (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
        (dyadicMomentOrder j) η).Nonempty := by
  have hn := ZetaRieszBandCompensation.eventually_core_tripleBand_nonempty hu hU
    (show 0 < η/8 by positivity)
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [hn,hord.eventually_ge_atTop (4/η)] with j hj hsize
  obtain ⟨n,hn⟩ := hj
  obtain ⟨hnS,hs,hc,hlo,hhi,hbal⟩ := Finset.mem_filter.mp hn
  refine ⟨n,Finset.mem_filter.mpr ⟨hnS,hs,hc,?_⟩⟩
  intro p hp
  have he : Real.log p-Real.log n/3 =
      (Real.log p-(2/3 : ℝ)*dyadicMomentOrder j)+
        ((2/3 : ℝ)*dyadicMomentOrder j-Real.log n/3) := by ring
  rw [he]
  have ht : |(2/3 : ℝ)*dyadicMomentOrder j-Real.log n/3| ≤ 1/3 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hηN := (div_le_iff₀ hη).mp hsize
  exact (abs_add_le _ _).trans ((add_le_add (hbal p hp) ht).trans (by nlinarith))

/-- Every balanced triple in the central radial interval is already
in the paid union, with the exact finite masks unchanged. -/
theorem balanced_mem_radialTriples {S : Finset ℕ} {N n : ℕ} {η : ℝ}
    (hN : 4000 ≤ N) (hη : 0 < η) (hηN : 4 ≤ η*N)
    (hn : n ∈ balancedTriples S N η)
    (hlo : (244/125 : ℝ)*N < Real.log n)
    (hhi : Real.log n ≤ (2029/1000 : ℝ)*N) : n ∈ radialTriples S N η := by
  obtain ⟨hnS,hs,hc,hbal⟩ := Finset.mem_filter.mp hn
  let M := ⌊Real.log n/2⌋₊
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (M : ℝ) ≤ Real.log n/2 := Nat.floor_le (by positivity [Real.log_natCast_nonneg n])
  have hceil : Real.log n/2 < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hMR : (M : ℝ) ≤ 2*N := by linarith
  have hM : M ∈ radialIndices N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,?_⟩
    · have h : M ≤ 2*N := by exact_mod_cast hMR
      omega
    constructor <;> linarith
  apply Finset.mem_biUnion.mpr
  refine ⟨M,hM,Finset.mem_filter.mpr ⟨hnS,hs,hc,by linarith,by linarith,?_⟩⟩
  intro p hp
  have he : Real.log p-(2/3 : ℝ)*M =
      (Real.log p-Real.log n/3)+(Real.log n-2*M)/3 := by ring
  rw [he]
  have ht : |(Real.log n-2*M)/3| ≤ 2/3 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hshare : η*(39/40 : ℝ)*N ≤ η*M := by
    have hMlo := (Finset.mem_filter.mp hM).2.1
    nlinarith [mul_nonneg hη.le (show 0 ≤ (M : ℝ)-(39/40 : ℝ)*N by linarith)]
  exact (abs_add_le _ _).trans ((add_le_add (hbal p hp) ht).trans (by nlinarith))

open LogarithmicDeviation ZetaArithmeticDeviationBounds

/-- The uncovered radial edges have a strict source-scale saving. -/
theorem radial_edge_costs :
    Real.log (2*ZetaRieszWideOwnerAudit.radiusCeiling) < deviationCost (244/125) ∧
      Real.log (2*ZetaRieszWideOwnerAudit.radiusCeiling) < deviationCost (2029/1000) := by
  have hlo : Real.log (ZetaRieszWideOwnerAudit.radiusCeiling*(244/125)) < -(3/125 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mpr
    have hbase : (497/500 : ℝ) < Real.exp (-(3/500 : ℝ)) := by
      have h := Real.add_one_lt_exp (by norm_num : -(3/500 : ℝ) ≠ 0)
      linarith
    have hp := pow_lt_pow_left₀ hbase (by norm_num : (0 : ℝ) ≤ 497/500)
      (by norm_num : (4 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
    linarith
  have hhi : Real.log (ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000)) < (29/2000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 29/2000) 4
    norm_num [Finset.sum_range_succ] at h
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
    linarith
  have he0 := log_rate_eq_deviation
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] : 0 < ZetaRieszWideOwnerAudit.radiusCeiling)
    (by norm_num : (0 : ℝ) < 244/125)
  have he1 := log_rate_eq_deviation
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] : 0 < ZetaRieszWideOwnerAudit.radiusCeiling)
    (by norm_num : (0 : ℝ) < 2029/1000)
  constructor <;> linarith

/-- All balanced triples missed by the paid radial union have an
independent geometric allowance. This is uniform in height, selection,
allocation set and the original allowed source radii. -/
theorem exists_missed_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N : ℕ) (S A : Finset ℕ) (η y u : ℝ),
        4000 ≤ N → 0 < η → 4 ≤ η*N → 0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        ‖(u : ℂ)^(N+1)*∑ n ∈ balancedTriples S N η\radialTriples S N η,
          residualCoefficient A (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ r^N*C := by
  obtain ⟨r,C,hr,hr1,hC,h⟩ := exists_uniform_deviation_bound (1 : Polynomial ℂ)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num : (0 : ℝ) < 244/125) (by norm_num) (by norm_num : (2 : ℝ) < 2029/1000)
    radial_edge_costs.1 radial_edge_costs.2
  refine ⟨r,C,hr,hr1,hC,?_⟩
  intro N S A η y u hN hη hηN hu hU
  let D := balancedTriples S N η\radialTriples S N η
  have he : deviationBand D (244/125) (2029/1000) N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnD,hlo,hhi⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnB,hnX⟩ := Finset.mem_sdiff.mp hnD
    exact hnX (balanced_mem_radialTriples hN hη hηN hnB hlo hhi)
  have hb := h N D (residualCoefficient A (SquarefreeVaughanLogSource.length u N) N)
    (fun n _ => norm_residualCoefficient_le A (SquarefreeVaughanLogSource.length_pos u N) N n)
    y u hu hU
  simpa only [he,Finset.sum_empty,sub_zero,zetaPrimeLogKernel,
    SquarefreeEulerQuadratic.primeFilterKernel_one] using hb

/-- The independently paid missed-edge allowance tends to zero on
any growing order schedule, including the original dyadic orders. -/
theorem tendsto_edge_allowance {r C : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun j => r^dyadicMomentOrder j*C) atTop (𝓝 0) := by
  simpa only [Function.comp_def,zero_mul] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp tendsto_dyadicMomentOrder
private theorem balanced_supply_disjoint {N : ℕ} (S : Finset ℕ) (η : ℝ) {h : ℝ} {v : ℕ → ℝ}
    (hN : 2000 ≤ N) (hh : 0 < h) (hhhi : h ≤ 1/20)
    (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2) :
    Disjoint (balancedTriples S N η) (radialSupply N h v) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hthree := (Finset.mem_filter.mp hn).2.2.1
  obtain ⟨M,hM,hn'⟩ := Finset.mem_biUnion.mp hn'
  have hbounds := (Finset.mem_filter.mp hM).2
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : h+v M ≤ (M : ℝ)/1000 := by linarith [(hv M hM).2]
  obtain ⟨ijk,hijk,hn'⟩ := Finset.mem_biUnion.mp hn'
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn'
  have hfour := tuple_count hh hi hj hk (hv M hM).1 hw hp
  rw [hpn] at hfour
  omega

/-- A fixed positive balanced share band is paid over the ENTIRE
original radial core. Missed edge labels cost only an independent
geometric error. The complementary signed sum and half the supply stay
in one lower bound; no separate decay or whole-core floor is assumed. -/
theorem eventually_core_balanced_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let X := ∑ n ∈ radialTriples S N η, f n
        let Y := ∑ n ∈ radialSupply N h v, f n
        let W := ∑ n ∈ S\(radialTriples S N η ∪ radialSupply N h v ∪ balancedTriples S N η), f n
        0 < Y.re ∧
          u^(N+1)*(W.re+max X.re 0+Y.re/2)-r^N*C ≤
            ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,hη,hηu,hh,hhhi,hspend⟩ := eventually_core_radial_spending hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_missed_bound
  refine ⟨η,h,r,C,hη,hηu,hh,hhhi,hr,hr1,hC,?_⟩
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [hspend,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    hord.eventually_ge_atTop (4/η)] with j hj hN hsize
  obtain ⟨v,hvb,hY,_hpaid,_hθ,hθhalf,hledger⟩ := hj
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let X := ∑ n ∈ radialTriples S N η, f n
  let Y := ∑ n ∈ radialSupply N h v, f n
  let W0 := ∑ n ∈ S\(radialTriples S N η ∪ radialSupply N h v), f n
  let W := ∑ n ∈ S\(radialTriples S N η ∪ radialSupply N h v ∪ balancedTriples S N η), f n
  let D := balancedTriples S N η\radialTriples S N η
  let θ := max (-X.re) 0/Y.re
  change θ ≤ 1/2 at hθhalf
  change 0 < Y.re at hY
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re =
    u^(N+1)*(W0.re+max X.re 0+(1-θ)*Y.re) at hledger
  have hηN : 4 ≤ η*N := by
    have ht := (div_le_iff₀ hη).mp hsize
    dsimp [N]
    nlinarith
  have hnorm := hmissed N S A η y u hN hη hηN (by linarith) hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ r^N*C at hnorm
  have hreal : -(r^N*C) ≤ u^(N+1)*(∑ n ∈ D, f n).re := by
    have ht := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
    simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using ht
  have hBY := balanced_supply_disjoint S η (by omega : 2000 ≤ N) hh hhhi hvb
  have hDsub : D ⊆ S\(radialTriples S N η ∪ radialSupply N h v) := by
    intro n hn
    obtain ⟨hnB,hnX⟩ := Finset.mem_sdiff.mp hn
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_filter.mp hnB).1,?_⟩
    intro hh
    rcases Finset.mem_union.mp hh with hx | hy
    · exact hnX hx
    · exact Finset.disjoint_left.mp hBY hnB hy
  have hset : (S\(radialTriples S N η ∪ radialSupply N h v))\D =
      S\(radialTriples S N η ∪ radialSupply N h v ∪ balancedTriples S N η) := by
    ext n
    simp only [D,Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨⟨hn,hab⟩,hd⟩
      refine ⟨hn,?_⟩
      rintro (hab' | hc)
      · exact hab hab'
      · exact hd ⟨hc,fun ha => hab (Or.inl ha)⟩
    · rintro ⟨hn,hall⟩
      exact ⟨⟨hn,fun hab => hall (Or.inl hab)⟩,fun hc => hall (Or.inr hc.1)⟩
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [hset] at hsum
  change W+(∑ n ∈ D, f n) = W0 at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  have hupos : 0 ≤ u^(N+1) := pow_nonneg (by linarith) _
  have hYhalf : u^(N+1)*(Y.re/2) ≤ u^(N+1)*((1-θ)*Y.re) := by
    apply mul_le_mul_of_nonneg_left _ hupos
    nlinarith
  refine ⟨v,hvb,hY,?_⟩
  change u^(N+1)*(W.re+max X.re 0+Y.re/2)-r^N*C ≤ _
  rw [hledger]
  nlinarith

end
end RiemannGaussian.ZetaRieszRadialCompensation
