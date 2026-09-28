/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoupledWindow
import RiemannGaussian.ZetaRieszMacroPrimeWindows

/-!
# Quantitative signed five-prime cells in the literal core

Macroscopic ordered cofactor-prime cells are combined with a fixed total-log
phase interval. Its last-prime window moves with the exact cofactor. The
three Riesz hinge caps provide a fully explicit credit with factor 997/1000
after all five prime-population bounds and old allocation. The exact core
embedding keeps every unselected label signed. A whole four/five angular
comparison and the final joint floor are not asserted.
-/

namespace RiemannGaussian.ZetaRieszFivePrimeCells
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszCoupledWindow ZetaRieszMacroPrimeWindows

/-- The common three-hinge credit on a rectangular outer-prime cell.
Coordinates are in increasing prime order: r, b, a, q. The last prime
is fixed by the total-log interval, not assigned an independent phase. -/
def boxCap (L t h : ℝ) (lo hi : Fin 4 → ℝ) : ℝ :=
  min (lo 0) (max 0 (min (L-t-h+lo 2+lo 1+lo 0) (t-L-hi 2)))+
  min (lo 0) (max 0 (min (L-t-h+lo 3+lo 1+lo 0) (t-L-hi 3)))+
  min (lo 0) (max 0 (min (L-hi 3-hi 2) (lo 3+lo 2+lo 1+lo 0-L)))

/-- The cell credit is nonnegative when its least-log endpoint is. -/
theorem boxCap_nonneg (L t h : ℝ) {lo hi : Fin 4 → ℝ} (hlo : 0 ≤ lo 0) :
    0 ≤ boxCap L t h lo hi := by
  unfold boxCap
  exact add_nonneg (add_nonneg (le_min hlo (le_max_left _ _))
    (le_min hlo (le_max_left _ _))) (le_min hlo (le_max_left _ _))

private theorem product_four (p : Fin 4 → ℕ) :
    ∏ i, p i = p 3*(p 2*(p 1*p 0)) := by
  simp only [Fin.prod_univ_four]
  ring

private theorem log_product_four {p : Fin 4 → ℕ} (hp : ∀ i, (p i).Prime) :
    Real.log (∏ i, p i : ℕ) = Real.log (p 3)+Real.log (p 2)+Real.log (p 1)+Real.log (p 0) := by
  rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hp i).ne_zero)]
  simp only [Fin.sum_univ_four]
  ring

/-- A whole cell pays one explicit common cap before summing actual
primes. Correlation through the exact cofactor logarithm is retained. -/
theorem boxCap_le_windowCap {L t h : ℝ} {lo hi : Fin 4 → ℝ} {p : Fin 4 → ℕ}
    (hp : ∀ i, (p i).Prime)
    (hl : ∀ i, lo i ≤ Real.log (p i)) (hu : ∀ i, Real.log (p i) ≤ hi i) :
    boxCap L t h lo hi ≤
      fiveWindowCap L (t-Real.log (∏ i, p i : ℕ)) h (p 3) (p 2) (p 1) (p 0) := by
  have he := log_product_four hp
  unfold boxCap fiveWindowCap
  apply add_le_add
  · apply add_le_add
    · apply min_le_min (hl 0)
      apply max_le_max le_rfl
      apply min_le_min <;> linarith [hl 0,hl 1,hl 2,hu 2]
    · apply min_le_min (hl 0)
      apply max_le_max le_rfl
      apply min_le_min <;> linarith [hl 0,hl 1,hl 3,hu 3]
  · apply min_le_min (hl 0)
    apply max_le_max le_rfl
    apply min_le_min <;> linarith [hl 0,hl 1,hl 2,hl 3,hu 2,hu 3]

/-- Cofactor boxes retain exact multiplicative harmonic weight. Ordering
makes the product image injective, without a factorial incidence credit. -/
theorem cofactor_reciprocal_eq {lo H : Fin 4 → ℝ}
    (horder : ∀ i j, i < j → lo i+H i ≤ lo j) :
    (∑ m ∈ (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
        (fun p => (∏ i, p i : ℕ)), (m : ℝ)⁻¹) =
      ∑ p ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i)), ∏ i, (p i : ℝ)⁻¹ := by
  rw [Finset.sum_image (ordered_macro_product_injective horder)]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.cast_prod,Finset.prod_inv_distrib]

private theorem tuple_bounds {lo H : Fin 4 → ℝ} {p : Fin 4 → ℕ}
    (hp : p ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i))) :
    (∀ i, (p i).Prime) ∧ (∏ i, p i) ≠ 0 ∧
      (∑ i, lo i) ≤ Real.log (∏ i, p i : ℕ) ∧
      Real.log (∏ i, p i : ℕ) ≤ ∑ i, (lo i+H i) := by
  have hpr (i : Fin 4) := (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1
  have he : Real.log (∏ i, p i : ℕ) = ∑ i, Real.log (p i) := by
    rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hpr i).ne_zero)]
  refine ⟨hpr,Finset.prod_ne_zero_iff.mpr (fun i _ => (hpr i).ne_zero),?_,?_⟩
  · rw [he]
    exact Finset.sum_le_sum (fun i _ => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).2.1.le)
  · rw [he]
    exact Finset.sum_le_sum (fun i _ => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).2.2)

private theorem tuple_ordered {lo H : Fin 4 → ℝ}
    (horder : ∀ i j, i < j → lo i+H i ≤ lo j) {p : Fin 4 → ℕ}
    (hp : p ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i))) :
    p 0 < p 1 ∧ p 1 < p 2 ∧ p 2 < p 3 := by
  have hh (i j : Fin 4) (hij : i < j) : p i < p j := by
    have hl := logPrimes_bounds (Fintype.mem_piFinset.mp hp i)
    have hu := logPrimes_bounds (Fintype.mem_piFinset.mp hp j)
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hl.1.pos)
      (by exact_mod_cast hu.1.pos)).mp (hl.2.2.trans_lt ((horder i j hij).trans_lt hu.2.1))
  exact ⟨hh 0 1 (by decide),hh 1 2 (by decide),hh 2 3 (by decide)⟩


/-- An explicit signed lower bound for a whole five-prime cell with
macroscopic outer widths. The total phase remains in one fixed interval,
all prime populations are literal, and every integer is counted once.
The 997/1000 factor pays old allocation and all five population errors. -/
theorem eventually_five_cell_lower {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 4 → ℝ) (A : Finset ℕ) (L t y : ℝ),
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∀ i j, i < j → lo i+H i ≤ lo j) → 0 < L →
      α*N ≤ t-(∑ i, (lo i+H i)) →
      lo 3+H 3 ≤ t-(∑ i, (lo i+H i)) →
      t-(∑ i, lo i)+h ≤ (9/16 : ℝ)*t →
      t-lo 3-lo 2+h ≤ L → L ≤ t-(lo 1+H 1)-(lo 0+H 0) →
      Real.cos (y*t)+|y| * h ≤ 0 →
      let M := (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image (fun p => (∏ i, p i : ℕ))
      (997/1000 : ℝ)*(t/L)*boxCap L t h lo (fun i => lo i+H i)*
        (-Real.cos (y*t)- |y| * h)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
        (h/(t-∑ i, lo i))*(∏ i, H i/(lo i+H i)) ≤
      (∑ n ∈ M.biUnion (fun m => (logPrimes (t-Real.log m) h).image (fun p => m*p)),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_five_cofactor_lower hh hhu hα,
    eventually_macro_tuple_bounds hα hβ (by decide : 4 ≤ 4),
    eventually_ge_atTop (1 : ℕ)] with N hbound hmass hN lo H A L t y hlo hH horder hL
      hmin hqp hmax hsat htriple hphase
  dsimp only
  let T := Fintype.piFinset (fun i => logPrimes (lo i) (H i))
  let M := T.image (fun p => (∏ i, p i : ℕ))
  let C := boxCap L t h lo (fun i => lo i+H i)
  let vmax := t-∑ i, lo i
  let V := Real.exp (-(t+h)/2)*t^N/N.factorial
  let Z := (999/1000 : ℝ)*(9999/10000 : ℝ)*(t/L)*
    (-Real.cos (y*t)- |y| * h)*V*h
  let B := Z*(C/vmax)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo0 (i : Fin 4) : 0 < lo i := by nlinarith [hlo i]
  have hH0 (i : Fin 4) : 0 < H i := by nlinarith [hH i]
  have hsum : (∑ i, lo i) ≤ ∑ i, (lo i+H i) :=
    Finset.sum_le_sum (fun i _ => le_add_of_nonneg_right (hH0 i).le)
  have ht : 0 < t := by
    have hl : 0 ≤ ∑ i, (lo i+H i) :=
      Finset.sum_nonneg (fun i _ => by linarith [hlo0 i,hH0 i])
    nlinarith
  have hvmax : 0 < vmax := by dsimp [vmax]; nlinarith
  have hC : 0 ≤ C := boxCap_nonneg L t h (hlo0 0).le
  have hφ : 0 ≤ -Real.cos (y*t)- |y| * h := by linarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hB : 0 ≤ B := mul_nonneg hZ (div_nonneg hC hvmax.le)
  have hm : ∀ m ∈ M, m ≠ 0 := by
    intro m hm'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm'
    exact (tuple_bounds hp).2.1
  have hdata (p : Fin 4 → ℕ) (hp : p ∈ T) :
      α*N ≤ t-Real.log (∏ i, p i : ℕ) ∧
      Real.log (p 3) ≤ t-Real.log (∏ i, p i : ℕ) ∧
      t-Real.log (∏ i, p i : ℕ)+h ≤ (9/16 : ℝ)*t ∧
      t-Real.log (∏ i, p i : ℕ)+h+Real.log (p 1*p 0 : ℕ) ≤ L ∧
      L ≤ t-Real.log (∏ i, p i : ℕ)+Real.log (p 3)+Real.log (p 2) := by
    have hb := tuple_bounds hp
    have hl (i : Fin 4) := logPrimes_bounds (Fintype.mem_piFinset.mp hp i)
    have he := log_product_four hb.1
    have hbr : Real.log (p 1*p 0 : ℕ) = Real.log (p 1)+Real.log (p 0) := by
      rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hb.1 1).ne_zero)
        (by exact_mod_cast (hb.1 0).ne_zero)]
    refine ⟨by linarith [hb.2.2.2],by linarith [(hl 3).2.2,hb.2.2.2],
      by linarith [hb.2.2.1],?_,?_⟩
    · rw [hbr]
      linarith [(hl 2).2.1,(hl 3).2.1]
    · linarith [(hl 0).2.2,(hl 1).2.2]
  have hpoint (m : ℕ) (hm' : m ∈ M) :
      B*(m : ℝ)⁻¹ ≤ (∑ p ∈ logPrimes (t-Real.log m) h, f (m*p)).re := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm'
    have hb := tuple_bounds hp
    have ho := tuple_ordered horder hp
    obtain ⟨hv,hqv,hvu,hpb,hpqa⟩ := hdata p hp
    have he := product_four p
    have hlow := hbound A (p 3) (p 2) (p 1) (p 0) t L y
      (hb.1 3) (hb.1 2) (hb.1 1) (hb.1 0) ho.2.2 ho.2.1 ho.1 hL
      (by simpa only [← he] using hv) (by simpa only [← he] using hqv)
      (by simpa only [← he] using hvu) (by simpa only [← he] using hpb)
      (by simpa only [← he] using hpqa) hphase
    rw [← he] at hlow
    have hv0 : 0 < t-Real.log (∏ i, p i : ℕ) := by nlinarith
    have hcap := boxCap_le_windowCap (L := L) (t := t) (h := h) hb.1
      (fun i => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).2.1.le)
      (fun i => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).2.2)
    have hratio : C/vmax ≤
        fiveWindowCap L (t-Real.log (∏ i, p i : ℕ)) h (p 3) (p 2) (p 1) (p 0)/
          (t-Real.log (∏ i, p i : ℕ)) := by
      exact (div_le_div_of_nonneg_left hC hv0
        (by dsimp [vmax]; linarith [hb.2.2.1])).trans
          (div_le_div_of_nonneg_right hcap hv0.le)
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hZ)
      (inv_nonneg.mpr (Nat.cast_nonneg (∏ i, p i)))
    apply hscale.trans
    calc
      _ = (((999/1000 : ℝ)*(t/L)*
          fiveWindowCap L (t-Real.log (∏ i, p i : ℕ)) h (p 3) (p 2) (p 1) (p 0)*
          (-Real.cos (y*t)- |y| * h))*(Real.exp (-(t+h)/2)*t^N/N.factorial)/
          ((∏ i, p i : ℕ) : ℝ))*((9999/10000 : ℝ)*h/(t-Real.log (∏ i, p i : ℕ))) := by
        dsimp [Z,V]
        ring
      _ ≤ _ := hlow
  have hP : ∀ m ∈ M, ∀ p ∈ logPrimes (t-Real.log m) h,
      p.Prime ∧ ∀ r : ℕ, r.Prime → r ∣ m → r < p := by
    intro m hm' p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm'
    have hb := tuple_bounds hv
    have ho := tuple_ordered horder hv
    have hg := hdata v hv
    have he := product_four v
    have hh := five_window_geometry (hb.1 3) (hb.1 2) (hb.1 1) (hb.1 0)
      ho.2.2 ho.2.1 ho.1 (by simpa only [← he] using hg.2.1)
      (by simpa only [← he] using hg.2.2.1) (by simpa only [← he] using hp)
    exact ⟨(logPrimes_bounds hp).1,by simpa only [← he] using hh.2.2.2⟩
  have hpop : (999/1000 : ℝ)*(∏ i, H i/(lo i+H i)) ≤ ∑ m ∈ M, (m : ℝ)⁻¹ := by
    rw [cofactor_reciprocal_eq horder]
    exact (hmass lo H hlo hH).1
  have hmain : B*((999/1000 : ℝ)*(∏ i, H i/(lo i+H i))) ≤
      (∑ n ∈ M.biUnion (fun m => (logPrimes (t-Real.log m) h).image (fun p => m*p)), f n).re := by
    apply (mul_le_mul_of_nonneg_left hpop hB).trans
    rw [Finset.mul_sum,sum_owned_products M (fun m => logPrimes (t-Real.log m) h) f hm hP,
      Complex.re_sum]
    exact Finset.sum_le_sum hpoint
  have hprod : 0 ≤ ∏ i, H i/(lo i+H i) :=
    Finset.prod_nonneg (fun i _ => div_nonneg (hH0 i).le (by linarith [hlo0 i,hH0 i]))
  have hfactor := mul_le_mul_of_nonneg_right
    (by norm_num : (997/1000 : ℝ) ≤ (999/1000)*(9999/10000)*(999/1000))
    (show 0 ≤ (t/L)*C*(-Real.cos (y*t)- |y| * h)*V*(h/vmax)*
      (∏ i, H i/(lo i+H i)) by positivity)
  apply le_trans _ hmain
  convert hfactor using 1 <;> dsimp [B,Z,V,C,vmax] <;> ring


/-- The complete five-prime cell has nonpositive arithmetic coefficients
before observing any phase. The same literal population can therefore
provide a ceiling when its phase is reversed. -/
theorem cell_products_coefficient_nonpos {lo H : Fin 4 → ℝ} {L t h : ℝ}
    (ht : 0 ≤ t) (hL : 0 < L)
    (horder : ∀ i j, i < j → lo i+H i ≤ lo j)
    (hqp : lo 3+H 3 ≤ t-(∑ i, (lo i+H i)))
    (hsat : t-lo 3-lo 2+h ≤ L) (htriple : L ≤ t-(lo 1+H 1)-(lo 0+H 0))
    {n : ℕ} (hn : n ∈ ((Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
      (fun p => (∏ i, p i : ℕ))).biUnion (fun m =>
        (logPrimes (t-Real.log m) h).image (fun p => m*p))) :
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ 0 := by
  obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  have hb := tuple_bounds hv
  have ho := tuple_ordered horder hv
  have he := product_four v
  have hl (i : Fin 4) := logPrimes_bounds (Fintype.mem_piFinset.mp hv i)
  have hp' := logPrimes_bounds hp
  have hqv : Real.log (v 3) ≤ t-Real.log (∏ i, v i : ℕ) := by
    linarith [(hl 3).2.2,hb.2.2.2]
  have hqp' : v 3 < p := by
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (hb.1 3).pos)
      (by exact_mod_cast hp'.1.pos)).mp (hqv.trans_lt hp'.2.1)
  have hs := squarefree_five_of_order hp'.1 (hb.1 3) (hb.1 2) (hb.1 1) (hb.1 0)
    hqp' ho.2.2 ho.2.1 ho.1
  have hlogs := log_product_four hb.1
  have hbr : Real.log (v 1*v 0 : ℕ) = Real.log (v 1)+Real.log (v 0) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hb.1 1).ne_zero)
      (by exact_mod_cast (hb.1 0).ne_zero)]
  have hpbr : t-Real.log (∏ i, v i : ℕ)+h+Real.log (v 1*v 0 : ℕ) ≤ L := by
    rw [hbr]
    linarith [(hl 3).2.1,(hl 2).2.1]
  have hthree : L ≤ t-Real.log (∏ i, v i : ℕ)+Real.log (v 3)+Real.log (v 2) := by
    linarith [(hl 1).2.2,(hl 0).2.2]
  have hid : (∏ i, v i : ℕ)*p = p*(v 3*(v 2*(v 1*v 0))) := by rw [he]; ring
  have hh : 0 < h := by linarith [hp'.2.1,hp'.2.2]
  have hqa : Real.log (v 2) ≤ Real.log (v 3) :=
    Real.log_le_log (by exact_mod_cast (hb.1 2).pos) (by exact_mod_cast ho.2.2.le)
  have hc := five_coefficient_window_lower hp'.1 (hb.1 3) (hb.1 2) (hb.1 1) (hb.1 0)
    (t := t) hs ho.1.le hL (by simpa only [← hid] using (product_log_bounds hb.2.1 hp).2.1.le)
    hp'.2.1.le hp'.2.2 hpbr (by linarith)
    (by linarith only [hqa,hqv,hpbr,hh]) hthree
  rw [← hid] at hc
  have hcap := mul_nonneg (div_nonneg ht hL.le)
    (fiveWindowCap_nonneg L (t-Real.log (∏ i, v i : ℕ)) h (v 3) (v 2) (v 1) (v 0))
  linarith only [hc,hcap]

/-- Every integer of a selected five-prime cell survives the current
core masks. The final-prime window enforces the two radial edges exactly. -/
theorem cell_products_subset_core (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    {lo H : Fin 4 → ℝ} {t h : ℝ}
    (horder : ∀ i j, i < j → lo i+H i ≤ lo j)
    (hqp : lo 3+H 3 ≤ t-(∑ i, (lo i+H i)))
    (hmax : t-(∑ i, lo i)+h ≤ (9/16 : ℝ)*t)
    (htlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ t)
    (hthi : t+h ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) :
    ((Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
      (fun p => (∏ i, p i : ℕ))).biUnion (fun m =>
        (logPrimes (t-Real.log m) h).image (fun p => m*p)) ⊆
      ZetaRieszParityPacket.coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  have hb := tuple_bounds hv
  have ho := tuple_ordered horder hv
  have he := product_four v
  have hqv : Real.log (v 3) ≤ t-Real.log (∏ i, v i : ℕ) := by
    linarith [(logPrimes_bounds (Fintype.mem_piFinset.mp hv 3)).2.2,hb.2.2.2]
  have hvu : t-Real.log (∏ i, v i : ℕ)+h ≤ (9/16 : ℝ)*t := by
    linarith [hb.2.2.1]
  have hg := five_window_geometry (hb.1 3) (hb.1 2) (hb.1 1) (hb.1 0)
    ho.2.2 ho.2.1 ho.1 (by simpa only [← he] using hqv)
    (by simpa only [← he] using hvu) (by simpa only [← he] using hp)
  rw [← he] at hg
  have ht := product_log_bounds hb.2.1 hp
  apply mem_core_of_prime_share_le j hj hu hU hL hg.1 (by rw [hg.2.1]; decide)
    (by
      rw [hg.2.1]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 3 ≤ j+3 by omega)
      dsimp [ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
      norm_num at hh
      omega)
    (htlo.trans_lt ht.2.1) (ht.2.2.trans hthi) hg.2.2.1

/-- The explicit macroscopic-cell credit is an independent lower bound
inside `coreResponse`, with every unselected integer left signed. It
retains the original moving length, allocation and moment order. -/
theorem eventually_five_cell_core_floor {u h α β : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ j : ℕ in atTop, ∀ (lo H : Fin 4 → ℝ) (t y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let M := (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image (fun p => (∏ i, p i : ℕ))
      let D := M.biUnion (fun m => (logPrimes (t-Real.log m) h).image (fun p => m*p))
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∀ i j, i < j → lo i+H i ≤ lo j) →
      α*N ≤ t-(∑ i, (lo i+H i)) →
      lo 3+H 3 ≤ t-(∑ i, (lo i+H i)) → t-(∑ i, lo i)+h ≤ (9/16 : ℝ)*t →
      t-lo 3-lo 2+h ≤ L → L ≤ t-(lo 1+H 1)-(lo 0+H 0) →
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      Real.cos (y*t)+|y| * h ≤ 0 →
      (∑ n ∈ ZetaRieszParityPacket.coreBand u N K\D,
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
      (997/1000 : ℝ)*(t/L)*boxCap L t h lo (fun i => lo i+H i)*
        (-Real.cos (y*t)- |y| * h)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
        (h/(t-∑ i, lo i))*(∏ i, H i/(lo i+H i)) ≤
      (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hroom : u < Real.exp (-(5/8 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 5/8) hroom
  filter_upwards [eventually_ge_atTop 32,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_five_cell_lower hh hhu hα hβ)] with j hj hL hbound lo H t y
  dsimp only
  intro hlo hH horder hmin hqp hmax hsat htriple htlo hthi hphase
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hDS := cell_products_subset_core j hj hu hU (by linarith)
    horder hqp hmax htlo hthi
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hDS)
  rw [Complex.add_re] at he
  change _ ≤ (∑ n ∈ ZetaRieszParityPacket.coreBand u N
    (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j), f n).re
  rw [← he]
  apply add_le_add le_rfl
  exact hbound lo H A L t y hlo hH horder
    (SquarefreeVaughanLogSource.length_pos u N) hmin hqp hmax hsat htriple hphase


/-- Each product in a five-prime cell has exactly five distinct prime
factors. This disjoins its credit from every four-prime debit or supply. -/
theorem cell_products_count {lo H : Fin 4 → ℝ} {t h : ℝ}
    (horder : ∀ i j, i < j → lo i+H i ≤ lo j)
    (hqp : lo 3+H 3 ≤ t-(∑ i, (lo i+H i)))
    (hmax : t-(∑ i, lo i)+h ≤ (9/16 : ℝ)*t)
    {n : ℕ} (hn : n ∈ ((Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
      (fun p => (∏ i, p i : ℕ))).biUnion (fun m =>
        (logPrimes (t-Real.log m) h).image (fun p => m*p))) : n.primeFactors.card = 5 := by
  obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  have hb := tuple_bounds hv
  have ho := tuple_ordered horder hv
  have he := product_four v
  have hqv : Real.log (v 3) ≤ t-Real.log (∏ i, v i : ℕ) := by
    linarith [(logPrimes_bounds (Fintype.mem_piFinset.mp hv 3)).2.2,hb.2.2.2]
  have hvu : t-Real.log (∏ i, v i : ℕ)+h ≤ (9/16 : ℝ)*t := by
    linarith [hb.2.2.1]
  have hg := five_window_geometry (hb.1 3) (hb.1 2) (hb.1 1) (hb.1 0)
    ho.2.2 ho.2.1 ho.1 (by simpa only [← he] using hqv)
    (by simpa only [← he] using hvu) (by simpa only [← he] using hp)
  simpa only [← he] using hg.2.1

/-- Separated ordered cofactor cells supply disjoint sets of actual labels.
The cofactor-dependent final-prime windows cannot duplicate an integer. -/
theorem cell_products_disjoint {a H b G : Fin 4 → ℝ} {t h : ℝ}
    (ha : ∀ i j, i < j → a i+H i ≤ a j)
    (hb : ∀ i j, i < j → b i+G i ≤ b j)
    (hap : a 3+H 3 ≤ t-(∑ i, (a i+H i)))
    (hbp : b 3+G 3 ≤ t-(∑ i, (b i+G i)))
    (ham : t-(∑ i, a i)+h ≤ (9/16 : ℝ)*t)
    (hbm : t-(∑ i, b i)+h ≤ (9/16 : ℝ)*t)
    (hsep : ∃ i, a i+H i ≤ b i ∨ b i+G i ≤ a i) :
    Disjoint
      (((Fintype.piFinset (fun i => logPrimes (a i) (H i))).image
        (fun p => (∏ i, p i : ℕ))).biUnion (fun m =>
          (logPrimes (t-Real.log m) h).image (fun p => m*p)))
      (((Fintype.piFinset (fun i => logPrimes (b i) (G i))).image
        (fun p => (∏ i, p i : ℕ))).biUnion (fun m =>
          (logPrimes (t-Real.log m) h).image (fun p => m*p))) := by
  have hd := disjoint_ordered_macro_products ha hb hsep
  have howner {lo H : Fin 4 → ℝ}
      (hord : ∀ i j, i < j → lo i+H i ≤ lo j)
      (hqp : lo 3+H 3 ≤ t-(∑ i, (lo i+H i)))
      (hmax : t-(∑ i, lo i)+h ≤ (9/16 : ℝ)*t)
      {m p : ℕ} (hm : m ∈ (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
        (fun p => (∏ i, p i : ℕ))) (hp : p ∈ logPrimes (t-Real.log m) h) :
      p.Prime ∧ ∀ r : ℕ, r.Prime → r ∣ m → r < p := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
    have hvb := tuple_bounds hv
    have hvo := tuple_ordered hord hv
    have he := product_four v
    have hqv : Real.log (v 3) ≤ t-Real.log (∏ i, v i : ℕ) := by
      linarith [(logPrimes_bounds (Fintype.mem_piFinset.mp hv 3)).2.2,hvb.2.2.2]
    have hvu : t-Real.log (∏ i, v i : ℕ)+h ≤ (9/16 : ℝ)*t := by
      linarith [hvb.2.2.1]
    have hg := five_window_geometry (hvb.1 3) (hvb.1 2) (hvb.1 1) (hvb.1 0)
      hvo.2.2 hvo.2.1 hvo.1 (by simpa only [← he] using hqv)
      (by simpa only [← he] using hvu) (by simpa only [← he] using hp)
    exact ⟨(logPrimes_bounds hp).1,by simpa only [← he] using hg.2.2.2⟩
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn
  obtain ⟨v,hv,hn'⟩ := Finset.mem_biUnion.mp hn'
  obtain ⟨q,hq,hqn⟩ := Finset.mem_image.mp hn'
  have hpo := howner ha hap ham hm hp
  have hqo := howner hb hbp hbm hv hq
  have he := (largest_prime_product_unique hpo.1 hqo.1 hpo.2 hqo.2 (hpn.trans hqn.symm)).1
  exact Finset.disjoint_left.mp hd hm (by simpa only [he] using hv)

end
end RiemannGaussian.ZetaRieszFivePrimeCells
