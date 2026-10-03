/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLehmanCoverage
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Square-product centre sharing and its exact coverage boundary

Restricting the weight product to a square shares the literal centres on
a short public index. Every positive square-product pair has the form
(h*u²,h*v²), with centre indexed by h*u*v. This saves construction work
but does not preserve the universal sixth-width Lehman window.

The counterexample is for this arithmetic cover. Modular aliases can
still reveal a factor; no general factoring or complexity impossibility
is asserted.
-/

namespace RiemannGaussian.SemiprimeSquareProductCover

/-- Every positive square-product weight pair has a common multiplier
and two square weights. No primitive-weight restriction is needed. -/
theorem square_product_weights {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hs : IsSquare (a*b)) :
    ∃ h u v : ℕ, 0 < h ∧ 0 < u ∧ 0 < v ∧ a = h*u^2 ∧ b = h*v^2 := by
  let h := a.gcd b
  let x := a/h
  let y := b/h
  have hh : 0 < h := Nat.gcd_pos_of_pos_left b ha
  have hax : h*x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hby : h*y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  obtain ⟨m, hm⟩ := hs
  have hm' : a*b = m^2 := by simpa only [pow_two] using hm
  have hdiv : h^2 ∣ m^2 := by
    refine ⟨x*y, ?_⟩
    rw [← hm', ← hax, ← hby]
    ring
  have hdm : h ∣ m := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hdiv
  obtain ⟨t, ht⟩ := hdm
  have hxy : x*y = t^2 := by
    apply Nat.mul_left_cancel (by positivity : 0 < h^2)
    calc
      h^2*(x*y) = (h*x)*(h*y) := by ring
      _ = a*b := by rw [hax, hby]
      _ = m^2 := hm'
      _ = h^2*t^2 := by rw [ht]; ring
  have hcop : x.Coprime y := Nat.coprime_div_gcd_div_gcd hh
  have hunit : IsUnit (gcd x y) := by
    apply Nat.isUnit_iff.mpr
    exact hcop
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit hxy
  have hunit' : IsUnit (gcd y x) := by
    apply Nat.isUnit_iff.mpr
    exact hcop.symm
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow hunit'
    (by simpa only [mul_comm] using hxy)
  have ha' : a = h*u^2 := by rw [← hu]; exact hax.symm
  have hb' : b = h*v^2 := by rw [← hv]; exact hby.symm
  have huPos : 0 < u := by
    by_contra hn
    have hu0 : u = 0 := by omega
    simp only [hu0, zero_pow (by decide : 2 ≠ 0), mul_zero] at ha'
    omega
  have hvPos : 0 < v := by
    by_contra hn
    have hv0 : v = 0 := by omega
    simp only [hv0, zero_pow (by decide : 2 ≠ 0), mul_zero] at hb'
    omega
  exact ⟨h, u, v, hh, huPos, hvPos, ha', hb'⟩

/-- A square-product pair's public centre has just one short integer
index m=h*u*v, retaining the exact ceiling boundary. -/
theorem square_product_centre (N h u v : ℕ) :
    SemiprimeLehmanCoverage.literalCentre N ((h*u^2)*(h*v^2)) =
      ⌈2*(h*u*v : ℕ)*Real.sqrt (N : ℝ)⌉₊ := by
  rw [SemiprimeLehmanCoverage.literalCentre_eq_natCeil]
  have he : ((h*u^2)*(h*v^2) : ℝ) = ((h*u*v : ℕ) : ℝ)^2 := by push_cast; ring
  push_cast at he ⊢
  rw [he, Real.sqrt_sq (by positivity)]
  congr 1
  ring

/-- The complete public centre cache for square weight products. -/
def squareCentres (N B : ℕ) : List ℕ :=
  (List.range B).map fun j => SemiprimeLehmanCoverage.literalCentre N ((j+1)^2)

/-- Only B centre entries are constructed, irrespective of the number
of square-product weight representations. This is an exact entry count. -/
theorem squareCentres_length (N B : ℕ) : (squareCentres N B).length = B := by
  simp [squareCentres]

/-- Every square-product row in the full weight budget uses an entry in
the short cache. The coverage counterexample below preserves this cache. -/
theorem mem_squareCentres {N B a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a*b ≤ B^2) (hs : IsSquare (a*b)) :
    SemiprimeLehmanCoverage.literalCentre N (a*b) ∈ squareCentres N B := by
  obtain ⟨m, hm⟩ := hs
  have he : a*b = m^2 := by simpa only [pow_two] using hm
  have hpos : 0 < m := by nlinarith [Nat.mul_pos ha hb]
  have hbound : m ≤ B := by nlinarith
  simp only [squareCentres, List.mem_map, List.mem_range]
  exact ⟨m-1, by omega, by simp only [Nat.sub_add_cancel hpos, he]⟩

/-- Exact centres also share within each non-square class d*m². -/
theorem square_class_centre (N d m : ℕ) :
    SemiprimeLehmanCoverage.literalCentre N (d*m^2) =
      ⌈2*(m : ℝ)*Real.sqrt (d*N : ℕ)⌉₊ := by
  rw [SemiprimeLehmanCoverage.literalCentre_eq_natCeil]
  push_cast
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ d), Real.sqrt_sq (by positivity),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ d)]
  congr 1
  ring

/-- Public arithmetic candidates for all classes 1<=d<=D. The padded
offset width encloses the sharp B/(4*m*sqrt(d)) window. The list uses no
factor labels or separate weights. Its coverage is not assumed. -/
def classCandidates (N B D : ℕ) : List (ℕ × ℕ) :=
  (List.range D).flatMap fun j =>
    (List.range ((B^2/(j+1)).sqrt)).flatMap fun l =>
      (List.range (B/(4*(l+1))+1)).map fun i =>
        ((j+1)*(l+1)^2, SemiprimeLehmanCoverage.literalCentre N ((j+1)*(l+1)^2)+i)

/-- Every admissible class and padded offset occurs in the actual list. -/
theorem mem_classCandidates {N B D d m i : ℕ} (hd : 0 < d) (hdD : d ≤ D)
    (hm : 0 < m) (hbudget : d*m^2 ≤ B^2) (hi : i < B/(4*m)+1) :
    (d*m^2, SemiprimeLehmanCoverage.literalCentre N (d*m^2)+i) ∈
      classCandidates N B D := by
  have hM : m ≤ (B^2/d).sqrt := Nat.le_sqrt'.mpr
    ((Nat.le_div_iff_mul_le hd).mpr (by simpa only [mul_comm] using hbudget))
  simp only [classCandidates, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨d-1, by omega, m-1, ?_, i, ?_, ?_⟩
  · simpa only [Nat.sub_add_cancel hd] using (by omega : m-1 < (B^2/d).sqrt)
  · simpa only [Nat.sub_add_cancel hm] using hi
  · simp only [Nat.sub_add_cancel hd, Nat.sub_add_cancel hm]

/-- The exact squared sharp boundary lies inside the padded integer
width used by classCandidates. -/
theorem sharp_class_squared_inside_width {B d m i : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hsharp : (4*m*i)^2*d < B^2) : i < B/(4*m)+1 := by
  have hsq : (4*m*i)^2 < B^2 := (Nat.le_mul_of_pos_right _ hd).trans_lt hsharp
  have hsmall : 4*m*i < B := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
  have hdiv : i ≤ B/(4*m) := (Nat.le_div_iff_mul_le (by positivity)).mpr
    (by simpa only [mul_comm] using hsmall.le)
  exact Nat.lt_succ_of_le hdiv

/-- The original real-valued sharp window supplies the exact squared
integer boundary, without a floating-point conversion. -/
theorem sharp_class_inside_width {B d m i : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hsharp : (i : ℝ) < (B : ℝ)/(4*m*Real.sqrt (d : ℝ))) : i < B/(4*m)+1 := by
  have hden : (0 : ℝ) < 4*m*Real.sqrt (d : ℝ) := by positivity
  have hmul := (lt_div_iff₀ hden).mp hsharp
  have hsq := (sq_lt_sq₀ (by positivity : (0 : ℝ) ≤ (i : ℝ)*(4*m*Real.sqrt (d : ℝ)))
    (by positivity : (0 : ℝ) ≤ B)).mpr hmul
  have hroot := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)
  have he : ((i : ℝ)*(4*m*Real.sqrt (d : ℝ)))^2 = (4*m*i : ℕ)^2*d := by
    push_cast
    nlinarith
  rw [he] at hsq
  apply sharp_class_squared_inside_width hd hm
  exact_mod_cast hsq

/-- Unrounded square weights turn the factor-sum gap into one exact
square. This is the arithmetic price of the shared-centre restriction. -/
theorem square_weight_gap {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (u v : ℝ) :
    u^2*q+v^2*p-2*u*v*Real.sqrt (p*q) =
      (u*Real.sqrt q-v*Real.sqrt p)^2 := by
  rw [Real.sqrt_mul hp]
  have hpRoot := Real.sq_sqrt hp
  have hqRoot := Real.sq_sqrt hq
  nlinarith

private theorem counterexample_real_gap {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huv : u*v ≤ 39) :
    (100 : ℝ) ≤ ((u : ℝ)*Real.sqrt 65521-(v : ℝ)*Real.sqrt 46337)^2 := by
  have hpLo : (215 : ℝ) ≤ Real.sqrt 46337 := Real.le_sqrt_of_sq_le (by norm_num)
  have hpHi : Real.sqrt (46337 : ℝ) ≤ 216 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hqLo : (255 : ℝ) ≤ Real.sqrt 65521 := Real.le_sqrt_of_sq_le (by norm_num)
  have hqHi : Real.sqrt (65521 : ℝ) ≤ 256 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  by_cases horder : v ≤ u
  · have horderR : (v : ℝ) ≤ u := by exact_mod_cast horder
    have h1 := mul_le_mul_of_nonneg_left hqLo (by positivity : 0 ≤ (u : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hpHi (by positivity : 0 ≤ (v : ℝ))
    have hdiff : (39 : ℝ) ≤ (u : ℝ)*Real.sqrt 65521-(v : ℝ)*Real.sqrt 46337 := by linarith
    nlinarith
  · have hvu : u+1 ≤ v := by omega
    have hu5 : u ≤ 5 := by nlinarith
    have hvuR : (u : ℝ)+1 ≤ v := by exact_mod_cast hvu
    have hu5R : (u : ℝ) ≤ 5 := by exact_mod_cast hu5
    have h1 := mul_le_mul_of_nonneg_left hpLo (by positivity : 0 ≤ (v : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hqHi (by positivity : 0 ≤ (u : ℝ))
    have hdiff : (10 : ℝ) ≤ (v : ℝ)*Real.sqrt 46337-(u : ℝ)*Real.sqrt 65521 := by linarith
    nlinarith

/-- Exact semiprime and sixth-root budget for the coverage control.
Both prime factors lie outside the already covered quadratic prefix. -/
theorem counterexample_semiprime_budget :
    Nat.Prime 46337 ∧ Nat.Prime 65521 ∧ 46337 < 65521 ∧
      38^6 < 46337*65521 ∧ 46337*65521 ≤ 39^6 ∧
      39^2 < 46337 ∧ 39^2 < 65521 := by norm_num

/-- Every positive weight pair with square product in the full budget
misses even the padded width-39 window on this semiprime. -/
theorem counterexample_square_product_gap {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a*b ≤ 39^2) (hs : IsSquare (a*b)) :
    SemiprimeLehmanCoverage.literalCentre (46337*65521) (a*b)+100 ≤
      a*65521+b*46337 := by
  obtain ⟨h, u, v, hh, hu, hv, ha', hb'⟩ := square_product_weights ha hb hs
  have hprod : a*b = (h*u*v)^2 := by rw [ha', hb']; ring
  have hbound : h*u*v ≤ 39 := by nlinarith [hab]
  have huv : u*v ≤ 39 := by
    have hm : u*v ≤ h*(u*v) := Nat.le_mul_of_pos_left _ hh
    nlinarith
  have hgap := counterexample_real_gap hu hv huv
  have he := square_weight_gap (by norm_num : (0 : ℝ) ≤ 46337)
    (by norm_num : (0 : ℝ) ≤ 65521) (u : ℝ) (v : ℝ)
  norm_num at he
  have hweight : ((a*65521+b*46337 : ℕ) : ℝ) -
      2*(h*u*v : ℕ)*Real.sqrt (46337*65521 : ℕ) =
      (h : ℝ)*((u : ℝ)*Real.sqrt 65521-(v : ℝ)*Real.sqrt 46337)^2 := by
    rw [ha', hb']
    push_cast
    rw [← he]
    ring
  have h100 : (100 : ℝ) ≤ (h : ℝ)*
      ((u : ℝ)*Real.sqrt 65521-(v : ℝ)*Real.sqrt 46337)^2 := by
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    nlinarith
  have hc := Nat.ceil_lt_add_one
    (by positivity : (0 : ℝ) ≤ 2*(h*u*v : ℕ)*Real.sqrt (46337*65521 : ℕ))
  have hcentre : SemiprimeLehmanCoverage.literalCentre (46337*65521) (a*b) =
      ⌈2*(h*u*v : ℕ)*Real.sqrt (46337*65521 : ℕ)⌉₊ := by
    rw [ha', hb']
    exact square_product_centre _ _ _ _
  rw [← hcentre] at hc
  have hlt : (SemiprimeLehmanCoverage.literalCentre (46337*65521) (a*b) : ℝ)+99 <
      ((a*65521+b*46337 : ℕ) : ℝ) := by linarith
  have hNat : SemiprimeLehmanCoverage.literalCentre (46337*65521) (a*b)+99 <
      a*65521+b*46337 := by exact_mod_cast hlt
  omega

/-- The universally quantified candidate hit required by the full
Lehman theorem is false after restricting products to squares. -/
theorem counterexample_no_square_product_window {a b i : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a*b ≤ 39^2)
    (hs : IsSquare (a*b)) (hi : i < 39) :
    a*65521+b*46337 ≠ SemiprimeLehmanCoverage.literalCentre (46337*65521) (a*b)+i := by
  have hgap := counterexample_square_product_gap ha hb hab hs
  omega

/-- A primitive non-square-product row retains an exact hit on the same
input. The failure is caused by the proposed square-product restriction. -/
theorem counterexample_nonsquare_hit :
    Nat.Coprime 12 17 ∧ 12*17 ≤ 39^2 ∧ ¬IsSquare (12*17 : ℕ) ∧
      12*65521+17*46337 = SemiprimeLehmanCoverage.literalCentre (46337*65521) (12*17) := by
  norm_num [SemiprimeLehmanCoverage.literalCentre, SemiprimeLehmanCoverage.ceilSqrt]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- A finite kernel-checked certificate: every candidate in the actual
public class-1-through-16 list fails discriminant recovery on the control.
This uses kernel reduction, without compiler-trusting evaluation. -/
theorem counterexample_class_recovery_none :
    ∀ c ∈ classCandidates (46337*65521) 39 16,
      SemiprimeLehmanCoverage.recoverWeighted (46337*65521) c.1 c.2 = none := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Enlarging the cache to every class through 16 still loses universal
coverage of the sharp window, and even of its stated padded enclosure.
Weights need not be primitive and d need not be squarefree. -/
theorem counterexample_no_small_class_window {a b d m i : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d ≤ 16) (hm : 0 < m)
    (hab : a*b ≤ 39^2) (hclass : a*b = d*m^2) (hi : i < 39/(4*m)+1) :
    a*65521+b*46337 ≠ SemiprimeLehmanCoverage.literalCentre (46337*65521) (a*b)+i := by
  intro hsum
  obtain ⟨hp, hq, hpq, hlow, hhigh, hpB, hqB⟩ := counterexample_semiprime_budget
  have hap : a < 46337 := (Nat.le_mul_of_pos_right _ hb).trans hab |>.trans_lt hpB
  have hbq : b < 65521 := (Nat.le_mul_of_pos_left _ ha).trans hab |>.trans_lt hqB
  obtain ⟨factor, hfactor⟩ := SemiprimeLehmanCoverage.recoverWeighted_succeeds hp hq hpq ha hb hap hbq
  have hc := mem_classCandidates hd hdD hm (by simpa only [← hclass] using hab) hi
    (N := 46337*65521)
  have hnone := counterexample_class_recovery_none _ hc
  rw [← hclass] at hnone
  rw [← hsum] at hnone
  rw [hnone] at hfactor
  cases hfactor

/-- The exact original Lehman sharp window also fails on every weight
product in classes 1 through 16. This includes every representation,
not just the rows visited by a particular parametrization. -/
theorem counterexample_no_small_class_sharp_window {a b d m i : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d ≤ 16) (hm : 0 < m)
    (hab : a*b ≤ 39^2) (hclass : a*b = d*m^2)
    (hsharp : (i : ℝ) < 39/(4*Real.sqrt (a*b : ℕ))) :
    a*65521+b*46337 ≠ SemiprimeLehmanCoverage.literalCentre (46337*65521) (a*b)+i := by
  have he : ((a*b : ℕ) : ℝ) = (d : ℝ)*(m : ℝ)^2 := by exact_mod_cast hclass
  rw [he, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ d), Real.sqrt_sq (by positivity)] at hsharp
  have hden : 4*(Real.sqrt (d : ℝ)*(m : ℝ)) = 4*m*Real.sqrt (d : ℝ) := by ring
  rw [hden] at hsharp
  exact counterexample_no_small_class_window ha hb hd hdD hm hab hclass
    (sharp_class_inside_width hd hm hsharp)

/-- Full-width arithmetic candidates used solely to certify the wider
window control. Materializing this diagnostic list is not a fast search. -/
def wideClassCandidates (N B D : ℕ) : List (ℕ × ℕ) :=
  (List.range D).flatMap fun j =>
    (List.range ((B^2/(j+1)).sqrt)).flatMap fun l =>
      (List.range B).map fun i =>
        ((j+1)*(l+1)^2, SemiprimeLehmanCoverage.literalCentre N ((j+1)*(l+1)^2)+i)

/-- Every admissible class and full-width offset occurs in the control list. -/
theorem mem_wideClassCandidates {N B D d m i : ℕ} (hd : 0 < d) (hdD : d ≤ D)
    (hm : 0 < m) (hbudget : d*m^2 ≤ B^2) (hi : i < B) :
    (d*m^2, SemiprimeLehmanCoverage.literalCentre N (d*m^2)+i) ∈
      wideClassCandidates N B D := by
  have hM : m ≤ (B^2/d).sqrt := Nat.le_sqrt'.mpr
    ((Nat.le_div_iff_mul_le hd).mpr (by simpa only [mul_comm] using hbudget))
  simp only [wideClassCandidates, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨d-1, by omega, m-1, ?_, i, hi, ?_⟩
  · simpa only [Nat.sub_add_cancel hd] using (by omega : m-1 < (B^2/d).sqrt)
  · simp only [Nat.sub_add_cancel hd, Nat.sub_add_cancel hm]

/-- The wider-window control is also a genuine semiprime outside the
quadratic prefix, at its literal sixth-root width 25. -/
theorem wide_control_semiprime_budget :
    Nat.Prime 13309 ∧ Nat.Prime 15767 ∧ 13309 < 15767 ∧
      24^6 < 13309*15767 ∧ 13309*15767 ≤ 25^6 ∧
      25^2 < 13309 ∧ 25^2 < 15767 := by norm_num

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- Kernel reduction verifies every full-width candidate for classes
through 16 on the wider-window control. No reference prime guides this
public candidate list, and no compiler evaluation is trusted. -/
theorem wide_control_recovery_none :
    ∀ c ∈ wideClassCandidates (13309*15767) 25 16,
      SemiprimeLehmanCoverage.recoverWeighted (13309*15767) c.1 c.2 = none := by
  decide +kernel

/-- Even replacing the sharp window by all offsets below B does not
repair universal coverage of the fixed class-1-through-16 menu. -/
theorem wide_control_no_small_class_window {a b d m i : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d ≤ 16) (hm : 0 < m)
    (hab : a*b ≤ 25^2) (hclass : a*b = d*m^2) (hi : i < 25) :
    a*15767+b*13309 ≠ SemiprimeLehmanCoverage.literalCentre (13309*15767) (a*b)+i := by
  intro hsum
  obtain ⟨hp, hq, hpq, hlow, hhigh, hpB, hqB⟩ := wide_control_semiprime_budget
  have hap : a < 13309 := (Nat.le_mul_of_pos_right _ hb).trans hab |>.trans_lt hpB
  have hbq : b < 15767 := (Nat.le_mul_of_pos_left _ ha).trans hab |>.trans_lt hqB
  obtain ⟨factor, hfactor⟩ := SemiprimeLehmanCoverage.recoverWeighted_succeeds hp hq hpq ha hb hap hbq
  have hc := mem_wideClassCandidates hd hdD hm (by simpa only [← hclass] using hab) hi
    (N := 13309*15767)
  have hnone := wide_control_recovery_none _ hc
  rw [← hclass] at hnone
  rw [← hsum] at hnone
  rw [hnone] at hfactor
  cases hfactor

/-- The original cover has an exact hit in square class 19 on this
input, immediately outside the proposed fixed class menu. -/
theorem wide_control_outside_menu_hit :
    Nat.Coprime 16 19 ∧ 16*19 ≤ 25^2 ∧ 16*19 = 19*4^2 ∧
      16*15767+19*13309 = SemiprimeLehmanCoverage.literalCentre (13309*15767) (16*19) := by
  norm_num [SemiprimeLehmanCoverage.literalCentre, SemiprimeLehmanCoverage.ceilSqrt]

end RiemannGaussian.SemiprimeSquareProductCover
