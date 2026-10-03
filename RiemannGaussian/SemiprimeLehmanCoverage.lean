/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCartesianCompletion
import RiemannGaussian.SemiprimeGroupCoverage
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Universal arithmetic coverage of the literal weighted centres

Dirichlet approximation supplies Lehman's weighted factor-sum cover for
every remaining semiprime after the quadratic small-factor prefix. The
weights and sum are witnesses in the proof, not advice to the algorithm.
All searched centres depend only on the public product and weight product.

This is a classical coverage theorem. It does not provide a square-root
speedup over the entire cover or a universal one-sixth bit-cost theorem.
-/

namespace RiemannGaussian.SemiprimeLehmanCoverage

/-- Dirichlet approximation gives positive bounded-product weights and
the strict squared cross-difference bound used by Lehman's method.
The hypothesis q ≤ p*r is exactly the small-factor-prefix complement. -/
theorem exists_lehman_weights {p q r : ℕ} (hp : 0 < p) (hpq : p < q)
    (hr : 0 < r) (hpr : q ≤ p*r) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a*b ≤ r ∧
      ((a : ℝ)*q-(b : ℝ)*p)^2*r < (p : ℝ)*q := by
  have hP : 0 < (p : ℝ) := by exact_mod_cast hp
  have hQ : 0 < (q : ℝ) := by exact_mod_cast hp.trans hpq
  have hR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hPQ : (p : ℝ) < q := by exact_mod_cast hpq
  have hPR : (q : ℝ) ≤ (p : ℝ)*r := by exact_mod_cast hpr
  let L := Real.sqrt ((q : ℝ)*r/p)
  have hL : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hLsq : L^2*(p : ℝ) = (q : ℝ)*r := by
    dsimp [L]
    rw [Real.sq_sqrt (by positivity), div_mul_cancel₀ _ hP.ne']
  have hLone : 1 < L := by
    have hRone : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hQR : (q : ℝ) ≤ (q : ℝ)*r := by nlinarith
    by_contra hn
    have hle : L ≤ 1 := by linarith
    have hs : L^2 ≤ 1 := by nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hle)]
    have hm := mul_le_mul_of_nonneg_right hs hP.le
    nlinarith
  let n := ⌊L⌋₊
  have hn : 0 < n := Nat.floor_pos.mpr hLone.le
  have hnL : (n : ℝ) ≤ L := Nat.floor_le hL.le
  have hLn : L < (n : ℝ)+1 := Nat.lt_floor_add_one L
  have hn1 : 0 < (n : ℝ)+1 := by positivity
  obtain ⟨j, k, hk, hkn, he⟩ := Real.exists_int_int_abs_mul_sub_le ((p : ℝ)/q) hn
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hPL : (q : ℝ) ≤ (p : ℝ)*L := by
    have hm := mul_le_mul_of_nonneg_left hPR hQ.le
    have hs : ((p : ℝ)*L)^2 = (p : ℝ)*q*r := by nlinarith [hLsq]
    nlinarith
  have hPnext : (q : ℝ) < (p : ℝ)*((n : ℝ)+1) :=
    hPL.trans_lt (mul_lt_mul_of_pos_left hLn hP)
  have hratio : 1/((n : ℝ)+1) < (p : ℝ)/q := by
    apply (div_lt_div_iff₀ hn1 hQ).mpr
    nlinarith
  have hxi : 0 < (p : ℝ)/q := div_pos hP hQ
  have hj : (0 : ℝ) < (j : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hk1 hxi.le
    have hu := (abs_le.mp he).2
    nlinarith
  have hjInt : 0 < j := by exact_mod_cast hj
  let a := j.toNat
  let b := k.toNat
  have hja : (a : ℤ) = j := Int.toNat_of_nonneg hjInt.le
  have hkb : (b : ℤ) = k := Int.toNat_of_nonneg hk.le
  have haR : (a : ℝ) = (j : ℝ) := by exact_mod_cast hja
  have hbR : (b : ℝ) = (k : ℝ) := by exact_mod_cast hkb
  have ha : 0 < a := by exact_mod_cast (haR ▸ hj)
  have hb : 0 < b := by exact_mod_cast (hbR ▸ (by exact_mod_cast hk : (0 : ℝ) < k))
  have hbL : (b : ℝ) ≤ L := by rw [hbR]; exact hknR.trans hnL
  have hb0 : 0 ≤ (b : ℝ) := by positivity
  have heab : |(b : ℝ)*((p : ℝ)/q)-a| ≤ 1/((n : ℝ)+1) := by
    simpa only [haR, hbR] using he
  have haUpper : (a : ℝ) ≤ (b : ℝ)*((p : ℝ)/q)+1/((n : ℝ)+1) := by
    have hh := (abs_le.mp heab).1
    linarith
  have habUpper : (a : ℝ)*b ≤ ((p : ℝ)/q)*(b : ℝ)^2+(b : ℝ)/((n : ℝ)+1) := by
    calc
      (a : ℝ)*b ≤ ((b : ℝ)*((p : ℝ)/q)+1/((n : ℝ)+1))*b :=
        mul_le_mul_of_nonneg_right haUpper hb0
      _ = ((p : ℝ)/q)*(b : ℝ)^2+(b : ℝ)/((n : ℝ)+1) := by ring
  have hbSq : (b : ℝ)^2 ≤ L^2 := by nlinarith
  have hratioL : ((p : ℝ)/q)*L^2 = r := by
    apply (mul_right_cancel₀ hQ.ne')
    calc
      ((p : ℝ)/q)*L^2*q = L^2*p := by field_simp
      _ = (q : ℝ)*r := hLsq
      _ = (r : ℝ)*q := by ring
  have hsmall : (b : ℝ)/((n : ℝ)+1) < 1 :=
    (div_lt_one hn1).mpr (hbL.trans_lt hLn)
  have habReal : (a : ℝ)*b < (r : ℝ)+1 := by
    have hm := mul_le_mul_of_nonneg_left hbSq hxi.le
    rw [hratioL] at hm
    linarith
  have hab : a*b ≤ r := by
    have hc : a*b < r+1 := by exact_mod_cast habReal
    omega
  have hdiff : |(a : ℝ)*q-(b : ℝ)*p| ≤ (q : ℝ)/((n : ℝ)+1) := by
    have hm := mul_le_mul_of_nonneg_right heab hQ.le
    have hid : ((b : ℝ)*((p : ℝ)/q)-a)*q = -((a : ℝ)*q-(b : ℝ)*p) := by
      field_simp
      ring
    have habs : |(b : ℝ)*((p : ℝ)/q)-a| * (q : ℝ) = |(a : ℝ)*q-(b : ℝ)*p| := by
      calc
        _ = |(b : ℝ)*((p : ℝ)/q)-a| * |(q : ℝ)| := by rw [abs_of_pos hQ]
        _ = |((b : ℝ)*((p : ℝ)/q)-a)*q| := (abs_mul _ _).symm
        _ = |-((a : ℝ)*q-(b : ℝ)*p)| := by rw [hid]
        _ = |(a : ℝ)*q-(b : ℝ)*p| := abs_neg _
    rw [habs] at hm
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hm
  have hdiffL : |(a : ℝ)*q-(b : ℝ)*p| * L < (q : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hdiff hL.le
    have hid : (q : ℝ)/((n : ℝ)+1)*((n : ℝ)+1) = q :=
      div_mul_cancel₀ _ hn1.ne'
    have hlt := mul_lt_mul_of_pos_left hLn (div_pos hQ hn1)
    exact hm.trans_lt (by linarith)
  have hdiffSq : ((a : ℝ)*q-(b : ℝ)*p)^2*L^2 < (q : ℝ)^2 := by
    have hnonneg : 0 ≤ |(a : ℝ)*q-(b : ℝ)*p| * L := by positivity
    have hs := (sq_lt_sq₀ hnonneg hQ.le).mpr hdiffL
    simpa only [mul_pow, sq_abs] using hs
  refine ⟨a, b, ha, hb, hab, ?_⟩
  apply (mul_lt_mul_iff_right₀ hQ).mp
  calc
    (q : ℝ)*(((a : ℝ)*q-(b : ℝ)*p)^2*r) = ((a : ℝ)*q-(b : ℝ)*p)^2*(L^2*p) := by
      rw [hLsq]
      ring
    _ = ((a : ℝ)*q-(b : ℝ)*p)^2*L^2*p := by ring
    _ < (q : ℝ)^2*p := mul_lt_mul_of_pos_right hdiffSq hP
    _ = (q : ℝ)*((p : ℝ)*q) := by ring

/-- The exact weighted centre, before integer rounding. -/
theorem weighted_centre_eq {N k : ℝ} (hN : 0 ≤ N) (hk : 0 ≤ k) :
    Real.sqrt (4*k*N) = 2*Real.sqrt N*Real.sqrt k := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  have hN2 := Real.sq_sqrt hN
  have hk2 := Real.sq_sqrt hk
  calc
    4*k*N = 4*(Real.sqrt N)^2*(Real.sqrt k)^2 := by rw [hN2, hk2]; ring
    _ = (2*Real.sqrt N*Real.sqrt k)^2 := by ring

/-- The short Lehman interval follows from the squared cross-difference
bound, retaining its dependence on the actual product of the weights. -/
theorem factor_sum_gap {p q a b r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hc : (a*q-b*p)^2*r < p*q) :
    0 ≤ a*q+b*p-2*Real.sqrt (p*q)*Real.sqrt (a*b) ∧
      a*q+b*p-2*Real.sqrt (p*q)*Real.sqrt (a*b) <
        Real.sqrt (p*q)/(4*r*Real.sqrt (a*b)) := by
  let N := p*q
  let K := a*b
  let w := Real.sqrt N
  let z := Real.sqrt K
  let v := 2*w*z
  let u := a*q+b*p
  have hN : 0 < N := mul_pos hp hq
  have hK : 0 < K := mul_pos ha hb
  have hw : 0 < w := Real.sqrt_pos.mpr hN
  have hz : 0 < z := Real.sqrt_pos.mpr hK
  have hw2 : w^2 = N := Real.sq_sqrt hN.le
  have hz2 : z^2 = K := Real.sq_sqrt hK.le
  have hv2 : v^2 = 4*K*N := by dsimp [v]; rw [mul_pow, mul_pow, hw2, hz2]; ring
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hd : u^2-v^2 = (a*q-b*p)^2 := by rw [hv2]; dsimp [u, K, N]; ring
  have huv : v ≤ u := by nlinarith [sq_nonneg (a*q-b*p)]
  have hdelta : 0 ≤ u-v := sub_nonneg.mpr huv
  have hden : 4*w*z ≤ u+v := by dsimp [v] at huv ⊢; linarith
  have hprod : (u-v)*(u+v)*r < N := by
    calc
      (u-v)*(u+v)*r = (u^2-v^2)*r := by ring
      _ = (a*q-b*p)^2*r := by rw [hd]
      _ < N := hc
  change 0 ≤ u-v ∧ u-v < w/(4*r*z)
  refine ⟨hdelta, ?_⟩
  apply (lt_div_iff₀ (by positivity : 0 < 4*r*z)).mpr
  apply (mul_lt_mul_iff_right₀ hw).mp
  calc
    w*((u-v)*(4*r*z)) = ((u-v)*r)*(4*w*z) := by ring
    _ ≤ ((u-v)*r)*(u+v) := mul_le_mul_of_nonneg_left hden (mul_nonneg hdelta hr.le)
    _ = (u-v)*(u+v)*r := by ring
    _ < N := hprod
    _ = w*w := by nlinarith [hw2]

/-- Computable ceiling square root, using an exact integer equality test. -/
def ceilSqrt (n : ℕ) : ℕ :=
  if n.sqrt^2 = n then n.sqrt else n.sqrt+1

theorem ceilSqrt_eq_natCeil (n : ℕ) : ceilSqrt n = ⌈Real.sqrt (n : ℝ)⌉₊ := by
  have hs : (n.sqrt : ℝ)^2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hl : (n : ℝ) < ((n.sqrt : ℝ)+1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' n
  have hr : (Real.sqrt (n : ℝ))^2 = n := Real.sq_sqrt (by positivity)
  have h0 := Real.sqrt_nonneg (n : ℝ)
  unfold ceilSqrt
  split_ifs with he
  · have hsEq : (n.sqrt : ℝ)^2 = n := by exact_mod_cast he
    have hroot : Real.sqrt (n : ℝ) = n.sqrt := by nlinarith
    rw [hroot, Nat.ceil_natCast]
  · apply Nat.le_antisymm
    · have hstrict : (n.sqrt : ℝ) < Real.sqrt (n : ℝ) := by
        have hlt : n.sqrt^2 < n := lt_of_le_of_ne (Nat.sqrt_le' n) he
        have hltR : (n.sqrt : ℝ)^2 < n := by exact_mod_cast hlt
        nlinarith
      have hceil := Nat.le_ceil (Real.sqrt (n : ℝ))
      have hnat : n.sqrt < ⌈Real.sqrt (n : ℝ)⌉₊ := by exact_mod_cast hstrict.trans_le hceil
      omega
    · apply Nat.ceil_le.mpr
      push_cast
      nlinarith

/-- Literal integer centre indexed only by the public input and k=ab. -/
def literalCentre (N k : ℕ) : ℕ := ceilSqrt (4*k*N)

theorem literalCentre_eq_natCeil (N k : ℕ) :
    literalCentre N k = ⌈2*Real.sqrt (N : ℝ)*Real.sqrt (k : ℝ)⌉₊ := by
  rw [literalCentre, ceilSqrt_eq_natCeil]
  push_cast
  rw [weighted_centre_eq (by positivity) (by positivity)]

/-- A failed quadratic prefix and a sixth-root budget bound imply the
ratio condition needed by Lehman's universal approximation theorem. -/
theorem prefix_complement_ratio {p q B : ℕ} (hp : 0 < p)
    (hsmall : B^2 < p) (hbudget : p*q ≤ B^6) : q ≤ p*B^2 := by
  have hs := Nat.pow_le_pow_left hsmall.le 2
  have hm := Nat.mul_le_mul_right (B^2) hs
  have hn : p*q ≤ p*(p*B^2) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hn hp

/-- Every remaining factor pair has a literal rounded-centre window hit.
The weights need only satisfy ab ≤ B²; no factor-ratio promise or small
local-order premise appears. Constructing all these rows is still costly. -/
theorem exists_literal_window {p q B : ℕ} (hp : 0 < p) (hpq : p < q)
    (hB : 0 < B) (hsmall : B^2 < p) (hbudget : p*q ≤ B^6) :
    ∃ a b i : ℕ, 0 < a ∧ 0 < b ∧ a*b ≤ B^2 ∧ i < B ∧
      (i : ℝ) < (B : ℝ)/(4*Real.sqrt ((a : ℝ)*b)) ∧
      a*q+b*p = literalCentre (p*q) (a*b)+i := by
  obtain ⟨a, b, ha, hb, hab, hcross⟩ := exists_lehman_weights hp hpq (by positivity : 0 < B^2)
    (prefix_complement_ratio hp hsmall hbudget)
  have hP : 0 < (p : ℝ) := by exact_mod_cast hp
  have hQ : 0 < (q : ℝ) := by exact_mod_cast hp.trans hpq
  have hA : 0 < (a : ℝ) := by exact_mod_cast ha
  have hBb : 0 < (b : ℝ) := by exact_mod_cast hb
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB
  have hgap := factor_sum_gap hP hQ hA hBb (by positivity : 0 < (B : ℝ)^2)
    (by exact_mod_cast hcross)
  have hroot : Real.sqrt ((p : ℝ)*q) ≤ (B : ℝ)^3 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hN : (p : ℝ)*q ≤ (B : ℝ)^6 := by exact_mod_cast hbudget
    nlinarith
  have hZ : 0 < Real.sqrt ((a : ℝ)*b) := Real.sqrt_pos.mpr (by positivity)
  have hden : 0 < 4*(B : ℝ)^2*Real.sqrt ((a : ℝ)*b) := by positivity
  have hbound : (a : ℝ)*q+b*p-2*Real.sqrt ((p : ℝ)*q)*Real.sqrt ((a : ℝ)*b) <
      (B : ℝ)/(4*Real.sqrt ((a : ℝ)*b)) := by
    have hm := div_le_div_of_nonneg_right hroot hden.le
    have he : (B : ℝ)^3/(4*(B : ℝ)^2*Real.sqrt ((a : ℝ)*b)) =
        (B : ℝ)/(4*Real.sqrt ((a : ℝ)*b)) := by field_simp
    rw [he] at hm
    exact hgap.2.trans_le hm
  have hC : literalCentre (p*q) (a*b) ≤ a*q+b*p := by
    rw [literalCentre_eq_natCeil]
    apply Nat.ceil_le.mpr
    push_cast
    linarith [hgap.1]
  let i := a*q+b*p-literalCentre (p*q) (a*b)
  have hiR : (i : ℝ) = (a : ℝ)*q+b*p-(literalCentre (p*q) (a*b) : ℝ) := by
    dsimp [i]
    rw [Nat.cast_sub hC]
    push_cast
    rfl
  have hceil := Nat.le_ceil (2*Real.sqrt ((p*q : ℕ) : ℝ)*Real.sqrt ((a*b : ℕ) : ℝ))
  rw [← literalCentre_eq_natCeil] at hceil
  push_cast at hceil
  have hiBound : (i : ℝ) < (B : ℝ)/(4*Real.sqrt ((a : ℝ)*b)) := by
    rw [hiR]
    linarith
  have hab1 : (1 : ℝ) ≤ (a : ℝ)*b := by exact_mod_cast Nat.mul_pos ha hb
  have hZ1 : 1 ≤ Real.sqrt ((a : ℝ)*b) := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ (a : ℝ)*b)
    nlinarith [Real.sqrt_nonneg ((a : ℝ)*b)]
  have hlimit : (B : ℝ)/(4*Real.sqrt ((a : ℝ)*b)) ≤ B :=
    div_le_self hBpos.le (by linarith)
  have hi : i < B := by exact_mod_cast hiBound.trans_le hlimit
  exact ⟨a, b, i, ha, hb, hab, hi, hiBound, by dsimp [i]; omega⟩

/-- The complete prefix turns the small-factor premise into a checked
public branch condition. This is universal arithmetic coverage, without
asserting that the entire weighted family fits a one-sixth work budget. -/
theorem exists_literal_window_after_prefix {p q B : ℕ} (hp : p.Prime) (hpq : p < q)
    (hB : 0 < B) (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1) :
    ∃ a b i : ℕ, 0 < a ∧ 0 < b ∧ a*b ≤ B^2 ∧ i < B ∧
      (i : ℝ) < (B : ℝ)/(4*Real.sqrt ((a : ℝ)*b)) ∧
      a*q+b*p = literalCentre (p*q) (a*b)+i := by
  rw [SemiprimeGroupCoverage.prefixProduct_eq_factorial] at hclear
  exact exists_literal_window hp.pos hpq hB
    (SemiprimeGroupCoverage.failed_prefix_excludes_small_prime hp (dvd_mul_right p q) hclear)
    hbudget

/-- Weighted factor-sum congruence, keeping the exact integer centre.
The local Fermat period makes a genuine window hit an anchor collision. -/
theorem weighted_anchor_hit {G : Type*} [CommGroup G] (g : G)
    {p q a b C i : ℤ} (hperiod : g^(p-1) = 1) (hsum : a*q+b*p = C+i) :
    SemiprimeRowStructure.rowAnchor g (p*q) a b C = g^i := by
  have he : a*(p*q)+b-C = (p-1)*(a*q-b)+i := by nlinarith only [hsum]
  rw [SemiprimeRowStructure.rowAnchor, he, zpow_add, zpow_mul, hperiod, one_zpow, one_mul]

/-- Every remaining semiprime has a literal collision in its hidden prime
field for every unit base. Whole-modulus collisions may require the
weighted discriminant path rather than shared-root deflation. -/
theorem exists_literal_prime_collision {p q B : ℕ} (hp : p.Prime) (hpq : p < q)
    (hB : 0 < B) (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1)
    (g : (ZMod p)ˣ) :
    ∃ a b i : ℕ, 0 < a ∧ 0 < b ∧ a*b ≤ B^2 ∧ i < B ∧
      SemiprimeRowStructure.rowAnchor g (p*q : ℕ) a b (literalCentre (p*q) (a*b)) = g^i := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, i, ha, hb, hab, hi, hbound, hsum⟩ :=
    exists_literal_window_after_prefix hp hpq hB hbudget hclear
  have hperiod : g^((p : ℤ)-1) = 1 := by
    have hh : g^((p-1 : ℕ) : ℤ) = 1 := by
      simpa only [zpow_natCast] using ZMod.units_pow_card_sub_one_eq_one p g
    simpa only [Nat.cast_sub hp.one_le, Nat.cast_one] using hh
  refine ⟨a, b, i, ha, hb, hab, hi, ?_⟩
  have hsumI : (a : ℤ)*q+b*p = (literalCentre (p*q) (a*b) : ℤ)+i := by exact_mod_cast hsum
  simpa only [Nat.cast_mul, zpow_natCast] using weighted_anchor_hit g hperiod hsumI

/-- The positive discriminant root computed from public N, k and s. -/
def discriminantRoot (N k s : ℕ) : ℕ :=
  (s+(s^2-4*k*N).sqrt)/2

/-- Exact square discriminant when the candidate is a weighted factor sum. -/
theorem weighted_discriminant_sq {p q a b : ℕ} :
    ∃ t : ℕ, (a*q+b*p)^2-4*(a*b)*(p*q) = t^2 := by
  have he : 4*(a*b)*(p*q) = 4*(a*q)*(b*p) := by ring
  rw [he]
  by_cases hh : b*p ≤ a*q
  · refine ⟨a*q-b*p, ?_⟩
    have hs := Nat.sub_add_cancel hh
    have hid : (a*q+b*p)^2 = (a*q-b*p)^2+4*(a*q)*(b*p) := by nlinarith
    rw [hid, Nat.add_sub_cancel]
  · have hh' : a*q ≤ b*p := by omega
    refine ⟨b*p-a*q, ?_⟩
    have hs := Nat.sub_add_cancel hh'
    have hid : (a*q+b*p)^2 = (b*p-a*q)^2+4*(a*q)*(b*p) := by nlinarith
    rw [hid, Nat.add_sub_cancel]

/-- The quadratic-formula root is the larger weighted prime multiple;
the algorithm does not need either weight separately to compute it. -/
theorem discriminantRoot_weighted (p q a b : ℕ) :
    discriminantRoot (p*q) (a*b) (a*q+b*p) = max (a*q) (b*p) := by
  have he : 4*(a*b)*(p*q) = 4*(a*q)*(b*p) := by ring
  unfold discriminantRoot
  rw [he]
  by_cases hh : b*p ≤ a*q
  · have hs := Nat.sub_add_cancel hh
    have hid : (a*q+b*p)^2 = (a*q-b*p)^2+4*(a*q)*(b*p) := by nlinarith
    rw [hid, Nat.add_sub_cancel, Nat.sqrt_eq', Nat.max_eq_left hh]
    omega
  · have hh' : a*q ≤ b*p := by omega
    have hs := Nat.sub_add_cancel hh'
    have hid : (a*q+b*p)^2 = (b*p-a*q)^2+4*(a*q)*(b*p) := by nlinarith
    rw [hid, Nat.add_sub_cancel, Nat.sqrt_eq', Nat.max_eq_right hh']
    omega

private theorem gcd_weighted_multiple {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (ha : 0 < a) (hap : a < p) : (p*q).gcd (a*q) = q := by
  rw [Nat.mul_comm p q]
  apply SemiprimeOrderSeparation.gcd_semiprime_of_separating_residue hp
  · exact dvd_mul_left q a
  · intro hd
    rcases hp.dvd_mul.mp hd with hleft | hright
    · exact Nat.not_dvd_of_pos_of_lt ha hap hleft
    · rcases hq.eq_one_or_self_of_dvd p hright with hp1 | heq
      · exact hp.ne_one hp1
      · exact hne heq

/-- Check a square discriminant and return only a certified proper GCD.
This path retains the useful weighted information in global collisions. -/
def recoverWeighted (N k s : ℕ) : Option ℕ :=
  let D := s^2-4*k*N
  if D.sqrt^2 = D then SemiprimeGroupSelection.checkedSignal N (discriminantRoot N k s)
  else none

theorem recoverWeighted_sound {N k s d : ℕ} (hh : recoverWeighted N k s = some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  dsimp only [recoverWeighted] at hh
  split_ifs at hh
  exact SemiprimeGroupSelection.checkedSignal_sound hh

/-- A true window hit supplies a proper factor through the discriminant,
even when its modular signal is coherent across both hidden primes. -/
theorem recoverWeighted_succeeds {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (ha : 0 < a) (hb : 0 < b) (hap : a < p) (hbq : b < q) :
    ∃ d, recoverWeighted (p*q) (a*b) (a*q+b*p) = some d := by
  obtain ⟨t, ht⟩ := weighted_discriminant_sq (p := p) (q := q) (a := a) (b := b)
  have hs : ((a*q+b*p)^2-4*(a*b)*(p*q)).sqrt^2 = (a*q+b*p)^2-4*(a*b)*(p*q) := by
    rw [ht, Nat.sqrt_eq']
  have hgp := gcd_weighted_multiple hp hq hpq.ne ha hap
  have hgq := gcd_weighted_multiple hq hp hpq.ne.symm hb hbq
  have hpProper : SemiprimeGroupSelection.ProperDivisor (p*q) p := by
    exact ⟨hp.one_lt, by nlinarith [hq.one_lt], dvd_mul_right p q⟩
  have hqProper : SemiprimeGroupSelection.ProperDivisor (p*q) q := by
    exact ⟨hq.one_lt, by nlinarith [hp.one_lt], dvd_mul_left q p⟩
  unfold recoverWeighted
  rw [if_pos hs, discriminantRoot_weighted]
  by_cases hh : b*p ≤ a*q
  · rw [Nat.max_eq_left hh]
    exact ⟨q, by simp [SemiprimeGroupSelection.checkedSignal, hgp, hqProper.1, hqProper.2.1]⟩
  · have hh' : a*q ≤ b*p := by omega
    rw [Nat.max_eq_right hh']
    have hg : (p*q).gcd (b*p) = p := by simpa only [Nat.mul_comm] using hgq
    exact ⟨p, by simp [SemiprimeGroupSelection.checkedSignal, hg, hpProper.1, hpProper.2.1]⟩

/-- Public integer width enclosing the sharp real-valued Lehman window.
The padded endpoint is harmless and avoids floating-point decisions. -/
def windowWidth (B k : ℕ) : ℕ := B/k.sqrt+1

/-- Public candidate list, with no private weights or prime labels. -/
def candidatePairs (N B : ℕ) : List (ℕ × ℕ) :=
  (List.range (B^2)).flatMap fun j =>
    (List.range (windowWidth B (j+1))).map fun i => (j+1, literalCentre N (j+1)+i)

/-- Every weight-product row contributes at least one public candidate.
Materializing this explicit list therefore already visits the quadratic
number of entries; this is a cost obstruction for this definition only. -/
theorem candidatePairs_length_ge (N B : ℕ) : B^2 ≤ (candidatePairs N B).length := by
  have hlength : ∀ l : List ℕ, l.length ≤
      (l.flatMap fun j => (List.range (windowWidth B (j+1))).map
        fun i => (j+1, literalCentre N (j+1)+i)).length := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.flatMap_cons, List.length_cons, List.length_append,
        List.length_map, List.length_range]
      have hw : 0 < windowWidth B (j+1) := Nat.succ_pos _
      omega
  simpa only [candidatePairs, List.length_range] using hlength (List.range (B^2))

theorem mem_candidatePairs {N B k i : ℕ} (hk : 0 < k) (hkB : k ≤ B^2)
    (hi : i < windowWidth B k) : (k, literalCentre N k+i) ∈ candidatePairs N B := by
  simp only [candidatePairs, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨k-1, by omega, i, by simpa only [Nat.sub_add_cancel hk] using hi,
    by simp only [Nat.sub_add_cancel hk]⟩

theorem sharp_window_inside_width {B k i : ℕ} (hk : 0 < k)
    (hi : (i : ℝ) < (B : ℝ)/(4*Real.sqrt (k : ℝ))) : i < windowWidth B k := by
  have hs : 0 < k.sqrt := Nat.sqrt_pos.mpr hk
  have hroot : (k.sqrt : ℝ) ≤ Real.sqrt (k : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' k
  have hZ : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hmul : (i : ℝ)*(4*Real.sqrt (k : ℝ)) < B := (lt_div_iff₀ (by positivity)).mp hi
  have hle : (i : ℝ)*(k.sqrt : ℝ) ≤ (i : ℝ)*(4*Real.sqrt (k : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hNat : i*k.sqrt ≤ B := by exact_mod_cast (hle.trans_lt hmul).le
  have hd : i ≤ B/k.sqrt := (Nat.le_div_iff_mul_le hs).mpr hNat
  exact Nat.lt_succ_of_le hd

/-- The universal weighted witness occurs in the actual public candidate
list, where its discriminant supplies a proper divisor. -/
theorem candidatePairs_have_factor_after_prefix {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hB : 0 < B)
    (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1) :
    ∃ c ∈ candidatePairs (p*q) B, ∃ d, recoverWeighted (p*q) c.1 c.2 = some d := by
  obtain ⟨a, b, i, ha, hb, hab, hi, hsharp, hsum⟩ :=
    exists_literal_window_after_prefix hp hpq hB hbudget hclear
  have hpB : B^2 < p := by
    rw [SemiprimeGroupCoverage.prefixProduct_eq_factorial] at hclear
    exact SemiprimeGroupCoverage.failed_prefix_excludes_small_prime hp (dvd_mul_right p q) hclear
  have habPos : 0 < a*b := Nat.mul_pos ha hb
  have haLe : a ≤ a*b := Nat.le_mul_of_pos_right _ hb
  have hbLe : b ≤ a*b := Nat.le_mul_of_pos_left _ ha
  obtain ⟨d, hd⟩ := recoverWeighted_succeeds hp hq hpq ha hb
    (haLe.trans hab |>.trans_lt hpB) (hbLe.trans hab |>.trans_lt (hpB.trans hpq))
  refine ⟨(a*b, literalCentre (p*q) (a*b)+i), ?_, d, ?_⟩
  · exact mem_candidatePairs habPos hab (sharp_window_inside_width habPos (by simpa only [Nat.cast_mul] using hsharp))
  · simpa only [hsum] using hd

/-- Search the public arithmetic cover. Its construction is still on the
one-third scale; this definition does not claim the target cost bound. -/
def factorAfterPrefix (N B : ℕ) : Option ℕ :=
  (candidatePairs N B).findSome? fun c => recoverWeighted N c.1 c.2

theorem factorAfterPrefix_sound {N B d : ℕ} (hh : factorAfterPrefix N B = some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  obtain ⟨l₁, c, l₂, he, hc, hnone⟩ := List.findSome?_eq_some_iff.mp hh
  exact recoverWeighted_sound hc

/-- Complete correctness on the full prefix-complement population.
No empirical curve cover or unproved order assumption is used. -/
theorem factorAfterPrefix_succeeds {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hB : 0 < B) (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1) :
    ∃ d, factorAfterPrefix (p*q) B = some d := by
  obtain ⟨c, hc, d, hd⟩ := candidatePairs_have_factor_after_prefix hp hq hpq hB hbudget hclear
  cases hs : factorAfterPrefix (p*q) B with
  | some d' => exact ⟨d', rfl⟩
  | none =>
    have hn := List.findSome?_eq_none_iff.mp hs c hc
    rw [hd] at hn
    contradiction

private theorem checked_prime_factor {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    SemiprimeGroupSelection.checkedSignal (p*q) p = some p := by
  have hg : (p*q).gcd p = p := Nat.gcd_eq_right (dvd_mul_right p q)
  have hlt : p < p*q := by nlinarith [hp.one_lt, hq.one_lt]
  simp [SemiprimeGroupSelection.checkedSignal, hg, hp.one_lt, hlt]

private theorem trial_scan_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ d, SemiprimeCartesianCompletion.scanProper (p*q) (List.range (p*q)) = some d := by
  have hc := checked_prime_factor hp hq
  have hm : p ∈ List.range (p*q) := List.mem_range.mpr (by nlinarith [hp.one_lt, hq.one_lt])
  cases hs : SemiprimeCartesianCompletion.scanProper (p*q) (List.range (p*q)) with
  | some d => exact ⟨d, rfl⟩
  | none =>
    have hn := (SemiprimeCartesianCompletion.scanProper_none_iff _ _).mp hs p hm
    rw [hc] at hn
    contradiction

/-- Full arithmetic baseline: finite small inputs, perfect squares,
quadratic prefix, then the complete Lehman candidate cover. This definition
has universal correctness, but no claimed one-sixth bit-cost bound. -/
def factorByCover (N B : ℕ) : Option ℕ :=
  if B < 4 then SemiprimeCartesianCompletion.scanProper N (List.range N)
  else if N.sqrt^2 = N then SemiprimeGroupSelection.checkedSignal N N.sqrt
  else match SemiprimeGroupSelection.checkedSignal N (SemiprimeGroupCoverage.prefixProduct B) with
    | some d => some d
    | none => factorAfterPrefix N B

theorem factorByCover_sound {N B d : ℕ} (hh : factorByCover N B = some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  unfold factorByCover at hh
  split_ifs at hh with hsmall hsquare
  · exact SemiprimeCartesianCompletion.scanProper_sound hh
  · exact SemiprimeGroupSelection.checkedSignal_sound hh
  · cases hc : SemiprimeGroupSelection.checkedSignal N (SemiprimeGroupCoverage.prefixProduct B) with
    | none => exact factorAfterPrefix_sound (by simpa only [hc] using hh)
    | some d' =>
      have he : d' = d := by simpa only [hc, Option.some.injEq] using hh
      subst d'
      exact SemiprimeGroupSelection.checkedSignal_sound hc

/-- Every semiprime, including prime squares, is factored by the complete
public arithmetic cover at its literal sixth-root width. This establishes
correctness; the explicit search still exceeds the target bit cost. -/
theorem factorByCover_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hbudget : p*q ≤ B^6) (hlower : (B-1)^6 < p*q) :
    ∃ d, factorByCover (p*q) B = some d := by
  by_cases hsmall : B < 4
  · obtain ⟨d, hd⟩ := trial_scan_semiprime hp hq
    exact ⟨d, by simpa only [factorByCover, if_pos hsmall] using hd⟩
  · have hB : 4 ≤ B := by omega
    by_cases hsquare : (p*q).sqrt^2 = p*q
    · have hn : 4 ≤ p*q := by nlinarith [hp.two_le, hq.two_le]
      have hr : 1 < (p*q).sqrt := by nlinarith
      have hlt : (p*q).sqrt < p*q := by nlinarith
      have hdiv : (p*q).sqrt ∣ p*q := ⟨(p*q).sqrt, by nlinarith⟩
      have hg : (p*q).gcd (p*q).sqrt = (p*q).sqrt := Nat.gcd_eq_right hdiv
      exact ⟨(p*q).sqrt, by simp [factorByCover, hsmall, hsquare,
        SemiprimeGroupSelection.checkedSignal, hg, hr, hlt]⟩
    · have hstrict : p < q := by
        apply lt_of_le_of_ne hpq
        intro he
        have hs : (p*q).sqrt^2 = p*q := by rw [← he]; simp [← pow_two]
        exact hsquare hs
      have hqB := SemiprimeGroupCoverage.larger_factor_above_prefix hB hpq hlower
      cases hc : SemiprimeGroupSelection.checkedSignal (p*q) (SemiprimeGroupCoverage.prefixProduct B) with
      | some d => exact ⟨d, by simp only [factorByCover, if_neg hsmall, if_neg hsquare, hc]⟩
      | none =>
        have hpB : B^2 < p := by
          by_contra hn
          have hpSmall : p ≤ B^2 := by omega
          have hg := SemiprimeGroupCoverage.polynomial_prefix_recovers_under_sixth_budget
            hp hq hB hpq hlower hpSmall
          have hs : SemiprimeGroupSelection.checkedSignal (p*q)
              (SemiprimeGroupCoverage.prefixProduct B) = some p := by
            simp [SemiprimeGroupSelection.checkedSignal, hg, hp.one_lt,
              show p < p*q by nlinarith [hp.one_lt, hq.one_lt]]
          rw [hc] at hs
          contradiction
        have hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1 := by
          rw [SemiprimeGroupCoverage.prefixProduct_eq_factorial]
          have hpc := hp.coprime_iff_not_dvd.mpr
            (SemiprimeGroupCoverage.prime_not_dvd_factorial_above hp _ hpB)
          have hqc := hq.coprime_iff_not_dvd.mpr
            (SemiprimeGroupCoverage.prime_not_dvd_factorial_above hq _ hqB)
          exact hpc.mul_left hqc
        obtain ⟨d, hd⟩ := factorAfterPrefix_succeeds hp hq hstrict (by omega) hbudget hclear
        exact ⟨d, by simpa only [factorByCover, if_neg hsmall, if_neg hsquare, hc] using hd⟩

private theorem sixth_bound_exists (N : ℕ) : ∃ B : ℕ, N ≤ B^6 :=
  ⟨N+1, (Nat.le_succ N).trans (Nat.le_pow (by decide : 0 < 6))⟩

/-- Minimal integer width satisfying the public sixth-power budget. The
definition is computable and does not consult a prime factor of N. -/
def sixthWidth (N : ℕ) : ℕ := Nat.find (sixth_bound_exists N)

theorem sixthWidth_upper (N : ℕ) : N ≤ (sixthWidth N)^6 :=
  Nat.find_spec (sixth_bound_exists N)

theorem sixthWidth_lower {N : ℕ} (hN : 0 < N) : (sixthWidth N-1)^6 < N := by
  have hpos : 0 < sixthWidth N := by
    apply (Nat.find_pos (sixth_bound_exists N)).mpr
    simpa only [zero_pow (by decide : 6 ≠ 0)] using Nat.not_le_of_gt hN
  exact lt_of_not_ge (Nat.find_min (sixth_bound_exists N) (by omega : sixthWidth N-1 < sixthWidth N))

/-- Single-public-input baseline whose universal correctness is checked
below. Achieving the goal requires replacing its expensive cover search
and proving the complete one-sixth bit-operation bound. -/
def factor (N : ℕ) : Option ℕ := factorByCover N (sixthWidth N)

theorem factor_sound {N d : ℕ} (hh : factor N = some d) :
    SemiprimeGroupSelection.ProperDivisor N d := factorByCover_sound hh

/-- Unconditional full semiprime correctness, with no order, smoothness,
ratio, curve, distinctness or hidden-information assumption. This does not
assert a one-sixth runtime bound for the constructed baseline. -/
theorem factor_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ d, factor (p*q) = some d ∧ SemiprimeGroupSelection.ProperDivisor (p*q) d := by
  have hN : 0 < p*q := Nat.mul_pos hp.pos hq.pos
  have hbudget := sixthWidth_upper (p*q)
  have hlower := sixthWidth_lower hN
  have hs : ∃ d, factor (p*q) = some d := by
    by_cases hpq : p ≤ q
    · exact factorByCover_semiprime hp hq hpq hbudget hlower
    · have hqp : q ≤ p := by omega
      have hb : q*p ≤ (sixthWidth (q*p))^6 := sixthWidth_upper _
      have hl := sixthWidth_lower (Nat.mul_pos hq.pos hp.pos)
      simpa only [factor, Nat.mul_comm] using factorByCover_semiprime hq hp hqp hb hl
  obtain ⟨d, hd⟩ := hs
  exact ⟨d, hd, factor_sound hd⟩

end RiemannGaussian.SemiprimeLehmanCoverage
