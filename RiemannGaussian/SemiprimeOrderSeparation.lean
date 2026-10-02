/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# A cheap semiprime order separator

Raising a unit to `p*q-1` removes the common part of its two local
orders. Subsequent common powers preserve coprimality. These are exact
information/extraction lemmas, not a generic one-sixth factoring theorem.
This side-investigation algebra is checked in the ordinary library; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimeOrderSeparation

theorem gcd_sub_one_mul {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (p - 1).gcd (p*q - 1) = (p - 1).gcd (q - 1) := by
  have hqp : q ≤ p*q := by nlinarith
  have he : p*q - 1 = (q - 1) + (p - 1)*q := by
    rw [Nat.sub_mul]
    omega
  rw [he, Nat.mul_comm (p - 1) q, Nat.gcd_add_mul_right_right]

theorem gcd_sub_one_mul_right {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (q - 1).gcd (p*q - 1) = (p - 1).gcd (q - 1) := by
  simpa [Nat.mul_comm, Nat.gcd_comm] using gcd_sub_one_mul hq hp

theorem order_pow_dvd_quotient {G : Type*} [Group G] (a : G)
    {A E g : ℕ} (ha : orderOf a ∣ A) (hgA : g ∣ A) (hgE : g ∣ E) :
    orderOf (a^E) ∣ A/g := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← pow_mul]
  apply (orderOf_dvd_iff_pow_eq_one).mp
  apply ha.trans
  have h := Nat.mul_dvd_mul_right hgE (A/g)
  simpa [Nat.mul_div_cancel' hgA] using h

/-- A common exponent divisible by the common cardinality part separates
the resulting local periods in any two finite-order groups. -/
theorem projected_orders_coprime_of_cardinalities {G H : Type*}
    [Group G] [Group H] (a : G) (b : H) {A B E : ℕ}
    (hA : 0 < A) (ha : orderOf a ∣ A) (hb : orderOf b ∣ B)
    (hE : A.gcd B ∣ E) :
    (orderOf (a^E)).Coprime (orderOf (b^E)) := by
  have hpa := order_pow_dvd_quotient a ha (Nat.gcd_dvd_left A B) hE
  have hpb := order_pow_dvd_quotient b hb (Nat.gcd_dvd_right A B) hE
  exact (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left B hA)).of_dvd hpa hpb

private theorem gcd_complement {A B E q : ℕ} (he : E+B=A*q) :
    A.gcd E = A.gcd B := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left A E)
    apply (Nat.dvd_add_iff_right (Nat.gcd_dvd_right A E)).mpr
    rw [he]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left A E) q
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left A B)
    apply (Nat.dvd_add_iff_left (Nat.gcd_dvd_right A B)).mpr
    rw [he]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left A B) q

theorem gcd_minus_plus {p q : ℕ} (hp : 0 < p) :
    (p-1).gcd (p*q+1) = (p-1).gcd (q+1) := by
  have he : p*q+1 = (q+1)+(p-1)*q := by
    rw [Nat.sub_mul]
    have hq : q ≤ p*q := by nlinarith
    omega
  rw [he, Nat.mul_comm (p-1) q, Nat.gcd_add_mul_right_right]

theorem gcd_plus_minus {p q : ℕ} (hq : 0 < q) :
    (p+1).gcd (p*q+1) = (p+1).gcd (q-1) := by
  apply gcd_complement (q := q)
  have hs : q-1+1=q := by omega
  nlinarith

theorem gcd_plus_plus {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (p+1).gcd (p*q-1) = (p+1).gcd (q+1) := by
  apply gcd_complement (q := q)
  have hm : 0 < p*q := Nat.mul_pos hp hq
  have hs : p*q-1+1=p*q := by omega
  nlinarith

/-- `split=true` encodes local Legendre colour +1; false encodes -1.
These local colours are hypotheses, not an oracle used by the program. -/
def colourCardinality (p : ℕ) (split : Bool) : ℕ := if split then p-1 else p+1

/-- The public Jacobi product chooses N-1 when colours agree and N+1
when they differ. Neither separate local colour is needed to compute it. -/
def colourExponent (p q : ℕ) (left right : Bool) : ℕ :=
  if left=right then p*q-1 else p*q+1

theorem colour_gcd_separator {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (left right : Bool) :
    (colourCardinality p left).gcd (colourExponent p q left right) =
      (colourCardinality p left).gcd (colourCardinality q right) := by
  cases left <;> cases right <;>
    simp only [colourCardinality,colourExponent,Bool.false_eq_true,Bool.true_eq_false,
      if_false,if_true] <;>
    first | exact gcd_plus_plus hp hq | exact gcd_plus_minus hq |
      exact gcd_minus_plus hp | exact gcd_sub_one_mul hp hq

theorem coloured_projected_orders_coprime {G H : Type*} [Group G] [Group H]
    (a : G) (b : H) {p q : ℕ} (hp : 1 < p) (hq : 0 < q)
    (left right : Bool)
    (ha : orderOf a ∣ colourCardinality p left)
    (hb : orderOf b ∣ colourCardinality q right) :
    (orderOf (a^(colourExponent p q left right))).Coprime
      (orderOf (b^(colourExponent p q left right))) := by
  have hpos : 0 < colourCardinality p left := by
    cases left
    · simp [colourCardinality]
    · simp [colourCardinality]; omega
  apply projected_orders_coprime_of_cardinalities a b hpos ha hb
  rw [← colour_gcd_separator (by omega) hq left right]
  exact Nat.gcd_dvd_right _ _

/-- Equal mixed-colour cardinalities are the public twin-factor case. -/
theorem mixed_equal_cardinalities_square {p q : ℕ}
    (h : p+1=q-1) (hq : 0 < q) : p*q+1=(p+1)^2 := by
  have he : q-1+1=q := by omega
  nlinarith

theorem projected_orders_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (a : (ZMod p)ˣ) (b : (ZMod q)ˣ) :
    (orderOf (a^(p*q - 1))).Coprime (orderOf (b^(p*q - 1))) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let g := (p - 1).gcd (q - 1)
  have hgE : g ∣ p*q - 1 := by
    dsimp [g]
    rw [← gcd_sub_one_mul hp.pos hq.pos]
    exact Nat.gcd_dvd_right _ _
  have ha := order_pow_dvd_quotient a (ZMod.orderOf_units_dvd_card_sub_one a)
    (Nat.gcd_dvd_left (p - 1) (q - 1)) hgE
  have hb := order_pow_dvd_quotient b (ZMod.orderOf_units_dvd_card_sub_one b)
    (Nat.gcd_dvd_right (p - 1) (q - 1)) hgE
  have hpp := hp.one_lt
  have hg : 0 < g := Nat.gcd_pos_of_pos_left (q - 1) (by omega)
  exact (Nat.coprime_div_gcd_div_gcd hg).of_dvd ha hb

theorem further_projection_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (a : (ZMod p)ˣ) (b : (ZMod q)ˣ) (M : ℕ) :
    (orderOf ((a^(p*q - 1))^M)).Coprime (orderOf ((b^(p*q - 1))^M)) :=
  (projected_orders_coprime hp hq a b).of_dvd (orderOf_pow_dvd M) (orderOf_pow_dvd M)

theorem shared_projected_order_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (a : (ZMod p)ˣ) (b : (ZMod q)ˣ) (M : ℕ)
    (he : orderOf ((a^(p*q - 1))^M) = orderOf ((b^(p*q - 1))^M)) :
    orderOf ((a^(p*q - 1))^M) = 1 := by
  have h := further_projection_coprime hp hq a b M
  rw [← he, Nat.coprime_self] at h
  exact h

/-- Once common local periods are removed, closing one nontrivial period
cannot also close the other. This is the exact separating collision. -/
theorem separating_power {G H : Type*} [Group G] [Group H] (a : G) (b : H)
    (hc : (orderOf a).Coprime (orderOf b)) (hb : orderOf b ≠ 1) :
    a^(orderOf a) = 1 ∧ b^(orderOf a) ≠ 1 := by
  refine ⟨pow_orderOf_eq_one a, ?_⟩
  intro he
  have hdiv : orderOf b ∣ orderOf a := orderOf_dvd_of_pow_eq_one he
  have hg : orderOf b ∣ (orderOf a).gcd (orderOf b) := Nat.dvd_gcd hdiv (dvd_refl _)
  rw [hc.gcd_eq_one] at hg
  exact hb (Nat.dvd_one.mp hg)

/-- A bounded local period supplies a literal bounded separating witness;
no factor or local order is required by the search to enumerate its cover. -/
theorem bounded_separating_witness {G H : Type*} [Group G] [Group H]
    (a : G) (b : H) {D : ℕ} (hc : (orderOf a).Coprime (orderOf b))
    (ha : 0 < orderOf a) (hD : orderOf a ≤ D) (hb : orderOf b ≠ 1) :
    ∃ d : ℕ, 0 < d ∧ d ≤ D ∧ a^d = 1 ∧ b^d ≠ 1 :=
  ⟨orderOf a, ha, hD, (separating_power a b hc hb).1,
    (separating_power a b hc hb).2⟩

theorem gcd_semiprime_of_separating_residue {p q x : ℕ} (hq : q.Prime)
    (hp : p ∣ x) (hnq : ¬q ∣ x) : (p*q).gcd x=p := by
  rw [Nat.mul_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd (hq.coprime_iff_not_dvd.mpr hnq) hp

theorem choose_dvd_of_coprime {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hc : N.Coprime k) : N ∣ N.choose k := by
  have he := Nat.add_one_mul_choose_eq (N - 1) (k - 1)
  have hNs : N - 1 + 1 = N := by omega
  have hks : k - 1 + 1 = k := by omega
  rw [hNs, hks] at he
  apply hc.dvd_of_dvd_mul_right
  rw [← he]
  exact dvd_mul_right N _

theorem low_choose_dvd_semiprime {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : 0 < k) (hkp : k < p) (hkq : k < q) :
    p*q ∣ (p*q).choose k := by
  have hpk : p.Coprime k := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact (not_le_of_gt hkp) (Nat.le_of_dvd hk h))
  have hqk : q.Coprime k := hq.coprime_iff_not_dvd.mpr (by
    intro h
    exact (not_le_of_gt hkq) (Nat.le_of_dvd hk h))
  exact choose_dvd_of_coprime (Nat.mul_pos hp.pos hq.pos) hk (hpk.mul_left hqk)

/-- The geometric polynomial's blocks cover every positive candidate order.
The representation is literal, with no order or factor oracle. -/
theorem geometric_order_cover {b J d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hD : d ≤ b*J) :
    ∃ j i : ℕ, 1 ≤ j ∧ j ≤ J ∧ i < b ∧ d + i = b*j := by
  generalize hq : (d - 1)/b = q
  generalize hr : (d - 1)%b = r
  have hrb : r < b := by rw [← hr]; exact Nat.mod_lt _ hb
  have he : r + b*q = d - 1 := by
    rw [← hr, ← hq]
    exact Nat.mod_add_div (d - 1) b
  have hj : q < J := by
    rw [← hq]
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    simpa [Nat.mul_comm] using (show d - 1 < b*J by omega)
  have hi : (b - r - 1) + r + 1 = b := by omega
  have hd' : d - 1 + 1 = d := by omega
  refine ⟨q + 1, b - r - 1, by omega, by omega, by omega, ?_⟩
  nlinarith

/-- Factor the known unit phase out of one collision difference. Signed
exponents avoid any assumption about which hidden local order is used. -/
theorem squared_collision_phase {R : Type*} [CommRing R] (beta : Rˣ) (e i : ℤ) :
    (↑(beta^(2*e)) : R)-↑(beta^(2*i)) =
      ↑(beta^(e+i))*(↑(beta^(e-i))-↑(beta^(i-e))) := by
  have h1 : (beta^(e+i))*(beta^(e-i))=beta^(2*e) := by
    rw [← zpow_add]; congr 1; ring
  have h2 : (beta^(e+i))*(beta^(i-e))=beta^(2*i) := by
    rw [← zpow_add]; congr 1; ring
  rw [mul_sub,← Units.val_mul,← Units.val_mul,h1,h2]

theorem inverse_difference_anti_selfadjoint {R : Type*} [CommRing R] [StarRing R]
    (beta : Rˣ) (hb : star beta=beta⁻¹) (e : ℤ) :
    star ((↑(beta^e) : R)-↑(beta^(-e))) =
      -((↑(beta^e) : R)-↑(beta^(-e))) := by
  have hs (n : ℤ) : star (↑(beta^n) : R) = ↑(beta^(-n)) := by
    rw [← Units.coe_star,star_zpow,hb]
    simp only [inv_zpow,zpow_neg]
  rw [star_sub,hs,hs]
  simp only [neg_neg]
  ring

/-- An even product of anti-selfadjoint collision factors is real after
one exact known phase is removed. This is algebraic, without a norm or a
floating-point optimizer, and applies over the composite base ring. -/
theorem even_collision_product_selfadjoint {R I : Type*}
    [CommRing R] [StarRing R] (S : Finset I) (f : I → R)
    (he : Even S.card) (hf : ∀ i ∈ S,star (f i)= -(f i)) :
    star (∏ i ∈ S,f i)=∏ i ∈ S,f i := by
  rw [star_prod]
  calc
    ∏ i ∈ S,star (f i) = ∏ i ∈ S,(-1 : R)*f i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hf i hi]
      ring
    _ = (-1 : R)^S.card*(∏ i ∈ S,f i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const]
    _ = _ := by rw [he.neg_one_pow,one_mul]

theorem product_collision_phase {R I : Type*} [CommRing R]
    (S : Finset I) (beta : Rˣ) (e : ℤ) (f : I → ℤ) :
    (∏ i ∈ S,((↑(beta^(2*e)) : R)-↑(beta^(2*f i)))) =
      (∏ i ∈ S,(↑(beta^(e+f i)) : R))*
        (∏ i ∈ S,((↑(beta^(e-f i)) : R)-↑(beta^(f i-e)))) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => squared_collision_phase beta e (f i))

/-- The coordinate discarded by the tilted evaluator is exactly zero
over any field of characteristic other than two, after phase removal. -/
theorem quadratic_selfadjoint_im_zero {F : Type*} [Field F]
    (D : F) (z : QuadraticAlgebra F D 0) (h2 : (2 : F) ≠ 0)
    (hz : star z=z) : z.im=0 := by
  have hi := congrArg QuadraticAlgebra.im hz
  simp only [QuadraticAlgebra.im_star] at hi
  have he : (2 : F)*z.im=0 := by linear_combination -hi
  exact (mul_eq_zero.mp he).resolve_left h2

/-- Recover the tilted scalar from just one convolution coordinate.
A nonunit phase coordinate is handled by a gcd in the implementation. -/
theorem quadratic_phase_recover {F : Type*} [Field F] (D : F)
    (phase : QuadraticAlgebra F D 0) (scalar : F) (hp : phase.re ≠ 0) :
    (phase * QuadraticAlgebra.C scalar).re / phase.re=scalar := by
  simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.re_C,QuadraticAlgebra.im_C,
    mul_zero,add_zero]
  rw [mul_comm]
  exact mul_div_cancel_right₀ scalar hp

theorem quadratic_norm_one_re_one {F : Type*} [Field F] {D : F}
    (x : QuadraticAlgebra F D 0) (hD : D ≠ 0)
    (hn : QuadraticAlgebra.norm x=1) (hr : x.re=1) : x=1 := by
  have hy : x.im*x.im=0 := by
    have hh : D*(x.im*x.im)=0 := by
      simpa [QuadraticAlgebra.norm_def,hr] using hn
    exact (mul_eq_zero.mp hh).resolve_left hD
  have hi : x.im=0 := (mul_eq_zero.mp hy).elim id id
  ext <;> simp [hr,hi,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

/-- Norms detect a collision of norm-one elements even when the quadratic
algebra is split: zero norm of an arbitrary element would not suffice. -/
theorem quadratic_norm_one_collision {F : Type*} [Field F] {D : F}
    (x y : QuadraticAlgebra F D 0) (hD : D ≠ 0) (h2 : (2 : F) ≠ 0)
    (hx : QuadraticAlgebra.norm x=1) (hy : QuadraticAlgebra.norm y=1) :
    QuadraticAlgebra.norm (x-y)=0 ↔ x=y := by
  constructor
  · intro hz
    have he : (2 : F)*(1-(x*star y).re)=0 := by
      simp only [QuadraticAlgebra.norm_def,QuadraticAlgebra.re_sub,
        QuadraticAlgebra.im_sub,QuadraticAlgebra.re_mul,QuadraticAlgebra.re_star,
        QuadraticAlgebra.im_star,zero_mul,add_zero] at hx hy hz ⊢
      linear_combination hz-hx-hy
    have hr : (x*star y).re=1 := by
      have hh := (mul_eq_zero.mp he).resolve_left h2
      linear_combination -hh
    have hn : QuadraticAlgebra.norm (x*star y)=1 := by
      rw [map_mul,QuadraticAlgebra.norm_star,hx,hy,mul_one]
    have hxy := quadratic_norm_one_re_one (x*star y) hD hn hr
    have hyy : star y*y=1 := by
      rw [mul_comm,← QuadraticAlgebra.algebraMap_norm_eq_mul_star,hy,map_one]
    have hh := congrArg (fun z => z*y) hxy
    simpa only [mul_assoc,hyy,mul_one,one_mul] using hh
  · intro h
    rw [h,sub_self,QuadraticAlgebra.norm_zero]

/-- A finite obstruction to coverage by the tested N^(1/6)-budget order
cover: all four local p±1 cardinalities have a prime rough factor >400.
It is not a lower bound for arbitrary factoring algorithms. -/
theorem four_rough_period_control :
    Nat.Prime 6827 ∧ Nat.Prime 7187 ∧
    Nat.Prime 3413 ∧ Nat.Prime 3593 ∧ Nat.Prime 569 ∧ Nat.Prime 599 ∧
    6827*7187=49065649 ∧
    19^6 < (49065649 : ℕ) ∧ 49065649 ≤ (20 : ℕ)^6 ∧
    (6827 : ℕ)-1=2*3413 ∧ (7187 : ℕ)-1=2*3593 ∧
    (6827 : ℕ)+1=12*569 ∧ (7187 : ℕ)+1=12*599 ∧
    400 < (569 : ℕ) ∧ 400 < (599 : ℕ) := by
  norm_num

end RiemannGaussian.SemiprimeOrderSeparation
