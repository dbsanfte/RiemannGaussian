/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeKnownBitsBudget
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.NormNum.NatSqrt

/-!
# Euclidean construction after removing the trivial linear row

The rank-three lattice lead of Gao--Feng--Hu--Pan retains a nontrivial
quadratic rather than its trivial linear direction. Here a public modular
relation in two integer coordinates constructs such quadratics by Euclidean
division. The original polynomial, its factor-sum identity and both signed
collision orientations remain available. No LLL or short-vector oracle is
assumed. This construction does not establish the requested one-sixth
factorisation bound or a complete bit-machine refinement.
-/

namespace RiemannGaussian.SemiprimeQuotientRows

/-- A sign bit changes the orientation without erasing the coordinate. -/
def signed (negative : Bool) (x : ℕ) : ℤ := if negative then -(x : ℤ) else x

/-- Flipping the sign retains its exact additive inverse. -/
theorem signed_not (negative : Bool) (x : ℕ) : signed (!negative) x = -signed negative x := by
  cases negative <;> simp [signed]

/-- Signed Euclidean updates keep the full quotient contribution. -/
theorem signed_update (negative : Bool) (x y q : ℕ) :
    signed (!negative) (x+q*y) = -signed negative x-(q : ℤ)*signed negative y := by
  cases negative <;> simp [signed]
  ring

/-- The sign bit has no effect on the coordinate's magnitude. -/
theorem signed_natAbs (negative : Bool) (x : ℕ) : (signed negative x).natAbs=x := by
  cases negative <;> simp [signed]

/-- Euclidean output retains its unsigned remainder, denominator and sign,
and charges every actual division step. -/
structure EuclidResult where
  /-- The last remainder, before applying its retained sign. -/
  remainder : ℕ
  /-- The positive coefficient of the original modular input. -/
  denominator : ℕ
  /-- Its collision orientation. -/
  negative : Bool
  /-- Actual quotient/remainder iterations; not a bit-operation count. -/
  divisions : ℕ
deriving Repr

/-- Stop at the public remainder threshold; every recursive step uses the
literal quotient and remainder, without inspecting either hidden factor. -/
def euclidShort (S r₀ r₁ x y : ℕ) (negative : Bool) : EuclidResult :=
  if r₁≤S then ⟨r₁,y,negative,0⟩ else
    let tail := euclidShort S r₁ (r₀%r₁) y (x+r₀/r₁*y) (!negative)
    { tail with divisions := tail.divisions+1 }
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- The determinant identity survives each concrete Euclidean division. -/
theorem euclid_determinant_step (r₀ r₁ x y : ℕ) :
    r₀*y+r₁*x=r₁*(x+r₀/r₁*y)+(r₀%r₁)*y := by
  have h := Nat.mod_add_div r₀ r₁
  nlinarith

/-- Exact congruences survive the same division and sign flip. -/
theorem euclid_congruence_step {m u r₀ r₁ x y : ℕ} {negative : Bool}
    (h₀ : (r₀ : ℤ) ≡ -(u : ℤ)*signed negative x [ZMOD m])
    (h₁ : (r₁ : ℤ) ≡ (u : ℤ)*signed negative y [ZMOD m]) :
    (r₁ : ℤ) ≡ -(u : ℤ)*signed (!negative) y [ZMOD m] ∧
      ((r₀%r₁ : ℕ) : ℤ) ≡ (u : ℤ)*signed (!negative) (x+r₀/r₁*y) [ZMOD m] := by
  constructor
  · rw [signed_not]
    convert h₁ using 1; ring
  · have he : ((r₀%r₁ : ℕ) : ℤ)=(r₀ : ℤ)-(r₀/r₁ : ℕ)*r₁ := by
      have hd : ((r₀%r₁ : ℕ) : ℤ)+(r₁ : ℤ)*(r₀/r₁ : ℕ)=r₀ := by
        exact_mod_cast Nat.mod_add_div r₀ r₁
      nlinarith
    rw [he,signed_update]
    convert h₀.sub (h₁.mul_left (r₀/r₁ : ℕ)) using 1; ring

/-- The executable construction returns a bounded remainder, a positive
denominator, and both original congruences' retained orientation. -/
theorem euclidShort_correct {m u S r₀ r₁ x y : ℕ} {negative : Bool}
    (horder : r₁<r₀) (hprev : S<r₀) (hy : 0<y)
    (hdet : m=r₀*y+r₁*x)
    (h₀ : (r₀ : ℤ) ≡ -(u : ℤ)*signed negative x [ZMOD m])
    (h₁ : (r₁ : ℤ) ≡ (u : ℤ)*signed negative y [ZMOD m]) :
    let z := euclidShort S r₀ r₁ x y negative
    z.remainder≤S ∧ 0<z.denominator ∧ (S+1)*z.denominator≤m ∧
      (z.remainder : ℤ) ≡ (u : ℤ)*signed z.negative z.denominator [ZMOD m] := by
  rw [euclidShort]
  split_ifs with hstop
  · dsimp only
    have hd : (S+1)*y≤m := by nlinarith
    exact ⟨hstop,hy,hd,h₁⟩
  · have hr : 0<r₁ := by omega
    have hq : 0<r₀/r₁ := Nat.div_pos horder.le hr
    have hm : m=r₁*(x+r₀/r₁*y)+(r₀%r₁)*y := by rw [hdet,euclid_determinant_step]
    have hc := euclid_congruence_step h₀ h₁
    exact euclidShort_correct (Nat.mod_lt _ hr) (by omega) (by positivity) hm hc.1 hc.2
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- Two successive Euclidean remainders shrink by at least a factor of
two. This counts actual division iterations, not real-valued norms. -/
theorem two_remainders_half {a b : ℕ} (hb : 0<b) (hrp : 0<a%b) :
    2*(b%(a%b))<b := by
  let r := a%b
  have hr : r<b := Nat.mod_lt a hb
  have hs : b%r<r := Nat.mod_lt b hrp
  by_cases hsmall : 2*r≤b
  · change 2*(b%r)<b
    omega
  · have hdiv : b/r=1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · simpa using hsmall
    have he := Nat.mod_add_div b r
    rw [hdiv] at he
    change 2*(b%r)<b
    omega

/-- An explicit power-of-two envelope bounds every execution by twice its
input bit length, even when no factor-specific information is available. -/
theorem euclidShort_divisions_pow (k S r₀ r₁ x y : ℕ) (negative : Bool)
    (hsize : r₁<2^k) : (euclidShort S r₀ r₁ x y negative).divisions≤2*k := by
  induction k generalizing r₀ r₁ x y negative with
  | zero =>
    have hr : r₁=0 := by simpa using hsize
    simp [hr,euclidShort]
  | succ k ih =>
    by_cases hstop : r₁≤S
    · simp [euclidShort,hstop]
    · by_cases hnext : r₀%r₁≤S
      · simp [euclidShort,hstop,hnext]
        omega
      · have hhalf := two_remainders_half (a:=r₀) (b:=r₁) (by omega) (by omega)
        have hsmall : r₁%(r₀%r₁)<2^k := by
          rw [pow_succ] at hsize
          omega
        have ht := ih (r₀%r₁) (r₁%(r₀%r₁)) (x+r₀/r₁*y)
          (y+r₁/(r₀%r₁)*(x+r₀/r₁*y)) (!(!negative)) hsmall
        rw [euclidShort,if_neg hstop,euclidShort,if_neg hnext]
        dsimp only
        omega

/-- The public bit-length envelope counts actual Euclidean divisions;
integer multiplication, division implementation and modular power costs
still require the separate bit backend. -/
theorem euclidShort_divisions_bound (S r₀ r₁ x y : ℕ) (negative : Bool) :
    (euclidShort S r₀ r₁ x y negative).divisions≤2*(r₁.log2+1) := by
  apply euclidShort_divisions_pow
  simpa only [Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by decide : 1<2) r₁

/-- The returned signed remainder and positive denominator form the
nontrivial modular relation used in the quotient lattice. -/
def shortPair (m u S : ℕ) : ℤ×ℕ :=
  let z := euclidShort S m (u%m) 0 1 false
  (signed z.negative z.remainder,z.denominator)

/-- Universal public short-relation guarantee for the exact executable
constructor; there is no supplied short-vector hypothesis. -/
theorem shortPair_correct {m u S : ℕ} (hS : 0<S) (hSm : S<m)
    (hcop : m.Coprime u) :
    let z := shortPair m u S
    z.1≠0 ∧ z.1.natAbs≤S ∧ 0<z.2 ∧ (S+1)*z.2≤m ∧
      z.1 ≡ (u : ℤ)*z.2 [ZMOD m] := by
  let out := euclidShort S m (u%m) 0 1 false
  have hc := euclidShort_correct (m:=m) (u:=u) (S:=S) (r₀:=m) (r₁:=u%m)
    (x:=0) (y:=1) (negative:=false) (Nat.mod_lt _ (by omega)) hSm (by decide)
    (by simp) (by simp [signed,Int.ModEq])
    (by simpa [signed] using Int.mod_modEq (u : ℤ) m)
  change out.remainder≤S ∧ 0<out.denominator ∧ (S+1)*out.denominator≤m ∧
    (out.remainder : ℤ) ≡ (u : ℤ)*signed out.negative out.denominator [ZMOD m] at hc
  have hrel : signed out.negative out.remainder ≡ (u : ℤ)*out.denominator [ZMOD m] := by
    cases hn : out.negative with
    | false => simpa [hn,signed] using hc.2.2.2
    | true => simpa [hn,signed] using hc.2.2.2.neg
  have hn : signed out.negative out.remainder≠0 := by
    intro hz
    have hdI : (m : ℤ)∣(u : ℤ)*out.denominator := by
      have hd := hrel.dvd
      rw [hz,sub_zero] at hd
      exact hd
    have hd : m∣u*out.denominator := by exact_mod_cast hdI
    have hdy := hcop.dvd_of_dvd_mul_left hd
    have hle : m≤out.denominator := Nat.le_of_dvd hc.2.1 hdy
    nlinarith [hc.2.2.1]
  change signed out.negative out.remainder≠0 ∧
    (signed out.negative out.remainder).natAbs≤S ∧ 0<out.denominator ∧
      (S+1)*out.denominator≤m ∧
        signed out.negative out.remainder ≡ (u : ℤ)*out.denominator [ZMOD m]
  rw [signed_natAbs]
  exact ⟨hn,hc.1,hc.2.1,hc.2.2.1,hrel⟩

/-- Center a public residue while keeping its modular class. -/
def centered (m : ℕ) (v : ℤ) : ℤ := (v+(m/2 : ℕ))%(m : ℤ)-(m/2 : ℕ)

/-- Centering is an exact modular identity, not a real approximation. -/
theorem centered_modEq (m : ℕ) (v : ℤ) : centered m v ≡ v [ZMOD m] := by
  have h := (Int.mod_modEq (v+(m/2 : ℕ)) m).sub (Int.ModEq.refl (m/2 : ℕ))
  simpa only [centered,add_sub_cancel_right] using h

/-- The centered linear coefficient has an explicit public magnitude bound. -/
theorem centered_natAbs_le {m : ℕ} (hm : 0<m) (v : ℤ) :
    (centered m v).natAbs≤m/2+1 := by
  have hpos : (0 : ℤ)<m := by exact_mod_cast hm
  have hr₀ := Int.emod_nonneg (v+(m/2 : ℕ)) (ne_of_gt hpos)
  have hr₁ := Int.emod_lt_of_pos (v+(m/2 : ℕ)) hpos
  have he := Nat.mod_add_div m 2
  have hh := Nat.mod_lt m (by decide : 0<2)
  have hb : -(m/2+1 : ℕ)≤centered m v ∧ centered m v≤(m/2+1 : ℕ) := by
    unfold centered
    omega
  have ha := abs_le.mpr hb
  rw [←Int.natCast_natAbs] at ha
  exact_mod_cast ha

/-- Actual integer row data and its Euclidean iteration count. -/
structure QuotientRow where
  /-- Nonzero quadratic coefficient. -/
  a : ℤ
  /-- Centered linear coefficient. -/
  b : ℤ
  /-- Integer constant coefficient. -/
  c : ℤ
  /-- Positive quotient-lattice denominator. -/
  t : ℤ
  /-- Actual Euclidean quotient/remainder steps. -/
  divisions : ℕ
deriving Repr

/-- Lift a public short pair into the original quadratic using exact
integer divisions and a centered modular inverse. -/
def liftRow (N : ℤ) (m j : ℕ) (inverse a t : ℤ) : QuotientRow :=
  let D := (N*t-(j : ℤ)^2*a)/(m : ℤ)
  let b := centered m (-inverse*D)
  ⟨a,b,(D+(j : ℤ)*b)/(m : ℤ),t,0⟩

/-- The integer quadratic is kept before any modular or scalar collapse. -/
def quadratic (a b c x : ℤ) : ℤ := a*x^2+b*x+c

/-- Membership in the quotient construction has one exact divisibility
constraint after eliminating the trivial linear row. -/
def quotientRelation (N m j a b c t : ℤ) : Prop :=
  m^2*c-j*m*b+j^2*a=N*t

/-- Lifting a short quotient pair uses two exact divisions. The public
linear coefficient can be centered without modifying its modular class. -/
theorem lift_quotient_relation {N m j a t b D c : ℤ}
    (hD : N*t-j^2*a=m*D) (hc : D+j*b=m*c) :
    quotientRelation N m j a b c t := by
  unfold quotientRelation
  linear_combination -hD-m*hc

/-- The executable lift satisfies the full quotient relation whenever
the public inverse and public short pair pass their exact congruences. -/
theorem liftRow_correct {N : ℤ} {m j : ℕ} {inverse a t : ℤ}
    (hinv : (j : ℤ)*inverse ≡ 1 [ZMOD m])
    (hpair : a ≡ N*inverse^2*t [ZMOD m]) :
    let z := liftRow N m j inverse a t
    quotientRelation N m j z.a z.b z.c z.t := by
  let D := (N*t-(j : ℤ)^2*a)/(m : ℤ)
  let b := centered m (-inverse*D)
  have hpow := (hinv.pow 2).mul_left (N*t)
  have hcross : (j : ℤ)^2*(N*inverse^2*t) ≡ N*t [ZMOD m] := by
    convert hpow using 1 <;> ring
  have hdiv : (m : ℤ)∣N*t-(j : ℤ)^2*a :=
    ((hpair.mul_left ((j : ℤ)^2)).trans hcross).dvd
  have hD : N*t-(j : ℤ)^2*a=(m : ℤ)*D := by
    dsimp only [D]
    rw [mul_comm (m : ℤ),Int.ediv_mul_cancel hdiv]
  have hb := (centered_modEq m (-inverse*D)).mul_left (j : ℤ)
  have hprod := hinv.mul_right (-D)
  have hlinear : (j : ℤ)*b ≡ -D [ZMOD m] := by
    apply hb.trans
    convert hprod using 1 <;> ring
  have hcdiv : (m : ℤ)∣D+(j : ℤ)*b := by
    apply Int.modEq_zero_iff_dvd.mp
    simpa only [add_neg_cancel] using (Int.ModEq.refl D).add hlinear
  have hC : D+(j : ℤ)*b=(m : ℤ)*((D+(j : ℤ)*b)/(m : ℤ)) := by
    rw [mul_comm (m : ℤ),Int.ediv_mul_cancel hcdiv]
  exact lift_quotient_relation hD hC

/-- Public Bezout inverse; computing it is part of the constructor. -/
def publicInverse (m j : ℕ) : ℤ := Int.gcdA (j : ℤ) (m : ℤ)

/-- The literal inverse has its exact public modular identity. -/
theorem publicInverse_correct {m j : ℕ} (hcop : j.Coprime m) :
    (j : ℤ)*publicInverse m j ≡ 1 [ZMOD m] := by
  have h := Int.gcd_eq_gcd_ab (j : ℤ) (m : ℤ)
  rw [Int.gcd_natCast_natCast,hcop, Nat.cast_one] at h
  apply Int.modEq_iff_dvd.mpr
  refine ⟨Int.gcdB (j : ℤ) (m : ℤ),?_⟩
  unfold publicInverse
  nlinarith only [h]

/-- The same Bezout data proves the inverse's coprimality, without a
second oracle or an unknown prime-component inverse. -/
theorem publicInverse_coprime {m j : ℕ} (hcop : j.Coprime m) :
    IsCoprime (m : ℤ) (publicInverse m j) := by
  have h := Int.gcd_eq_gcd_ab (j : ℤ) (m : ℤ)
  rw [Int.gcd_natCast_natCast,hcop,Nat.cast_one] at h
  refine ⟨Int.gcdB (j : ℤ) (m : ℤ),(j : ℤ),?_⟩
  unfold publicInverse
  nlinarith only [h]

/-- Public quotient-lattice slope. Its reduction uses the input N only. -/
def quotientSlope (N m j : ℕ) : ℕ :=
  (((N : ℤ)*(publicInverse m j)^2)%(m : ℤ)).toNat

/-- The slope's canonical representative retains the original inverse product. -/
theorem quotientSlope_modEq {N m j : ℕ} (hm : 0<m) :
    (quotientSlope N m j : ℤ) ≡ (N : ℤ)*(publicInverse m j)^2 [ZMOD m] := by
  unfold quotientSlope
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast ne_of_gt hm))]
  exact Int.mod_modEq _ _

/-- Coprimality needed by the short-relation constructor is discharged
from the public prefix/inverse checks, rather than assumed of a hidden row. -/
theorem quotientSlope_coprime {N m j : ℕ} (hm : 0<m)
    (hN : m.Coprime N) (hj : j.Coprime m) : m.Coprime (quotientSlope N m j) := by
  let w := (N : ℤ)*(publicInverse m j)^2
  have hc : IsCoprime (m : ℤ) w :=
    hN.isCoprime.mul_right (publicInverse_coprime hj).pow_right
  have he : w%(m : ℤ)+(m : ℤ)*(w/(m : ℤ))=w := Int.emod_add_mul_ediv _ _
  have hr : IsCoprime (m : ℤ) (w%(m : ℤ)) := by
    apply IsCoprime.of_add_mul_left_right
    rw [he]
    exact hc
  apply Nat.isCoprime_iff_coprime.mp
  unfold quotientSlope
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast ne_of_gt hm))]
  exact hr

/-- One public residue produces a concrete informative quadratic row;
the original three-dimensional lattice matrix is never constructed. -/
def publicRow (N m j : ℕ) : QuotientRow :=
  let u := quotientSlope N m j
  let z := euclidShort m.sqrt m (u%m) 0 1 false
  let row := liftRow N m j (publicInverse m j) (signed z.negative z.remainder) z.denominator
  { row with divisions := z.divisions }

/-- Universal guarantees of the public row constructor. Both quotient
coordinates have square-root scale, and all Euclidean divisions are counted. -/
theorem publicRow_correct {N m j : ℕ} (hm : 1<m)
    (hN : m.Coprime N) (hj : j.Coprime m) :
    let z := publicRow N m j
    z.a≠0 ∧ z.a.natAbs≤m.sqrt ∧ 0<z.t ∧ z.t≤m.sqrt ∧
      z.b.natAbs≤m/2+1 ∧ quotientRelation N m j z.a z.b z.c z.t ∧
      z.divisions≤2*(m.log2+1) := by
  have hpos : 0<m := by omega
  have hS : 0<m.sqrt := Nat.sqrt_pos.mpr hpos
  have hSm : m.sqrt<m := Nat.sqrt_lt_self hm
  have hp := shortPair_correct hS hSm (quotientSlope_coprime hpos hN hj)
  let u := quotientSlope N m j
  let out := euclidShort m.sqrt m (u%m) 0 1 false
  change signed out.negative out.remainder≠0 ∧
    (signed out.negative out.remainder).natAbs≤m.sqrt ∧ 0<out.denominator ∧
      (m.sqrt+1)*out.denominator≤m ∧
        signed out.negative out.remainder ≡ (u : ℤ)*out.denominator [ZMOD m] at hp
  have hden : out.denominator≤m.sqrt := by
    have hs := Nat.lt_succ_sqrt' m
    nlinarith [hp.2.2.2.1]
  have hpair := hp.2.2.2.2.trans ((quotientSlope_modEq (N:=N) (j:=j) hpos).mul_right
    (out.denominator : ℤ))
  have hrow := liftRow_correct (publicInverse_correct hj) hpair
  have hcount : out.divisions≤2*(m.log2+1) := by
    apply euclidShort_divisions_pow
    exact (Nat.mod_lt _ hpos).trans (by
      simpa only [Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by decide : 1<2) m)
  change (signed out.negative out.remainder)≠0 ∧
    (signed out.negative out.remainder).natAbs≤m.sqrt ∧
      (0 : ℤ)<out.denominator ∧ (out.denominator : ℤ)≤m.sqrt ∧
        (centered m _).natAbs≤m/2+1 ∧ _ ∧ out.divisions≤2*(m.log2+1)
  exact ⟨hp.1,hp.2.1,by exact_mod_cast hp.2.2.1,by exact_mod_cast hden,
    centered_natAbs_le hpos _,hrow,hcount⟩

/-- Adding the trivial direction preserves the quotient class but retains
its full change in the integer polynomial. -/
theorem quotientRelation_shift {N m j a b c t : ℤ}
    (h : quotientRelation N m j a b c t) (k : ℤ) :
    quotientRelation N m j a (b+k*m) (c+k*j) t := by
  unfold quotientRelation at h ⊢
  nlinarith

/-- The public quadratic becomes a weighted factor sum after evaluating
the correct residue row; the hidden factors occur only in this proof. -/
theorem scaled_quadratic_factor_sum {p q m j a b c t x : ℤ}
    (hp : p=m*x+j) (h : quotientRelation (p*q) m j a b c t) :
    m^2*quadratic a b c x=p*(a*p+b*m-2*a*j+t*q) := by
  unfold quotientRelation at h
  unfold quadratic
  rw [hp] at h ⊢
  nlinarith only [h]

/-- A quotient row has an integer index in its correct prime component,
without assuming an unknown lattice vector or a modular collision oracle. -/
theorem quotient_row_integer_index {p q m j a b c t x : ℤ}
    (hp : p=m*x+j) (h : quotientRelation (p*q) m j a b c t)
    (hcop : IsCoprime p m) : ∃ i : ℤ, quadratic a b c x=p*i := by
  have hscaled := scaled_quadratic_factor_sum hp h
  have hd : p∣m^2*quadratic a b c x := by
    rw [hscaled]
    exact dvd_mul_right _ _
  have hdq := (hcop.pow_right (n:=2)).dvd_of_dvd_mul_left hd
  obtain ⟨i,hi⟩ := hdq
  exact ⟨i,hi⟩

/-- An exact public coefficient bound also bounds the retained collision
index; cancellation in the factor sum is kept before this upper estimate. -/
theorem factor_sum_index_bound {p q m j a b t i S T : ℤ}
    (hp : 0≤p) (hq : 0≤q) (hm : 0≤m) (hj₀ : 0≤j) (hjm : j≤m)
    (ha : |a|≤S) (hb : |b|≤T) (ht : |t|≤S)
    (he : m^2*i=a*p+b*m-2*a*j+t*q) :
    |i| *m^2≤S*(p+q+2*m)+T*m := by
  have hnorm : |a*p+b*m-2*a*j+t*q|≤
      |a| *(p+2*j)+|b| *m+|t| *q := by
    calc
      _≤|a*p+b*m-2*a*j|+|t*q| := abs_add_le _ _
      _≤(|a*p+b*m|+|2*a*j|)+|t*q| := by
        have h : |a*p+b*m-2*a*j|≤|a*p+b*m|+|2*a*j| := by
          simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (a*p+b*m) (-(2*a*j))
        linarith
      _≤((|a*p|+|b*m|)+|2*a*j|)+|t*q| := by
        have h := abs_add_le (a*p) (b*m)
        linarith
      _=|a| *(p+2*j)+|b| *m+|t| *q := by
        simp only [abs_mul,abs_of_nonneg hp,abs_of_nonneg hq,abs_of_nonneg hm,
          abs_of_nonneg hj₀,abs_of_nonneg (by decide : (0 : ℤ)≤2)]
        ring
  have hSa := mul_le_mul_of_nonneg_right ha (show 0≤p+2*j by omega)
  have hTb := mul_le_mul_of_nonneg_right hb hm
  have hSt := mul_le_mul_of_nonneg_right ht hq
  have hS : 0≤S := (abs_nonneg a).trans ha
  have hSj := mul_le_mul_of_nonneg_left hjm hS
  rw [←he,abs_mul,abs_of_nonneg (sq_nonneg m)] at hnorm
  nlinarith only [hnorm,hSa,hTb,hSt,hSj]

/-- Complete positive baby-axis length under the explicit balanced-factor
promise p≤q≤2p. A negative index uses the inverse giant-step orientation. -/
def indexLength (N m : ℕ) : ℕ :=
  (m.sqrt*(3*(N.sqrt+1)+2*m)+(m/2+1)*m)/m^2+1

/-- A square modulus at fifth-root scale has a linear explicit search
budget. This is a bound on row/point inputs, not on total bit operations. -/
theorem indexLength_fifth_budget {N M : ℕ} (hM : 0<M) (hN : N≤M^10) :
    indexLength N (M^2)≤10*M^2+1 := by
  have hroot : N.sqrt≤M^5 := by
    have h : N≤(M^5)^2 := by simpa only [←pow_mul] using hN
    simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt h
  have hM5 : 0<M^5 := pow_pos hM 5
  have hheight : N.sqrt+1≤2*M^5 := by omega
  have haxis := Nat.mul_le_mul_left M (Nat.add_le_add_right
    (Nat.mul_le_mul_left 3 hheight) (2*M^2))
  have hM3 : M^3≤M^6 := Nat.pow_le_pow_right hM (by decide)
  have hM4 : M^4≤M^6 := Nat.pow_le_pow_right hM (by decide)
  have hm2 : 0<M^2 := pow_pos hM 2
  have hhalf : M^2/2+1≤2*M^2 := by
    have h := Nat.div_le_self (M^2) 2
    omega
  have htail := Nat.mul_le_mul_right (M^2) hhalf
  have hbudget : M*(3*(N.sqrt+1)+2*M^2)+(M^2/2+1)*M^2≤10*M^6 := by
    nlinarith only [haxis,htail,hM3,hM4]
  have hden : 0<(M^2)^2 := pow_pos hm2 2
  have hdiv := Nat.div_le_div_right (c:=(M^2)^2) hbudget
  have he : 10*M^6=(10*M^2)*(M^2)^2 := by ring
  rw [he,Nat.mul_div_cancel _ hden] at hdiv
  unfold indexLength
  rw [Nat.sqrt_eq']
  omega

/-- Both signed giant-step orientations fit the same fifth-root input
budget without constructing any baby/giant pair grid. -/
theorem fifth_layout_budget {N M : ℕ} (hM : 0<M) (hN : N≤M^10) :
    2*M^2+indexLength N (M^2)≤12*M^2+1 := by
  have h := indexLength_fifth_budget hM hN
  omega

/-- Public giant-step exponent for the retained quadratic. -/
def giantExponent (m j a b c : ℤ) : ℤ :=
  c*m^2+b*m*(1-j)+a*(1-j)^2

/-- Its factor-sum form is exact, including the centered linear term. -/
theorem giantExponent_eq {N m j a b c t : ℤ} (h : quotientRelation N m j a b c t) :
    giantExponent m j a b c=t*N+a+b*m-2*a*j := by
  unfold quotientRelation at h
  unfold giantExponent
  nlinarith only [h]

/-- The correct residue row yields a genuine local Fermat collision.
The signed index and the public m-squared baby step are both retained. -/
theorem quotient_row_power_hit {G : Type*} [CommGroup G] (g : G)
    {p q m j a b c t x i : ℤ} (hp : p=m*x+j)
    (h : quotientRelation (p*q) m j a b c t)
    (hi : quadratic a b c x=p*i) (hp0 : p≠0) (hperiod : g^(p-1)=1) :
    g^giantExponent m j a b c=g^(m^2*i) := by
  have he := scaled_quadratic_factor_sum hp h
  rw [hi] at he
  have hsum : a*p+b*m-2*a*j+t*q=m^2*i := by
    apply mul_left_cancel₀ hp0
    nlinarith only [he]
  have hd : giantExponent m j a b c=(p-1)*(t*q-a)+m^2*i := by
    rw [giantExponent_eq h]
    nlinarith only [hsum]
  rw [hd,zpow_add,zpow_mul,hperiod,one_zpow,one_mul]

/-- Every exact collision index supplies a quadratic with the actual
factor as an integer root; a nonzero leading coefficient is informative. -/
theorem quotient_row_recovery_equation {p q m j a b c t x i : ℤ}
    (hp : p=m*x+j) (h : quotientRelation (p*q) m j a b c t)
    (hi : quadratic a b c x=p*i) :
    quadratic a (b*m-2*a*j-m^2*i) (t*(p*q)) p=0 := by
  have he := scaled_quadratic_factor_sum hp h
  rw [hi] at he
  unfold quadratic
  nlinarith only [he]

/-- For the correct residue row, the executable public constructor has a
bounded integer index and an informative recovery equation on every
balanced semiprime. Factor coordinates enter only as proof witnesses. -/
theorem publicRow_balanced_coverage {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hq₂ : q≤2*p) (hm : 1<m) (hN : m.Coprime (p*q)) :
    let z := publicRow (p*q) m (p%m)
    ∃ i : ℤ, i.natAbs < indexLength (p*q) m ∧ z.a≠0 ∧
      quadratic z.a z.b z.c (p/m : ℕ)=p*i ∧
        quadratic z.a (z.b*m-2*z.a*(p%m : ℕ)-(m : ℤ)^2*i) (z.t*(p*q : ℕ)) p=0 := by
  have hmp : m.Coprime p := hN.of_dvd_right (dvd_mul_right p q)
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hmp
  let z := publicRow (p*q) m (p%m)
  have hc := publicRow_correct hm hN hj
  have he : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have h := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ) z.a z.b z.c z.t := by
    simpa only [Nat.cast_mul] using hc.2.2.2.2.2.1
  obtain ⟨i,hi⟩ := quotient_row_integer_index he hrel hmp.symm.isCoprime
  have hsum := scaled_quadratic_factor_sum he hrel
  rw [hi] at hsum
  have hs : (m : ℤ)^2*i=z.a*p+z.b*m-2*z.a*(p%m : ℕ)+z.t*q := by
    have hp0 : (p : ℤ)≠0 := by exact_mod_cast hp.ne_zero
    apply mul_left_cancel₀ hp0
    nlinarith only [hsum]
  have ht : |z.t|≤(m.sqrt : ℕ) := by
    rw [abs_of_nonneg hc.2.2.1.le]
    exact hc.2.2.2.1
  have ha : |z.a|≤(m.sqrt : ℕ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hc.2.1
  have hb : |z.b|≤(m/2+1 : ℕ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hc.2.2.2.2.1
  have hbound := factor_sum_index_bound (p:=p) (q:=q) (m:=m) (j:=(p%m : ℕ))
    (by exact_mod_cast hp.pos.le) (by exact_mod_cast hq.pos.le) (by positivity) (by positivity)
    (by exact_mod_cast (Nat.mod_lt p (by omega : 0<m)).le) ha hb ht hs
  have hbNat : i.natAbs*m^2≤m.sqrt*(p+q+2*m)+(m/2+1)*m := by
    rw [←Int.natCast_natAbs] at hbound
    exact_mod_cast hbound
  have hpRoot : p≤(p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p hpq)
  have hsumBound : p+q≤3*((p*q).sqrt+1) := by omega
  have hbudget : i.natAbs*m^2≤m.sqrt*(3*((p*q).sqrt+1)+2*m)+(m/2+1)*m := by
    have h := Nat.mul_le_mul_left m.sqrt (Nat.add_le_add_right hsumBound (2*m))
    omega
  have hindex : i.natAbs < indexLength (p*q) m := by
    unfold indexLength
    have hdiv := (Nat.le_div_iff_mul_le (pow_pos (by omega : 0<m) 2)).mpr hbudget
    omega
  exact ⟨i,hindex,hc.1,hi,by simpa only [Nat.cast_mul] using quotient_row_recovery_equation he hrel hi⟩

/-- Executable integer candidates from both square-root orientations.
Every candidate still needs the public proper-divisor validation. -/
def integerRoots (a L C : ℤ) : List ℤ :=
  let d := L^2-4*a*C
  if d<0 then [] else [(-L+Int.sqrt d)/(2*a),(-L-Int.sqrt d)/(2*a)]

/-- At any integer quadratic root the discriminant is an exact square. -/
theorem root_discriminant {a L C p : ℤ} (h : quadratic a L C p=0) :
    L^2-4*a*C=(2*a*p+L)^2 := by
  unfold quadratic at h
  nlinarith [congrArg (fun z : ℤ => 4*a*z) h]

/-- The literal public candidate list contains every integer root of a
nondegenerate quadratic. No factor is passed to its constructor. -/
theorem integerRoots_complete {a L C p : ℤ} (ha : a≠0)
    (h : quadratic a L C p=0) : p∈integerRoots a L C := by
  have hd := root_discriminant h
  have hn : ¬L^2-4*a*C<0 := by rw [hd]; exact not_lt.mpr (sq_nonneg _)
  have hs : Int.sqrt (L^2-4*a*C)=|(2*a*p+L)| := by
    rw [hd,pow_two,Int.sqrt_eq,Int.natCast_natAbs]
  have hden : 2*a≠0 := mul_ne_zero (by decide) ha
  unfold integerRoots
  rw [if_neg hn,hs]
  by_cases hsign : 0≤2*a*p+L
  · rw [abs_of_nonneg hsign]
    have he : (-L+(2*a*p+L))/(2*a)=p := by
      have heq : -L+(2*a*p+L)=p*(2*a) := by ring
      rw [heq,Int.mul_ediv_cancel _ hden]
    simp only [List.mem_cons]
    exact Or.inl he.symm
  · rw [abs_of_neg (lt_of_not_ge hsign)]
    have he : (-L-(-(2*a*p+L)))/(2*a)=p := by
      have heq : -L-(-(2*a*p+L))=p*(2*a) := by ring
      rw [heq,Int.mul_ediv_cancel _ hden]
    simp only [List.mem_cons]
    exact Or.inr (Or.inl he.symm)

/-- The executable public residue row supplies both an actual hidden-field
collision and a complete public quadratic candidate list. The index is a
proof witness; its acquisition still costs the explicit search axis. -/
theorem publicRow_balanced_power_coverage {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hq₂ : q≤2*p) (hm : 1<m) (hN : m.Coprime (p*q))
    (g : (ZMod p)ˣ) :
    let z := publicRow (p*q) m (p%m)
    ∃ i : ℤ, i.natAbs < indexLength (p*q) m ∧
      g^giantExponent m (p%m : ℕ) z.a z.b z.c=g^((m : ℤ)^2*i) ∧
        (p : ℤ)∈integerRoots z.a (z.b*m-2*z.a*(p%m : ℕ)-(m : ℤ)^2*i)
          (z.t*(p*q : ℕ)) := by
  let : Fact p.Prime := ⟨hp⟩
  let z := publicRow (p*q) m (p%m)
  obtain ⟨i,hindex,ha,hi,hroot⟩ := publicRow_balanced_coverage hp hq hpq hq₂ hm hN
  have hmp : m.Coprime p := hN.of_dvd_right (dvd_mul_right p q)
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hmp
  have hc := publicRow_correct hm hN hj
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ) z.a z.b z.c z.t := by
    simpa only [Nat.cast_mul] using hc.2.2.2.2.2.1
  have he : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have h := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hperiod : g^((p : ℤ)-1)=1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p g
    have hz : g^((p-1 : ℕ) : ℤ)=1 := by simpa only [zpow_natCast] using h
    simpa only [Nat.cast_sub hp.one_le,Nat.cast_one] using hz
  exact ⟨i,hindex,quotient_row_power_hit g he hrel hi
    (by exact_mod_cast hp.ne_zero) hperiod,integerRoots_complete ha hroot⟩

/-- Exact public control, including the informative integer quadratic and
both recovered square-root orientations. -/
theorem control_public_row :
    (publicRow 10403 4 1).a = -1 ∧ (publicRow 10403 4 1).b = -1 ∧
      (publicRow 10403 4 1).c=650 ∧ (publicRow 10403 4 1).t=1 ∧
        (publicRow 10403 4 1).divisions=1 ∧
          giantExponent 4 1 (-1) (-1) 650=10400 ∧
            integerRoots (-1) (-2) 10403=[-103,101] := by
  have hinv : publicInverse 4 1=1 := by
    norm_num [publicInverse,Int.gcdA,Nat.gcdA,Nat.xgcd,Nat.xgcdAux_rec]
  have hwalk : euclidShort 2 4 3 0 1 false=⟨1,1,true,1⟩ := by
    rw [euclidShort]
    norm_num only
    rw [euclidShort]
    norm_num
  have hu : (3 : ℤ).toNat=3 := rfl
  have hd : (41616 : ℤ).toNat=41616 := rfl
  norm_num only [publicRow,quotientSlope,hinv]
  norm_num only [hu]
  norm_num [hwalk,signed,liftRow,centered,giantExponent,integerRoots,Int.sqrt,
    hd]

end RiemannGaussian.SemiprimeQuotientRows
