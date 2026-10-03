/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeStrassenPrefix
import RiemannGaussian.SemiprimeRHCancellation

/-!
# A centre-free semiprime collision cover

The Lehman cross-difference witness can absorb its second weight into a
short exponent. This gives B geometric roots and a 3 B² + 1 exponent
interval, without constructing the literal square-root centres. Coverage
is universal on the small-factor-prefix complement; separation requires
the explicitly stated local-period conditions below.

The interval remains quadratic. The explicit baby/giant reshaping proved
here still needs at least order B^(3/2) inputs. No one-sixth bit-cost
theorem or universal base-selection theorem is asserted.
-/

namespace RiemannGaussian.SemiprimeCentreFreeCover

/-- The second Lehman weight can be folded into a short, positive
exponent. The searched root uses only the first weight, which is at most B. -/
theorem exists_short_linear_relation {p q B : ℕ} (hp : 0 < p) (hpq : p < q)
    (hB : 0 < B) (hsmall : B^2 < p) (hbudget : p*q ≤ B^6) :
    ∃ a b u : ℕ, 0 < a ∧ a ≤ B ∧ 0 < b ∧ a*b ≤ B^2 ∧
      a+b ≤ B^2+1 ∧ u ≤ 3*B^2 ∧
      a*(p*q)+B^2 = u+(p-1)*(a*q+b) := by
  obtain ⟨a, b, ha, hb, hab, hcross⟩ :=
    SemiprimeLehmanCoverage.exists_lehman_weights hp hpq (pow_pos hB 2)
      (SemiprimeLehmanCoverage.prefix_complement_ratio hp hsmall hbudget)
  have hBR : 0 < (B : ℝ) := by exact_mod_cast hB
  have hBs : 0 < (B : ℝ)^2 := by positivity
  have hN : (p : ℝ)*q ≤ (B : ℝ)^6 := by exact_mod_cast hbudget
  have hdSq : ((a : ℝ)*q-(b : ℝ)*p)^2 < (B : ℝ)^4 := by
    apply (mul_lt_mul_iff_left₀ hBs).mp
    have hh := hcross.trans_le hN
    push_cast at hh
    convert hh using 1; ring
  have hlo : -(B : ℝ)^2 < (a : ℝ)*q-(b : ℝ)*p := by
    nlinarith [sq_nonneg ((a : ℝ)*q-(b : ℝ)*p+(B : ℝ)^2)]
  have hhi : (a : ℝ)*q-(b : ℝ)*p < (B : ℝ)^2 := by
    nlinarith [sq_nonneg ((a : ℝ)*q-(b : ℝ)*p-(B : ℝ)^2)]
  have habOrder : a ≤ b := by
    by_contra hn
    have hba : (b : ℝ)+1 ≤ a := by exact_mod_cast (show b+1 ≤ a by omega)
    have hPQ : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
    have hP : (B : ℝ)^2 < p := by exact_mod_cast hsmall
    have hA : 0 ≤ (a : ℝ) := by positivity
    have hP0 : 0 ≤ (p : ℝ) := by positivity
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hPQ),
      mul_nonneg (sub_nonneg.mpr hba) hP0]
  have haB : a ≤ B := by nlinarith
  have hbB : b ≤ B^2 := by nlinarith
  have hsum : a+b ≤ B^2+1 := by
    have ha1 : 1 ≤ a := ha
    have hb1 : 1 ≤ b := hb
    have hh : 0 ≤ ((a : ℤ)-1)*((b : ℤ)-1) :=
      mul_nonneg (by omega) (by omega)
    have hs : a+b ≤ a*b+1 := by exact_mod_cast (by nlinarith :
      (a : ℤ)+b ≤ (a : ℤ)*b+1)
    omega
  have hloZ : -(B : ℤ)^2 < (a : ℤ)*q-(b : ℤ)*p := by exact_mod_cast hlo
  have hhiZ : (a : ℤ)*q-(b : ℤ)*p < (B : ℤ)^2 := by exact_mod_cast hhi
  let uZ : ℤ := (B : ℤ)^2+b+(a : ℤ)*q-(b : ℤ)*p
  have hu0 : 0 ≤ uZ := by dsimp [uZ]; omega
  have hu3 : uZ ≤ 3*(B : ℤ)^2 := by
    have hbZ : (b : ℤ) ≤ (B : ℤ)^2 := by exact_mod_cast hbB
    dsimp [uZ]
    omega
  let u := uZ.toNat
  have huCast : (u : ℤ) = uZ := Int.toNat_of_nonneg hu0
  have hu : u ≤ 3*B^2 := by exact_mod_cast (huCast ▸ hu3 : (u : ℤ) ≤ 3*(B : ℤ)^2)
  refine ⟨a, b, u, ha, haB, hb, hab, hsum, hu, ?_⟩
  have he : (a : ℤ)*((p : ℤ)*q)+(B : ℤ)^2 =
      (u : ℤ)+(p-1 : ℕ)*( (a : ℤ)*q+b) := by
    rw [huCast]
    dsimp [uZ]
    have hpZ : ((p-1 : ℕ) : ℤ) = (p : ℤ)-1 := by omega
    rw [hpZ]
    ring
  exact_mod_cast he

/-- The complete public prefix supplies the small-factor complement. -/
theorem exists_short_linear_relation_after_prefix {p q B : ℕ} (hp : p.Prime)
    (hpq : p < q) (hB : 0 < B) (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1) :
    ∃ a b u : ℕ, 0 < a ∧ a ≤ B ∧ 0 < b ∧ a*b ≤ B^2 ∧
      a+b ≤ B^2+1 ∧ u ≤ 3*B^2 ∧
      a*(p*q)+B^2 = u+(p-1)*(a*q+b) := by
  rw [SemiprimeGroupCoverage.prefixProduct_eq_factorial] at hclear
  exact exists_short_linear_relation hp.pos hpq hB
    (SemiprimeGroupCoverage.failed_prefix_excludes_small_prime hp (dvd_mul_right p q) hclear)
    hbudget

/-- A linear relation gives a literal power collision in the smaller
prime field, for every unit base. -/
theorem linear_relation_hit {G : Type*} [Monoid G] (g : G)
    {p q B a b u : ℕ} (hperiod : g^(p-1) = 1)
    (hrelation : a*(p*q)+B^2 = u+(p-1)*(a*q+b)) :
    g^(a*(p*q)+B^2) = g^u := by
  rw [hrelation, pow_add, pow_mul, hperiod, one_pow, mul_one]

/-- Universal prime-field coverage without any literal square-root
centre. The witnesses are proof objects, not inputs to the search. -/
theorem exists_centre_free_prime_collision {p q B : ℕ} (hp : p.Prime)
    (hpq : p < q) (hB : 0 < B) (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1)
    (g : (ZMod p)ˣ) :
    ∃ a u : ℕ, 0 < a ∧ a ≤ B ∧ u ≤ 3*B^2 ∧
      g^(a*(p*q)+B^2) = g^u := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, u, ha, haB, _, _, _, hu, he⟩ :=
    exists_short_linear_relation_after_prefix hp hpq hB hbudget hclear
  exact ⟨a, u, ha, haB, hu, linear_relation_hit g
    (ZMod.units_pow_card_sub_one_eq_one p g) he⟩

/-- The root sequence is geometric; its ratio is the public power g^N. -/
theorem root_step {G : Type*} [Monoid G] (g : G) (N B a : ℕ) :
    g^((a+1)*N+B^2) = g^(a*N+B^2)*g^N := by
  rw [← pow_add]
  congr 1
  ring

/-- Explicit geometric roots indexed by a=1,...,B. -/
def centreFreeRoots {G : Type*} [Monoid G] (g : G) (N B : ℕ) : List G :=
  (List.range B).map (fun i => g^((i+1)*N+B^2))

/-- The complete short-exponent interval; this is still quadratic. -/
def intervalTargets {G : Type*} [Monoid G] (g : G) (B : ℕ) : List G :=
  (List.range (3*B^2+1)).map (fun i => g^i)

theorem centreFreeRoots_length {G : Type*} [Monoid G] (g : G) (N B : ℕ) :
    (centreFreeRoots g N B).length = B := by simp [centreFreeRoots]

theorem intervalTargets_length {G : Type*} [Monoid G] (g : G) (B : ℕ) :
    (intervalTargets g B).length = 3*B^2+1 := by simp [intervalTargets]

/-- Every covered exponent has an exact baby/giant decomposition. -/
theorem interval_decomposition {B m u : ℕ} (hm : 0 < m) (hu : u ≤ 3*B^2) :
    ∃ j i : ℕ, j < 3*B^2/m+1 ∧ i < m ∧ u = j*m+i := by
  refine ⟨u/m, u%m, ?_, Nat.mod_lt _ hm, ?_⟩
  · have hh := Nat.div_le_div_right hu (c := m)
    omega
  · simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div u m).symm

/-- The explicit shifted roots use every first-weight/block pair. -/
def shiftedRoots {G : Type*} [Group G] (g : G) (N B m : ℕ) : List G :=
  (List.range B).flatMap (fun a => (List.range (3*B^2/m+1)).map
    (fun j => g^((((a+1)*N+B^2 : ℕ) : ℤ)-((j*m : ℕ) : ℤ))))

theorem shiftedRoots_length {G : Type*} [Group G] (g : G) (N B m : ℕ) :
    (shiftedRoots g N B m).length = B*(3*B^2/m+1) := by
  simp [shiftedRoots, List.length_flatMap, List.sum_replicate]

/-- The exact input count of this explicit baby/giant reshape cannot be
linear in B. This is not a lower bound for other interval algorithms. -/
theorem explicit_reshape_input_bound {B m : ℕ} (hB : 0 < B) (hm : 0 < m) :
    12*B^3 < (m+B*(3*B^2/m+1))^2 := by
  have hcover : 3*B^2 < m*(3*B^2/m+1) := by
    have hh := Nat.mod_lt (3*B^2) hm
    have he := Nat.mod_add_div (3*B^2) m
    nlinarith
  have hprod : 3*B^3 < m*(B*(3*B^2/m+1)) := by
    have hh := Nat.mul_lt_mul_of_pos_left hcover hB
    nlinarith
  have hprodZ : 3*(B : ℤ)^3 < (m : ℤ)*(B*(3*B^2/m+1) : ℕ) := by
    exact_mod_cast hprod
  have hboundZ : 12*(B : ℤ)^3 <
      ((m : ℤ)+(B*(3*B^2/m+1) : ℕ))^2 := by
    nlinarith [sq_nonneg ((m : ℤ)-(B*(3*B^2/m+1) : ℕ))]
  exact_mod_cast hboundZ

/-- If a divisor of the powering exponent survives L repeated powers,
its L stripped copies together with the final period divide the original
period. This avoids a factorization oracle or a valuation computation. -/
theorem surviving_power_dvd {G : Type*} [Group G] [Finite G] (g : G)
    {r E : ℕ} (hrE : r ∣ E) (L : ℕ)
    (hr : r ∣ orderOf (g^(E^L))) :
    r^L*orderOf (g^(E^L)) ∣ orderOf g := by
  induction L with
  | zero => simp
  | succ L ih =>
    have he : g^(E^(L+1)) = (g^(E^L))^E := by rw [pow_succ, pow_mul]
    have hcur : r ∣ orderOf (g^(E^L)) := by
      rw [he] at hr
      exact hr.trans (orderOf_pow_dvd E)
    have hgcd : r ∣ (orderOf (g^(E^L))).gcd E := Nat.dvd_gcd hcur hrE
    have hstep : r*orderOf ((g^(E^L))^E) ∣ orderOf (g^(E^L)) := by
      rw [orderOf_pow]
      have hh := Nat.mul_dvd_mul_right hgcd
        (orderOf (g^(E^L))/(orderOf (g^(E^L))).gcd E)
      simpa [Nat.mul_div_cancel' (Nat.gcd_dvd_left (orderOf (g^(E^L))) E)] using hh
    have hh := (Nat.mul_dvd_mul_left (r^L) hstep).trans (ih hcur)
    rw [he, pow_succ, Nat.mul_assoc]
    exact hh

/-- A sufficiently repeated factorial power removes every prime at most
B from the local period. The bound is on the original period. -/
theorem factorial_projection_rough {G : Type*} [Group G] [Finite G] (g : G)
    {B K L r : ℕ} (horder : orderOf g ≤ K) (hL : K < 2^L)
    (hr : r.Prime) (hrdiv : r ∣ orderOf (g^((B.factorial)^L))) :
    B < r := by
  by_contra hn
  have hrB : r ≤ B := by omega
  have hh := surviving_power_dvd g (Nat.dvd_factorial hr.pos hrB) L hrdiv
  have hpos := orderOf_pos (g^((B.factorial)^L))
  have hle : r^L ≤ orderOf g := by
    have hmul : r^L ≤ r^L*orderOf (g^((B.factorial)^L)) := by
      simpa using Nat.mul_le_mul_left (r^L) (show 1 ≤ orderOf (g^((B.factorial)^L)) from hpos)
    exact hmul.trans (Nat.le_of_dvd (orderOf_pos g) hh)
  have hpow : 2^L ≤ r^L := Nat.pow_le_pow_left hr.two_le L
  omega

/-- A long, B-rough period coprime to the smaller field's long period
cannot share a prime with the smaller field cardinality. The cubic width
bound is the arithmetic reason this implication is available. -/
theorem rough_order_coprime_cardinality {B p dp dq : ℕ}
    (hp : 1 < p) (hpB : p ≤ B^3) (hdp : dp ∣ p-1) (hlarge : B^2 < dp)
    (hc : dp.Coprime dq) (hrough : ∀ r, r.Prime → r ∣ dq → B < r) :
    dq.Coprime (p-1) := by
  by_contra hn
  obtain ⟨r, hr, hrdq, hrp⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hrB := hrough r hr hrdq
  have hcr : r.Coprime dp := hc.symm.of_dvd_left hrdq
  have hmul : r*dp ∣ p-1 := hcr.mul_dvd_of_dvd_of_dvd hrp hdp
  have hp1 : 0 < p-1 := by omega
  have hle := Nat.le_of_dvd hp1 hmul
  have hprod : B^3 < r*dp := by
    have hh := Nat.mul_lt_mul_of_pos_right hrB (show 0 < dp by omega)
    have hh' := Nat.mul_le_mul_left B hlarge.le
    nlinarith
  omega

/-- A positive short weight sum prevents the centre-free hit from also
closing the other local period. All period premises are visible. -/
theorem linear_relation_separates {G H : Type*} [Group G] [Group H]
    (g : G) (h : H) {p q B a b u : ℕ} (hq : 0 < q)
    (hperiod : g^(p-1) = 1) (horder : orderOf h ∣ q-1)
    (hc : (orderOf h).Coprime (p-1))
    (hsum0 : 0 < a+b) (hsum : a+b < orderOf h)
    (hrelation : a*(p*q)+B^2 = u+(p-1)*(a*q+b)) :
    g^(a*(p*q)+B^2) = g^u ∧ h^(a*(p*q)+B^2) ≠ h^u := by
  refine ⟨linear_relation_hit g hperiod hrelation, ?_⟩
  intro he
  have hpw : h^((p-1)*(a*q+b)) = 1 := by
    apply mul_left_cancel (a := h^u)
    simpa only [mul_one, ← pow_add, ← hrelation] using he
  have hd : orderOf h ∣ a*q+b := hc.dvd_of_dvd_mul_left
    (orderOf_dvd_of_pow_eq_one hpw)
  have heq : a*q+b = a*(q-1)+(a+b) := by
    have hh : q-1+1=q := by omega
    nlinarith
  have hds : orderOf h ∣ a+b := by
    rw [heq] at hd
    exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right horder a)).mpr hd
  exact (not_le_of_gt hsum) (Nat.le_of_dvd hsum0 hds)

/-- The common public projection gives a B-rough local period. Its
logarithmic repetition count exceeds every field's original unit order. -/
theorem public_projection_rough {p q B r : ℕ} (hp : p.Prime) (hq : 0 < q)
    (g : (ZMod p)ˣ) (hr : r.Prime)
    (hrdiv : r ∣ orderOf ((g^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))) :
    B < r := by
  let : Fact p.Prime := ⟨hp⟩
  have hbound : orderOf (g^(p*q-1)) ≤ p-1 :=
    Nat.le_of_dvd (by have hh := hp.one_lt; omega)
      (ZMod.orderOf_units_dvd_card_sub_one _)
  have hq1 : 1 ≤ q := hq
  have hppq : p-1 < p*q+1 := by
    have hh : p ≤ p*q := by nlinarith
    omega
  exact factorial_projection_rough (g^(p*q-1)) hbound
    (hppq.trans_le (Nat.le_pow_clog (by decide) (p*q+1))) hr hrdiv

/-- In the long-period branch, the rough public projection forces the
other period to be coprime to the smaller field cardinality. -/
theorem projected_order_coprime_cardinality {p q B : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≤ q) (hbudget : p*q ≤ B^6)
    (g : (ZMod p)ˣ) (h : (ZMod q)ˣ)
    (hlarge : B^2 < orderOf ((g^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))) :
    (orderOf ((h^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))).Coprime (p-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply rough_order_coprime_cardinality hp.one_lt
    (SemiprimeGroupCoverage.smaller_factor_le_cubic_width hpq hbudget)
    (ZMod.orderOf_units_dvd_card_sub_one _) hlarge
    (SemiprimeOrderSeparation.further_projection_coprime hp hq g h _)
  intro r hr hrd
  have hh : q*p = p*q := Nat.mul_comm _ _
  apply public_projection_rough hq hp.pos h hr
  simpa only [hh] using hrd

/-- After the short-period branch has excluded both small local periods,
the universal centre-free relation gives a proper separating collision.
This theorem does not discharge public base selection or interval cost. -/
theorem exists_projected_separating_collision {p q B : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hB : 0 < B) (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1)
    (g : (ZMod p)ˣ) (h : (ZMod q)ˣ)
    (hlargeP : B^2 < orderOf ((g^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1)))))
    (hlargeQ : B^2+1 < orderOf ((h^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))) :
    ∃ a u : ℕ, 0 < a ∧ a ≤ B ∧ u ≤ 3*B^2 ∧
      ((g^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))^(a*(p*q)+B^2) =
        ((g^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))^u ∧
      ((h^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))^(a*(p*q)+B^2) ≠
        ((h^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))^u := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, b, u, ha, haB, _, _, hsum, hu, he⟩ :=
    exists_short_linear_relation_after_prefix hp hpq hB hbudget hclear
  have hh := linear_relation_separates
    ((g^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1))))
    ((h^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1)))) hq.pos
    (ZMod.units_pow_card_sub_one_eq_one p _)
    (ZMod.orderOf_units_dvd_card_sub_one _)
    (projected_order_coprime_cardinality hp hq hpq.le hbudget g h hlargeP)
    (show 0 < a+b by omega) (hsum.trans_lt hlargeQ) he
  exact ⟨a, u, ha, haB, hu, hh⟩

/-- Prime-field reduction of a residue's canonical representative. -/
theorem castHom_val {N r : ℕ} [NeZero N] (hrN : r ∣ N) (x : ZMod N) :
    (x.val : ZMod r) = ZMod.castHom hrN (ZMod r) x := by
  rw [ZMod.castHom_apply]
  exact ZMod.natCast_val x

/-- A residue vanishing in exactly the smaller prime field has GCD p. -/
theorem separating_residue_gcd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (x : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) x = 0)
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) x ≠ 0) :
    (p*q).gcd x.val = p := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  apply SemiprimeOrderSeparation.gcd_semiprime_of_separating_residue hq
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [castHom_val (dvd_mul_right p q), hP]
  · intro hdiv
    apply hQ
    rw [← castHom_val (dvd_mul_left q p)]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdiv

/-- The field collision certificate retains the literal original
residual, so its proper factor survives composite-ring recovery. -/
theorem separating_power_gcd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) {e u : ℕ}
    (hP : (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g)^e =
      (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g)^u)
    (hQ : (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g)^e ≠
      (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g)^u) :
    (p*q).gcd ((g^u : ZMod (p*q))-(g^e : ZMod (p*q))).val = p := by
  apply separating_residue_gcd hp hq
  · rw [map_sub]
    apply sub_eq_zero.mpr
    have hh := congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hP.symm
    rw [map_pow, map_pow]
    simp only [Units.val_pow_eq_pow_val, Units.coe_map] at hh
    exact hh
  · rw [map_sub, sub_ne_zero]
    intro he
    apply hQ
    apply Units.ext
    simp only [map_pow] at he
    simp only [Units.val_pow_eq_pow_val, Units.coe_map]
    exact he.symm

/-- Unit rephasing is exact even when the residue saturates the whole
modulus. The signed shift does not cancel or discard a target channel. -/
theorem shifted_difference_gcd {N : ℕ} (g : (ZMod N)ˣ)
    {e u j m i : ℕ} (hu : u = j*m+i) :
    N.gcd ((↑(g^(i : ℤ)) : ZMod N)-(↑(g^((e : ℤ)-(j*m : ℕ))) : ZMod N)).val =
      N.gcd ((g^u : ZMod N)-(g^e : ZMod N)).val := by
  have he : (↑(g^(-((j*m : ℕ) : ℤ))) : ZMod N)*
      ((g^u : ZMod N)-(g^e : ZMod N)) =
      (↑(g^(i : ℤ)) : ZMod N)-(↑(g^((e : ℤ)-(j*m : ℕ))) : ZMod N) := by
    rw [mul_sub, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, ← Units.val_mul]
    have h1 : g^(-((j*m : ℕ) : ℤ))*g^u = g^(i : ℤ) := by
      rw [← zpow_natCast g u, ← zpow_add]
      congr 1
      exact_mod_cast (by omega : -(j*m : ℤ)+u=i)
    have h2 : g^(-((j*m : ℕ) : ℤ))*g^e = g^((e : ℤ)-(j*m : ℕ)) := by
      rw [← zpow_natCast g e, ← zpow_add]
      congr 1
      omega
    rw [h1, h2]
  rw [← he]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq (g^(-((j*m : ℕ) : ℤ))) _

/-- Membership of a shifted root keeps both the first weight and block
index. A flattened list does not lose the original residual witness. -/
theorem shifted_root_mem {G : Type*} [Group G] (g : G) {N B m a j : ℕ}
    (ha : 0 < a) (haB : a ≤ B) (hj : j < 3*B^2/m+1) :
    g^(((a*N+B^2 : ℕ) : ℤ)-(j*m : ℕ)) ∈ shiftedRoots g N B m := by
  apply List.mem_flatMap.mpr
  refine ⟨a-1, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_map.mpr
  refine ⟨j, List.mem_range.mpr hj, ?_⟩
  have he : a-1+1=a := by omega
  rw [he]

/-- The recovery interface uses the charged explicit shifted-root list
and baby list, with shared global roots removed by the existing detector. -/
noncomputable def recoverShifted {N : ℕ} (g : (ZMod N)ˣ) (B m : ℕ) : Option ℕ :=
  SemiprimeCartesianCompletion.recoverResidueBatch
    ((shiftedRoots g N B m).map (fun x : (ZMod N)ˣ => (x : ZMod N))).toFinset
    ((List.range m).map (fun i => (g^i : ZMod N)))

/-- Both exponents depend only on the public modulus and width. -/
def projectedUnit {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) : (ZMod N)ˣ :=
  (g^(N-1))^((B.factorial)^(Nat.clog 2 (N+1)))

/-- Staged powering avoids constructing the full factorial exponent. -/
def stagedProjection {G : Type*} [Monoid G] (g : G) (B L : ℕ) : G :=
  (List.range B).foldl (fun x i => x^((i+1)^L)) g

/-- The B charged stages compute precisely the full factorial projection. -/
theorem stagedProjection_eq {G : Type*} [Monoid G] (g : G) (B L : ℕ) :
    stagedProjection g B L = g^((B.factorial)^L) := by
  induction B with
  | zero => simp [stagedProjection]
  | succ B ih =>
    change (List.range (B+1)).foldl (fun x i => x^((i+1)^L)) g = _
    rw [List.range_succ, List.foldl_append]
    change (stagedProjection g B L)^((B+1)^L) = _
    rw [ih, Nat.factorial_succ, mul_pow, Nat.mul_comm, pow_mul]

/-- A public coprime-to-one certificate excludes a trivial component;
the algorithm never asks for the hidden prime or its local order. -/
theorem clear_unit_component_order_ne_one {N r : ℕ} [NeZero N]
    (hr : r.Prime) (hrN : r ∣ N) (g : (ZMod N)ˣ)
    (hclear : N.gcd ((g : ZMod N)-1).val=1) :
    orderOf (Units.map (ZMod.castHom hrN (ZMod r)).toMonoidHom g) ≠ 1 := by
  intro he
  have hunit := orderOf_eq_one_iff.mp he
  have hv := congrArg (fun z : (ZMod r)ˣ => (z : ZMod r)) hunit
  simp only [Units.coe_map, Units.val_one] at hv
  have hfield : ZMod.castHom hrN (ZMod r) ((g : ZMod N)-1)=0 := by
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr hv
  have hdiv : r ∣ ((g : ZMod N)-1).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [castHom_val hrN, hfield]
  have hh := Nat.dvd_gcd hrN hdiv
  rw [hclear] at hh
  exact hr.not_dvd_one hh

/-- The short-period search contains m giant powers and m babies. -/
noncomputable def recoverShort {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : Option ℕ :=
  SemiprimeCartesianCompletion.recoverResidueBatch
    ((List.range m).map (fun j => (g^(m*(j+1)) : ZMod N))).toFinset
    ((List.range m).map (fun i => (g^i : ZMod N)))

/-- Coprime local periods guarantee a proper short-period hit whenever
the smaller field's period lies inside the square cover. -/
theorem recoverShort_succeeds_of_small_left {p q m : ℕ} (hp : p.Prime)
    (hq : q.Prime) (g : (ZMod (p*q))ˣ) (hm : 0 < m)
    (hc : (orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g)).Coprime
      (orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g)))
    (hother : orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g) ≠ 1)
    (hsmall : orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g) ≤ m*m) :
    ∃ d, recoverShort g m=some d := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  let gp := Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g
  let gq := Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g
  obtain ⟨d, hd, hdm, hP, hQ⟩ := SemiprimeOrderSeparation.bounded_separating_witness
    gp gq hc (orderOf_pos gp) hsmall hother
  obtain ⟨j, i, hj0, hjm, hi, he⟩ := SemiprimeOrderSeparation.geometric_order_cover hm hd hdm
  have hhitP : gp^(m*j)=gp^i := by rw [← he, pow_add, hP, one_mul]
  have hhitQ : gq^(m*j) ≠ gq^i := by
    intro hh
    apply hQ
    have hmul : gq^d*gq^i=1*gq^i := by
      simpa only [one_mul, ← pow_add, he] using hh
    exact mul_right_cancel hmul
  have hfactor := separating_power_gcd hp hq g hhitP hhitQ
  have hx : (g^(m*j) : ZMod (p*q)) ∈
      (List.range m).map (fun j => (g^(m*(j+1)) : ZMod (p*q))) := by
    apply List.mem_map.mpr
    refine ⟨j-1, List.mem_range.mpr (by omega), ?_⟩
    have hj : j-1+1=j := by omega
    rw [hj]
  have ht : (g^i : ZMod (p*q)) ∈
      (List.range m).map (fun i => (g^i : ZMod (p*q))) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  apply SemiprimeCartesianCompletion.recoverResidueList_succeeds_of_proper_pair hx ht
  rw [hfactor]
  exact ⟨hp.one_lt, by have hh := hq.one_lt; nlinarith [hp.pos], dvd_mul_right p q⟩

/-- The symmetric period is covered by the same public short search. -/
theorem recoverShort_succeeds_of_small_right {p q m : ℕ} (hp : p.Prime)
    (hq : q.Prime) (g : (ZMod (p*q))ˣ) (hm : 0 < m)
    (hc : (orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g)).Coprime
      (orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g)))
    (hother : orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g) ≠ 1)
    (hsmall : orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g) ≤ m*m) :
    ∃ d, recoverShort g m=some d := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  let gp := Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g
  let gq := Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g
  obtain ⟨d, hd, hdm, hQ, hP⟩ := SemiprimeOrderSeparation.bounded_separating_witness
    gq gp hc.symm (orderOf_pos gq) hsmall hother
  obtain ⟨j, i, hj0, hjm, hi, he⟩ := SemiprimeOrderSeparation.geometric_order_cover hm hd hdm
  have hhitQ : gq^(m*j)=gq^i := by rw [← he, pow_add, hQ, one_mul]
  have hhitP : gp^(m*j) ≠ gp^i := by
    intro hh
    apply hP
    have hmul : gp^d*gp^i=1*gp^i := by
      simpa only [one_mul, ← pow_add, he] using hh
    exact mul_right_cancel hmul
  let x : ZMod (p*q) := (g^i : ZMod (p*q))-(g^(m*j) : ZMod (p*q))
  have hqdiv : q ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [castHom_val (dvd_mul_left q p)]
    change ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((g^i : ZMod (p*q))-(g^(m*j) : ZMod (p*q)))=0
    rw [map_sub]
    apply sub_eq_zero.mpr
    have hh := congrArg (fun z : (ZMod q)ˣ => (z : ZMod q)) hhitQ.symm
    rw [map_pow, map_pow]
    simp only [gq, Units.val_pow_eq_pow_val, Units.coe_map] at hh
    exact hh
  have hpnot : ¬p ∣ x.val := by
    intro hdiv
    have hh := (ZMod.natCast_eq_zero_iff _ p).mpr hdiv
    rw [castHom_val (dvd_mul_right p q)] at hh
    change ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((g^i : ZMod (p*q))-(g^(m*j) : ZMod (p*q)))=0 at hh
    rw [map_sub, sub_eq_zero] at hh
    apply hhitP
    apply Units.ext
    simp only [map_pow] at hh
    simp only [gp, Units.val_pow_eq_pow_val, Units.coe_map]
    exact hh.symm
  have hfactor : (p*q).gcd x.val=q :=
    Nat.gcd_mul_of_coprime_of_dvd (hp.coprime_iff_not_dvd.mpr hpnot) hqdiv
  have hx : (g^(m*j) : ZMod (p*q)) ∈
      (List.range m).map (fun j => (g^(m*(j+1)) : ZMod (p*q))) := by
    apply List.mem_map.mpr
    refine ⟨j-1, List.mem_range.mpr (by omega), ?_⟩
    have hj : j-1+1=j := by omega
    rw [hj]
  have ht : (g^i : ZMod (p*q)) ∈
      (List.range m).map (fun i => (g^i : ZMod (p*q))) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  apply SemiprimeCartesianCompletion.recoverResidueList_succeeds_of_proper_pair hx ht
  change SemiprimeGroupSelection.ProperDivisor (p*q) ((p*q).gcd x.val)
  rw [hfactor]
  exact ⟨hq.one_lt, by have hh := hp.one_lt; nlinarith [hq.pos], dvd_mul_left q p⟩

/-- Failing the public short search discharges both long-period premises.
Its only nontriviality premise is the public GCD certificate. -/
theorem failed_projected_short_forces_long {p q B s : ℕ} (hp : p.Prime)
    (hq : q.Prime) (g : (ZMod (p*q))ˣ) (hs : 0 < s)
    (hclear : (p*q).gcd ((projectedUnit g B : ZMod (p*q))-1).val=1)
    (hnone : recoverShort (projectedUnit g B) s=none) :
    s*s < orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
      (projectedUnit g B)) ∧
    s*s < orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
      (projectedUnit g B)) := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hP := clear_unit_component_order_ne_one hp (dvd_mul_right p q) (projectedUnit g B) hclear
  have hQ := clear_unit_component_order_ne_one hq (dvd_mul_left q p) (projectedUnit g B) hclear
  have hc := SemiprimeOrderSeparation.further_projection_coprime hp hq
    (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g)
    (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g)
    ((B.factorial)^(Nat.clog 2 (p*q+1)))
  have hc' : (orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
      (projectedUnit g B))).Coprime
      (orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
      (projectedUnit g B))) := by
    simpa only [projectedUnit, map_pow] using hc
  constructor
  · by_contra hn
    obtain ⟨d, hd⟩ := recoverShort_succeeds_of_small_left hp hq (projectedUnit g B)
      hs hc' hQ (by omega)
    rw [hnone] at hd
    contradiction
  · by_contra hn
    obtain ⟨d, hd⟩ := recoverShort_succeeds_of_small_right hp hq (projectedUnit g B)
      hs hc' hP (by omega)
    rw [hnone] at hd
    contradiction

/-- The long-period coverage theorem yields a proper original GCD for a
single public unit. Local periods remain proof-side conditions. -/
theorem exists_projected_proper_hit {p q B : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hB : 0 < B) (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1)
    (g : (ZMod (p*q))ˣ)
    (hlargeP : B^2 < orderOf (Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom (projectedUnit g B)))
    (hlargeQ : B^2+1 < orderOf (Units.map
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom (projectedUnit g B))) :
    ∃ a u : ℕ, 0 < a ∧ a ≤ B ∧ u ≤ 3*B^2 ∧
      (p*q).gcd (((projectedUnit g B)^u : ZMod (p*q))-
        ((projectedUnit g B)^(a*(p*q)+B^2) : ZMod (p*q))).val = p := by
  obtain ⟨a, u, ha, haB, hu, hP, hQ⟩ := exists_projected_separating_collision
    hp hq hpq hB hbudget hclear
    (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g)
    (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g)
    (by simpa only [projectedUnit, map_pow] using hlargeP)
    (by simpa only [projectedUnit, map_pow] using hlargeQ)
  refine ⟨a, u, ha, haB, hu, separating_power_gcd hp hq (projectedUnit g B) ?_ ?_⟩
  · simpa only [projectedUnit, map_pow] using hP
  · simpa only [projectedUnit, map_pow] using hQ

/-- Every original proper hit survives the reshape and is recovered.
The theorem charges no unproved fast circuit for constructing the lists. -/
theorem recoverShifted_succeeds_of_proper_hit {N : ℕ} [NeZero N]
    (g : (ZMod N)ˣ) {B m a u : ℕ} (hm : 0 < m)
    (ha : 0 < a) (haB : a ≤ B) (hu : u ≤ 3*B^2)
    (hh : SemiprimeGroupSelection.ProperDivisor N
      (N.gcd ((g^u : ZMod N)-(g^(a*N+B^2) : ZMod N)).val)) :
    ∃ d, recoverShifted g B m = some d := by
  obtain ⟨j, i, hj, hi, he⟩ := interval_decomposition hm hu
  have hshift := shifted_difference_gcd g he (e := a*N+B^2)
  have hx : (↑(g^(((a*N+B^2 : ℕ) : ℤ)-(j*m : ℕ))) : ZMod N) ∈
      (shiftedRoots g N B m).map (fun x : (ZMod N)ˣ => (x : ZMod N)) :=
    List.mem_map.mpr ⟨(g^(((a*N+B^2 : ℕ) : ℤ)-(j*m : ℕ)) : (ZMod N)ˣ),
      shifted_root_mem g (N := N) ha haB hj, rfl⟩
  have ht : (g^i : ZMod N) ∈ (List.range m).map (fun i => (g^i : ZMod N)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  apply SemiprimeCartesianCompletion.recoverResidueList_succeeds_of_proper_pair hx ht
  rw [← hshift] at hh
  simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using hh

/-- Proper recovery for the explicitly stated long-period branch. The
constructor receives the public unit, width and block size only. -/
theorem recoverShifted_projected_succeeds {p q B m : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hB : 0 < B) (hm : 0 < m) (hbudget : p*q ≤ B^6)
    (hclear : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B) = 1)
    (g : (ZMod (p*q))ˣ)
    (hlargeP : B^2 < orderOf (Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom (projectedUnit g B)))
    (hlargeQ : B^2+1 < orderOf (Units.map
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom (projectedUnit g B))) :
    ∃ d, recoverShifted (projectedUnit g B) B m = some d := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  obtain ⟨a, u, ha, haB, hu, he⟩ := exists_projected_proper_hit
    hp hq hpq hB hbudget hclear g hlargeP hlargeQ
  apply recoverShifted_succeeds_of_proper_hit (projectedUnit g B) hm ha haB hu
  rw [he]
  exact ⟨hp.one_lt, by have hh := hq.one_lt; nlinarith [hp.pos], dvd_mul_right p q⟩

/-- Public certificates from the prefix and short-period search discharge
every hidden-period condition in the centre-free recovery theorem.
This still leaves base selection and the B^(3/2) reshape cost open. -/
theorem recoverShifted_after_failed_short {p q B m : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hB : 0 < B) (hm : 0 < m) (hbudget : p*q ≤ B^6)
    (hprefix : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B)=1)
    (g : (ZMod (p*q))ˣ)
    (hclear : (p*q).gcd ((projectedUnit g B : ZMod (p*q))-1).val=1)
    (hnone : recoverShort (projectedUnit g B) (2*B+1)=none) :
    ∃ d, recoverShifted (projectedUnit g B) B m=some d := by
  have hlong := failed_projected_short_forces_long hp hq g (by omega) hclear hnone
  apply recoverShifted_projected_succeeds hp hq hpq hB hm hbudget hprefix g
  · nlinarith [hlong.1]
  · nlinarith [hlong.2]

set_option maxRecDepth 32768 in
/-- A public control beyond the (2B+1)² short-period range. The small
fixed projection is a reproducible example, not the general factorial
projection nor a universal guarantee about the base 2. -/
theorem control_long_original_hit :
    Nat.Prime 44963 ∧ Nat.Prime 62347 ∧
    44963*62347=2803308161 ∧
    (37 : ℕ)^6 < 2803308161 ∧ 2803308161 ≤ (38 : ℕ)^6 ∧
    (38 : ℕ)^2 < 44963 ∧
    13*2803308161+38^2 = 2639+(44963-1)*(13*62347+18) ∧
    (13 : ℕ)+18 ≤ 38^2+1 ∧ (2639 : ℕ) ≤ 3*38^2 ∧
    (((2 : ZMod 2803308161)^((2803308161-1)*6^32)) : ZMod 2803308161)=1823692905 ∧
    Nat.gcd 2803308161
      (((1823692905 : ZMod 2803308161)^2639)-
        (1823692905 : ZMod 2803308161)^(13*2803308161+38^2)).val=44963 := by
  norm_num
  reduce_mod_char
  norm_num [ZMod.val_ofNat]

set_option maxRecDepth 32768 in
/-- The two local periods in the finite control exceed the complete
linear short-period batch's range; the new hit is outside that pass. -/
theorem control_long_period_certificates :
    Nat.Prime 22481 ∧ Nat.Prime 10391 ∧
    (1823692905 : ZMod 44963)^22481=1 ∧ (1823692905 : ZMod 44963) ≠ 1 ∧
    (1823692905 : ZMod 62347)^10391=1 ∧ (1823692905 : ZMod 62347) ≠ 1 ∧
    (2*38+1 : ℕ)^2 < 22481 ∧ (2*38+1 : ℕ)^2 < 10391 := by
  norm_num
  reduce_mod_char
  norm_num
  decide

/-- Prime period certificates determine the exact two local orders. -/
theorem control_long_local_orders :
    orderOf (1823692905 : ZMod 44963)=22481 ∧
    orderOf (1823692905 : ZMod 62347)=10391 ∧
    (2*38+1 : ℕ)^2 < orderOf (1823692905 : ZMod 44963) ∧
    (2*38+1 : ℕ)^2 < orderOf (1823692905 : ZMod 62347) := by
  obtain ⟨hrp, hrq, hpowP, hneP, hpowQ, hneQ, hlongP, hlongQ⟩ :=
    control_long_period_certificates
  let : Fact (Nat.Prime 22481) := ⟨hrp⟩
  let : Fact (Nat.Prime 10391) := ⟨hrq⟩
  have hP : orderOf (1823692905 : ZMod 44963)=22481 := orderOf_eq_prime hpowP hneP
  have hQ : orderOf (1823692905 : ZMod 62347)=10391 := orderOf_eq_prime hpowQ hneQ
  exact ⟨hP, hQ, hP.symm ▸ hlongP, hQ.symm ▸ hlongQ⟩

set_option maxRecDepth 32768 in
/-- A public base can remain in the projection kernel even after a
clear quadratic prefix. Arbitrary base selection is still unresolved. -/
theorem control_public_base_kernel :
    Nat.Prime 829 ∧ Nat.Prime 1657 ∧ 829*1657=1373653 ∧
    (10 : ℕ)^6 < 1373653 ∧ 1373653 ≤ (11 : ℕ)^6 ∧
    (11 : ℕ)^2 < 829 ∧ Nat.gcd 1373653 ((11 : ℕ)^2).factorial=1 ∧
    (2 : ZMod 1373653)^(1373653-1)=1 := by
  norm_num
  reduce_mod_char

end RiemannGaussian.SemiprimeCentreFreeCover
