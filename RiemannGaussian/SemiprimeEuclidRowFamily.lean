/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeQuotientCentering

/-!
# Complete Euclidean intermediate-row packets

This public family retains every convergent and intermediate quadratic,
both public balanced-factor centers, and the original row in each packet.
Its coefficient relations are exact. A kernel-checked literal semiprime
control tests the proposed linear-modulus baby window. It is an audit of
this particular candidate family, not a general factoring lower bound.
-/

namespace RiemannGaussian.SemiprimeEuclidRowFamily

open SemiprimeQuotientRows SemiprimeQuotientCentering

/-- Retain every current and intermediate Euclidean vector. Full-step
duplicates are omitted; the following recursive row retains that vector. -/
def euclidPairs (r₀ r₁ x y : ℕ) (negative : Bool) : List (ℤ×ℕ) :=
  if r₁=0 then [] else
    (signed negative r₁,y)::
      ((List.range (r₀/r₁-1)).map (fun k =>
        (signed (!negative) (r₀-(k+1)*r₁),x+(k+1)*y))++
          euclidPairs r₁ (r₀%r₁) y (x+r₀/r₁*y) (!negative))
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- Orienting a modular vector keeps its positive denominator without
discarding the signed numerator. -/
theorem oriented_congruence {m u r t : ℕ} {negative : Bool}
    (h : (r : ℤ) ≡ (u : ℤ)*signed negative t [ZMOD m]) :
    signed negative r ≡ (u : ℤ)*t [ZMOD m] := by
  cases hn : negative with
  | false => simpa [hn,signed] using h
  | true => simpa [hn,signed] using h.neg

/-- Every intermediate division, rather than only the full quotient,
preserves the same exact modular relation. -/
theorem intermediate_congruence {m u r₀ r₁ x y k : ℕ} {negative : Bool}
    (hk : k*r₁≤r₀)
    (h₀ : (r₀ : ℤ) ≡ -(u : ℤ)*signed negative x [ZMOD m])
    (h₁ : (r₁ : ℤ) ≡ (u : ℤ)*signed negative y [ZMOD m]) :
    (r₀-k*r₁ : ℕ) ≡ (u : ℤ)*signed (!negative) (x+k*y) [ZMOD m] := by
  rw [Nat.cast_sub hk,Nat.cast_mul,signed_update]
  convert h₀.sub (h₁.mul_left (k : ℤ)) using 1
  ring

/-- The executable full family consists of informative, positive-
denominator vectors in the original modular quotient class. -/
theorem euclidPairs_correct {m u r₀ r₁ x y : ℕ} {negative : Bool}
    (horder : r₁<r₀) (hy : 0<y)
    (h₀ : (r₀ : ℤ) ≡ -(u : ℤ)*signed negative x [ZMOD m])
    (h₁ : (r₁ : ℤ) ≡ (u : ℤ)*signed negative y [ZMOD m])
    {z : ℤ×ℕ} (hz : z∈euclidPairs r₀ r₁ x y negative) :
    z.1≠0 ∧ 0<z.2 ∧ z.1 ≡ (u : ℤ)*z.2 [ZMOD m] := by
  rw [euclidPairs] at hz
  split_ifs at hz with hr
  · simp only [List.not_mem_nil] at hz
  · have hrpos : 0<r₁ := by omega
    simp only [List.mem_cons,List.mem_append,List.mem_map] at hz
    rcases hz with hcur | hmid | htail
    · subst z
      have ha : signed negative r₁≠0 := by
        intro he
        have he' := congrArg Int.natAbs he
        rw [signed_natAbs] at he'
        simp only [Int.natAbs_zero] at he'
        omega
      exact ⟨ha,hy,oriented_congruence h₁⟩
    · obtain ⟨k,hk,rfl⟩ := hmid
      have hk' : k+1<r₀/r₁ := by
        have h := List.mem_range.mp hk
        omega
      have hmul : (k+1)*r₁<r₀ := by
        exact (Nat.mul_lt_mul_of_pos_right hk' hrpos).trans_le (Nat.div_mul_le_self _ _)
      have ha : signed (!negative) (r₀-(k+1)*r₁)≠0 := by
        intro he
        have he' := congrArg Int.natAbs he
        rw [signed_natAbs] at he'
        simp only [Int.natAbs_zero] at he'
        omega
      exact ⟨ha,by positivity,oriented_congruence (intermediate_congruence hmul.le h₀ h₁)⟩
    · have hc := euclid_congruence_step h₀ h₁
      have hq : 0<r₀/r₁ := Nat.div_pos horder.le hrpos
      exact euclidPairs_correct (Nat.mod_lt _ hrpos) (by positivity) hc.1 hc.2 htail
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- N-only unit-residue coordinates; no hidden factor selects a vector. -/
def publicPairs (N m j : ℕ) : List (ℤ×ℕ) :=
  euclidPairs m (quotientSlope N m j%m) 0 1 false

/-- Every publicly emitted vector satisfies the inverse-product class
needed by the exact quadratic lift. -/
theorem publicPairs_correct {N m j : ℕ} (hm : 0<m) {z : ℤ×ℕ}
    (hz : z∈publicPairs N m j) :
    z.1≠0 ∧ 0<z.2 ∧ z.1 ≡ (N : ℤ)*(publicInverse m j)^2*z.2 [ZMOD m] := by
  let u := quotientSlope N m j
  have hc := euclidPairs_correct (m:=m) (u:=u) (r₀:=m) (r₁:=u%m)
    (x:=0) (y:=1) (negative:=false) (Nat.mod_lt _ hm) (by decide)
    (by simp [signed,Int.ModEq])
    (by simpa [signed] using Int.mod_modEq (u : ℤ) m) hz
  exact ⟨hc.1,hc.2.1,hc.2.2.trans ((quotientSlope_modEq hm).mul_right (z.2 : ℤ))⟩

/-- Public center for the larger factor, retaining the same offset.
The two factor orientations are kept rather than conflated. -/
def reflectedShift (N m j : ℕ) (a b t : ℤ) : ℤ :=
  let v := b*m-2*a*j
  let lo := t*(N/2).sqrt+a*(if 0≤a then N.sqrt else (2*N).sqrt)+v
  let hi := t*N.sqrt+a*(if 0≤a then (2*N).sqrt else N.sqrt)+v
  (lo+hi+(m : ℤ)^2)/(2*(m : ℤ)^2)

/-- A complete original row with its residue and public center retained. -/
structure FamilyPacket where
  /-- The original public unit residue. -/
  residue : ℕ
  /-- Its informative quadratic before phase extraction. -/
  original : QuotientRow
  /-- The exact public integer change of collision origin. -/
  shift : ℤ
deriving Repr

/-- Every intermediate vector gets both public balanced-factor centers. -/
def residuePackets (N m j : ℕ) : List FamilyPacket :=
  (publicPairs N m j).flatMap (fun v =>
    let z := liftRow N m j (publicInverse m j) v.1 v.2
    [⟨j,z,publicShift N m j z.a z.b z.t⟩,⟨j,z,reflectedShift N m j z.a z.b z.t⟩])

/-- Enumerate all public unit residues; private factors are proof
witnesses only. This is a finite constructor, not a price certificate. -/
def publicPackets (N m : ℕ) : List FamilyPacket :=
  (List.range m).flatMap (fun j => if j.Coprime m then residuePackets N m j else [])

/-- Exact giant exponent of the retained centered row. -/
def packetExponent (m : ℕ) (w : FamilyPacket) : ℤ :=
  giantExponent m w.residue w.original.a w.original.b w.original.c-w.shift*(m : ℤ)^2

/-- Public exponents retain their entire source packet upstream. -/
def publicExponents (N m : ℕ) : List ℤ := (publicPackets N m).map (packetExponent m)

/-- Every intermediate lifted row has the original exact quotient
relation, without a short-vector or factor-residue oracle. -/
theorem intermediate_row_correct {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m)
    {v : ℤ×ℕ} (hv : v∈publicPairs N m j) :
    let z := liftRow N m j (publicInverse m j) v.1 v.2
    z.a≠0 ∧ 0<z.t ∧ quotientRelation N m j z.a z.b z.c z.t := by
  have hc := publicPairs_correct hm hv
  exact ⟨hc.1,by change (0 : ℤ)<(v.2 : ℤ); exact_mod_cast hc.2.1,
    liftRow_correct (publicInverse_correct hj) hc.2.2⟩

/-- The actual centered packet exponent preserves the target shift
proved for the original quotient row. -/
theorem packetExponent_eq (m : ℕ) (w : FamilyPacket) :
    packetExponent m w=giantExponent m w.residue
      (shiftRow m w.residue w.shift w.original).a
      (shiftRow m w.residue w.shift w.original).b
      (shiftRow m w.residue w.shift w.original).c := by
  exact (shiftRow_giant m w.residue w.shift w.original).symm

/-- A bounded integer cannot have a residue outside both ends of the
short signed window. The sign and endpoint cases remain explicit. -/
theorem emod_short_window {d M i : ℤ} (hd : M<d) (hi : |i|≤M) :
    i%d≤M ∨ d-i%d≤M := by
  have hib := abs_le.mp hi
  by_cases hip : 0≤ i
  · left
    rw [Int.emod_eq_of_lt hip (by omega)]
    exact hib.2
  · right
    have hlo : 0≤ i+d := by omega
    have hhi : i+d<d := by omega
    have hmod : i%d=i+d := by
      have h := Int.emod_eq_of_lt hlo hhi
      simpa only [Int.add_emod_right] using h
    rw [hmod]
    omega

/-- Inverting the public stride modulo a certified order converts a
collision to its literal index residue. This is only a proof-side check. -/
theorem collision_index_modEq {G : Type*} [Group G] (g : G)
    {d m inv e i : ℤ} (horder : (orderOf g : ℤ)=d)
    (hinv : m^2*inv ≡ 1 [ZMOD d]) (hhit : g^e=g^(m^2*i)) :
    e*inv ≡ i [ZMOD d] := by
  have h : e ≡ m^2*i [ZMOD d] := by
    rw [←horder]
    exact zpow_eq_zpow_iff_modEq.mp hhit
  have hmul := h.mul_right inv
  have hi := hinv.mul_left i
  apply hmul.trans
  convert hi using 1 <;> ring

/-- A literal out-of-window index residue excludes every signed baby
collision, with no enumeration of all baby/giant pairs in the proof. -/
theorem no_short_collision {G : Type*} [Group G] (g : G)
    {d m inv e M : ℤ} (horder : (orderOf g : ℤ)=d) (hd : M<d)
    (hinv : m^2*inv ≡ 1 [ZMOD d])
    (hfar : M<(e*inv)%d ∧ (e*inv)%d+M<d) {i : ℤ} (hi : |i|≤M) :
    g^e≠g^(m^2*i) := by
  intro hhit
  have he := collision_index_modEq g horder hinv hhit
  have hm : (e*inv)%d=i%d := he
  have hwindow := emod_short_window hd hi
  rw [←hm] at hwindow
  omega

set_option maxRecDepth 32768 in
/-- The counterexample is a literal balanced semiprime; its modulus is
the first prime at or above the ceiling sixth root. -/
theorem control_arithmetic :
    Nat.Prime 14799739 ∧ Nat.Prime 24991489 ∧ Nat.Prime 269 ∧
      14799739*24991489=369867514421371 ∧
      14799739≤24991489 ∧ 24991489≤2*14799739 ∧
      (267 : ℕ)^6<369867514421371 ∧ 369867514421371≤(268 : ℕ)^6 ∧
      ¬Nat.Prime 268 ∧ 369867514421371≤(269 : ℕ)^6 ∧
      Nat.Coprime 269 369867514421371 := by
  norm_num [Nat.Coprime]

/-- Exact public base in the first control component; constructing the
base does not require that component in the N-only algorithm. -/
def controlBaseP : (ZMod 14799739)ˣ := ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 14799739)

/-- Exact base in the second control component, used only by the audit. -/
def controlBaseQ : (ZMod 24991489)ˣ := ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 24991489)

/-- Kernel-checked powers determining the first component's order. -/
theorem control_p_powers :
    (2 : ZMod 14799739)^4933246=1 ∧
      (2 : ZMod 14799739)^2466623≠1 ∧ (2 : ZMod 14799739)^2≠1 := by
  reduce_mod_char
  decide

/-- Kernel-checked powers for every prime divisor of the second order. -/
theorem control_q_powers :
    (2 : ZMod 24991489)^12495744=1 ∧
      (2 : ZMod 24991489)^6247872≠1 ∧
      (2 : ZMod 24991489)^4165248≠1 ∧
      (2 : ZMod 24991489)^1152≠1 := by
  reduce_mod_char
  decide

/-- Literal residue checker uses the two actual base orders. It tests
all retained public centered exponents, not just correct factor residues. -/
def controlFar (e : ℤ) : Bool :=
  decide (269<(e*3615823)%4933246 ∧ (e*3615823)%4933246+269<4933246 ∧
    269<(e*5350681)%12495744 ∧ (e*5350681)%12495744+269<12495744)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
/-- Every public intermediate row and both public center orientations
miss the complete short signed window in both control components. -/
theorem control_all_far :
    (publicExponents 369867514421371 269).all controlFar=true := by
  decide +kernel

/-- The first actual component order is proved from all its prime
divisor tests; a purported large order is never taken as algorithm advice. -/
theorem control_p_order : orderOf controlBaseP=4933246 := by
  have hv (k : ℕ) : (controlBaseP^k=1) ↔ (2 : ZMod 14799739)^k=1 := by
    rw [Units.ext_iff]
    simp only [controlBaseP,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Units.val_one,Nat.cast_ofNat]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) ((hv _).mpr control_p_powers.1)
  intro r hr hd
  have hdiv : r∣2*2466623 := hd
  have heq : r=2 ∨ r=2466623 := by
    rcases hr.dvd_mul.mp hdiv with h₂ | hlast
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h₂)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hlast)
  rcases heq with rfl | rfl
  · intro he
    exact control_p_powers.2.1 ((hv _).mp he)
  · intro he
    exact control_p_powers.2.2 ((hv _).mp he)

/-- The second order includes every prime-power component of the
literal order; neither saturation nor a short-period assumption is hidden. -/
theorem control_q_order : orderOf controlBaseQ=12495744 := by
  have hv (k : ℕ) : (controlBaseQ^k=1) ↔ (2 : ZMod 24991489)^k=1 := by
    rw [Units.ext_iff]
    simp only [controlBaseQ,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Units.val_one,Nat.cast_ofNat]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) ((hv _).mpr control_q_powers.1)
  intro r hr hd
  have hdiv : r∣2^7*3^2*10847 := hd
  have heq : r=2 ∨ r=3 ∨ r=10847 := by
    rcases hr.dvd_mul.mp hdiv with hfirst | hlast
    · rcases hr.dvd_mul.mp hfirst with h₂ | h₃
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp (hr.dvd_of_dvd_pow h₂))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp (hr.dvd_of_dvd_pow h₃)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hlast))
  rcases heq with rfl | rfl | rfl
  · intro he
    exact control_q_powers.2.1 ((hv _).mp he)
  · intro he
    exact control_q_powers.2.2.1 ((hv _).mp he)
  · intro he
    exact control_q_powers.2.2.2 ((hv _).mp he)

/-- The public m-squared baby bases have large actual orders in both
components, so the native failure is not short-period setup saturation. -/
theorem control_baby_orders :
    orderOf (controlBaseP^(269 : ℕ)^2)=4933246 ∧
      orderOf (controlBaseQ^(269 : ℕ)^2)=12495744 := by
  have hp : (orderOf controlBaseP).Coprime (269^2) := by
    rw [control_p_order]
    norm_num [Nat.Coprime]
  have hq : (orderOf controlBaseQ).Coprime (269^2) := by
    rw [control_q_order]
    norm_num [Nat.Coprime]
  exact ⟨hp.orderOf_pow.trans control_p_order,hq.orderOf_pow.trans control_q_order⟩

/-- Every actual centered public giant misses every signed short baby
in BOTH actual factor fields, including all incorrect residue aliases. -/
theorem control_no_short_collisions {e i : ℤ}
    (he : e∈publicExponents 369867514421371 269) (hi : |i|≤269) :
    controlBaseP^e≠controlBaseP^((269 : ℤ)^2*i) ∧
      controlBaseQ^e≠controlBaseQ^((269 : ℤ)^2*i) := by
  have hcheck := List.all_eq_true.mp control_all_far e he
  have hfar : 269<(e*3615823)%4933246 ∧ (e*3615823)%4933246+269<4933246 ∧
      269<(e*5350681)%12495744 ∧ (e*5350681)%12495744+269<12495744 :=
    of_decide_eq_true hcheck
  have hinvP : (269 : ℤ)^2*3615823 ≡ 1 [ZMOD 4933246] := by norm_num [Int.ModEq]
  have hinvQ : (269 : ℤ)^2*5350681 ≡ 1 [ZMOD 12495744] := by norm_num [Int.ModEq]
  have horderP : (orderOf controlBaseP : ℤ)=4933246 := by rw [control_p_order]; norm_num
  have horderQ : (orderOf controlBaseQ : ℤ)=12495744 := by rw [control_q_order]; norm_num
  exact ⟨no_short_collision controlBaseP horderP (by norm_num) hinvP
    ⟨hfar.1,hfar.2.1⟩ hi,
    no_short_collision controlBaseQ horderQ (by norm_num) hinvQ hfar.2.2 hi⟩

/-- The literal public base is constructed modulo N with only N and 2.
The factor fields enter solely in the downstream audit proofs. -/
def controlBase : (ZMod (14799739*24991489))ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num [Nat.Coprime] : Nat.Coprime 2 (14799739*24991489))

/-- Mapping a unit's signed power retains the original exponent. -/
theorem map_unit_zpow {R S : Type*} [CommRing R] [CommRing S]
    (φ : R→+*S) (g : Rˣ) (e : ℤ) :
    φ ((g^e : Rˣ) : R)=(((Units.map φ.toMonoidHom g)^e : Sˣ) : S) := by
  change ((Units.map φ.toMonoidHom (g^e) : Sˣ) : S)=_
  rw [map_zpow]

/-- The actual N-only base reduces to the first checked component base. -/
theorem control_base_left : SemiprimeLocalOrderRouting.leftUnit controlBase=controlBaseP := by
  apply Units.ext
  simp only [controlBaseP,ZMod.coe_unitOfCoprime]
  apply SemiprimeLocalOrderRouting.leftUnit_natCast
  simp [controlBase]

/-- The same public base supplies the second actual component. -/
theorem control_base_right : SemiprimeLocalOrderRouting.rightUnit controlBase=controlBaseQ := by
  apply Units.ext
  simp only [controlBaseQ,ZMod.coe_unitOfCoprime]
  apply SemiprimeLocalOrderRouting.rightUnit_natCast
  simp [controlBase]

/-- A literal public giant/baby residual, with its source upstream. -/
def controlResidual (e i : ℤ) : ZMod (14799739*24991489) :=
  ((controlBase^e : (ZMod (14799739*24991489))ˣ) : ZMod (14799739*24991489))-
    ((controlBase^((269 : ℤ)^2*i) : (ZMod (14799739*24991489))ˣ) : ZMod (14799739*24991489))

/-- Every original public residual in this proposed short window is a
unit. The failure is certified over the actual semiprime ring. -/
theorem control_residual_isUnit {e i : ℤ}
    (he : e∈publicExponents 369867514421371 269) (hi : |i|≤269) :
    IsUnit (controlResidual e i) := by
  have hmiss := control_no_short_collisions he hi
  apply SemiprimeIntervalJet.isUnit_of_prime_reductions control_arithmetic.1 control_arithmetic.2.1
  · rw [controlResidual,map_sub,map_unit_zpow,map_unit_zpow]
    change ((SemiprimeLocalOrderRouting.leftUnit controlBase^e : (ZMod 14799739)ˣ) : ZMod 14799739)-
      ((SemiprimeLocalOrderRouting.leftUnit controlBase^((269 : ℤ)^2*i) : (ZMod 14799739)ˣ) : ZMod 14799739)≠0
    rw [control_base_left]
    intro hz
    exact hmiss.1 (Units.ext (sub_eq_zero.mp hz))
  · rw [controlResidual,map_sub,map_unit_zpow,map_unit_zpow]
    change ((SemiprimeLocalOrderRouting.rightUnit controlBase^e : (ZMod 24991489)ˣ) : ZMod 24991489)-
      ((SemiprimeLocalOrderRouting.rightUnit controlBase^((269 : ℤ)^2*i) : (ZMod 24991489)ˣ) : ZMod 24991489)≠0
    rw [control_base_right]
    intro hz
    exact hmiss.2 (Units.ext (sub_eq_zero.mp hz))

/-- The entire public scalar column is retained as a product, rather
than a signed sum that could erase original collisions. -/
def controlColumn (i : ℤ) : ZMod (14799739*24991489) :=
  ((publicExponents 369867514421371 269).map (fun e => controlResidual e i)).prod

/-- Every product column of the proposed short detector is a unit.
There is no hidden original hit for a cancellation to recover here. -/
theorem control_column_isUnit {i : ℤ} (hi : |i|≤269) : IsUnit (controlColumn i) := by
  apply List.prod_isUnit
  intro x hx
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
  exact control_residual_isUnit he hi

/-- All aggregate GCD outputs in the literal short window are 1.
This is a fixed-family counterexample, not a general one-sixth no-go. -/
theorem control_column_gcd_one {i : ℤ} (hi : |i|≤269) :
    (14799739*24991489).gcd (controlColumn i).val=1 := by
  let : NeZero (14799739*24991489) := ⟨by norm_num⟩
  exact (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr (control_column_isUnit hi)

end RiemannGaussian.SemiprimeEuclidRowFamily
