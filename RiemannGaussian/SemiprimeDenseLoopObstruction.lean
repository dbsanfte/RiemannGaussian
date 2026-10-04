/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeDenseRowCarries
import RiemannGaussian.SemiprimeLocalOrderRouting
import Mathlib.GroupTheory.OrderOfElement

/-!
# The dense row's public loop and its short-window obstruction

The length-m loop is fixed by a public cofactor residue. After a bounded
phase adjustment it is just g^(m*(N-k)). Replacing the floor-filtered
source by these loops loses its short-index forcing: an explicit factor-gap
band excludes every loop/baby collision at full local orders. This is a
failure of the loop-only shortcut, not of the dense coverage theorem or
all implicit acquisition algorithms.
-/

namespace RiemannGaussian.SemiprimeDenseLoopObstruction

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries

/-- The public cofactor residue attached to an actual seed. -/
def cofactorResidue (N m j : ℕ) : ℕ := (representative N m j 1*j)%m

/-- The exact exponent of one complete length-m loop of the implicit curve. -/
def loopExponent (N m j : ℕ) : ℤ :=
  (m : ℤ)*giantExponent m j (seedRow N m j).a (seedRow N m j).b (seedRow N m j).c-
    (representative N m j 1 : ℤ)*(m : ℤ)*(1-(j : ℤ))

/-- Bounded public phase removed from the complete loop. -/
def loopPhase (N m j : ℕ) : ℤ :=
  (seedRow N m j).b-(representative N m j 1*j/m : ℕ)

/-- The normalized loop retains its target shift explicitly. -/
def normalizedLoopExponent (N m j : ℕ) : ℤ :=
  loopExponent N m j-(m : ℤ)^2*loopPhase N m j

/-- The implicit word repeats with this exact multiplicative loop, rather
than with an unproved periodic or ordinary-geometric identity. -/
theorem progression_loop {G : Type*} [CommGroup G] (g : G)
    {N m j t : ℕ} (hm : 0<m) (negative : Bool) :
    progressionValue m (t+m) negative (progressionSeed g N m j)=
      progressionValue m t negative (progressionSeed g N m j)*g^loopExponent N m j := by
  have hd : representative N m j 1*(t+m)/m=
      representative N m j 1*t/m+representative N m j 1 := by
    simpa only [Nat.mul_add,Nat.add_mul,Nat.mul_comm] using
      Nat.add_mul_div_left (representative N m j 1*t) (representative N m j 1) hm
  have hk : leadingCarry N m j (t+m) negative=
      leadingCarry N m j t negative+representative N m j 1 := by
    unfold leadingCarry
    rw [hd]
    omega
  rw [progressionValue_eq,progressionValue_eq,←zpow_add]
  congr 1
  unfold reducedExponent loopExponent
  rw [hk,Nat.cast_add,Nat.cast_add]
  ring

/-- The actual loop collapses to one cofactor-residue power after the
public phase adjustment. No factor or local order is used in this identity. -/
theorem normalizedLoopExponent_eq {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    normalizedLoopExponent N m j=(m : ℤ)*((N : ℤ)-cofactorResidue N m j) := by
  have hs := denseRow_relation (N:=N) (t:=1) hm hj false
  change quotientRelation N m j (seedRow N m j).a (seedRow N m j).b
    (seedRow N m j).c 1 at hs
  have he := giantExponent_eq hs
  have ha : (seedRow N m j).a=(representative N m j 1 : ℤ) := rfl
  rw [ha,one_mul] at he
  have hd : (cofactorResidue N m j : ℤ)+
      (m : ℤ)*(representative N m j 1*j/m : ℕ)=
        (representative N m j 1 : ℤ)*j := by
    exact_mod_cast Nat.mod_add_div (representative N m j 1*j) m
  unfold normalizedLoopExponent loopExponent loopPhase
  rw [ha,he]
  linear_combination (m : ℤ)*hd

/-- Normalizing the complete loop only shifts the target by a linear
public amount; this does not recover the intermediate short collision. -/
theorem loopPhase_bound {N m j : ℕ} (hm : 1<m) (hjm : j<m) :
    |loopPhase N m j|≤2*(m : ℤ) := by
  have hu : representative N m j 1<m := Nat.mod_lt _ (by omega)
  have hd : representative N m j 1*j/m<m := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0<m)).mpr
    nlinarith only [hu,hjm]
  have hb := abs_le.mp (denseRow_b_bound (N:=N) (j:=j) (t:=1) hm false)
  change -(m : ℤ)≤(seedRow N m j).b ∧ (seedRow N m j).b≤m at hb
  have hdz : ((representative N m j 1*j/m : ℕ) : ℤ)<m := by exact_mod_cast hd
  have hd₀ : (0 : ℤ)≤(representative N m j 1*j/m : ℕ) := by positivity
  unfold loopPhase
  apply abs_le.mpr
  constructor <;> omega

/-- A multiple of D cannot lie strictly between two consecutive multiples. -/
theorem no_divisor_in_open_period {D h x : ℤ} (hD : 0<D)
    (hlo : h*D<x) (hhi : x<(h+1)*D) : ¬D∣x := by
  rintro ⟨z,hz⟩
  have hl : h<z := by nlinarith only [hD,hlo,hz]
  have hh : z<h+1 := by nlinarith only [hD,hhi,hz]
  omega

/-- A whole band of cofactor values misses every short normalized loop
at a full local order coprime to m. Every residue k<m is excluded. -/
theorem normalized_loop_no_hit {G : Type*} [CommGroup G] (g : G)
    {p q m k R h : ℕ} (hp : 1<p) (horder : orderOf g=p-1)
    (hcop : m.Coprime (p-1)) (hk : k<m) {I : ℤ} (hI : I.natAbs≤R)
    (hlo : h*(p-1)+m*(R+1)<q)
    (hhi : q+m*(R+1)<(h+1)*(p-1)) :
    g^((m : ℤ)*((p : ℤ)*q-k))≠g^((m : ℤ)^2*I) := by
  intro he
  have hd := (orderOf_dvd_sub_iff_zpow_eq_zpow).mpr he
  rw [horder] at hd
  have hd' : ((p-1 : ℕ) : ℤ)∣(m : ℤ)*((p : ℤ)*q-k-m*I) := by
    convert hd using 1
    ring
  have hc := hcop.symm.isCoprime.dvd_of_dvd_mul_left hd'
  have hN : ((p-1 : ℕ) : ℤ)∣(p : ℤ)*q-q := by
    refine ⟨(q : ℤ),?_⟩
    rw [Nat.cast_sub hp.le,Nat.cast_one]
    ring
  have hdiv : ((p-1 : ℕ) : ℤ)∣(q : ℤ)-k-m*I := by
    convert hc.sub hN using 1 <;> first | rfl | ring
  have hIb : -(R : ℤ)≤I ∧ I≤R := by
    apply abs_le.mp
    rw [←Int.natCast_natAbs]
    exact_mod_cast hI
  have hIz₀ := mul_le_mul_of_nonneg_left hIb.1 (by positivity : (0 : ℤ)≤m)
  have hIz₁ := mul_le_mul_of_nonneg_left hIb.2 (by positivity : (0 : ℤ)≤m)
  have hl : (h : ℤ)*((p-1 : ℕ) : ℤ)+(m : ℤ)*((R : ℤ)+1)<q := by
    exact_mod_cast hlo
  have hh : (q : ℤ)+(m : ℤ)*((R : ℤ)+1)<((h : ℤ)+1)*((p-1 : ℕ) : ℤ) := by
    exact_mod_cast hhi
  have hkz : (k : ℤ)<m := by exact_mod_cast hk
  have hpD : (0 : ℤ)<(p-1 : ℕ) := by exact_mod_cast (by omega : 0<p-1)
  exact no_divisor_in_open_period (D:=((p-1 : ℕ) : ℤ)) (h:=(h : ℤ))
    (x:=(q : ℤ)-k-m*I) hpD
    (by nlinarith only [hl,hIz₁,hkz])
    (by nlinarith only [hh,hIz₀,show (0 : ℤ)≤k from by positivity]) hdiv

/-- The raw seed loop also misses the linear window when the gap band
is padded for its complete public phase. -/
theorem raw_seed_loop_no_hit {G : Type*} [CommGroup G] (g : G)
    {p q m j R h : ℕ} (hm : 1<m) (hp : 1<p) (hj : j.Coprime m) (hjm : j<m)
    (horder : orderOf g=p-1) (hcop : m.Coprime (p-1)) {I : ℤ} (hI : I.natAbs≤R)
    (hlo : h*(p-1)+m*(R+2*m+1)<q)
    (hhi : q+m*(R+2*m+1)<(h+1)*(p-1)) :
    g^loopExponent (p*q) m j≠g^((m : ℤ)^2*I) := by
  have hm₀ : 0<m := by omega
  have hc := loopPhase_bound (N:=p*q) hm hjm
  intro he
  have ht : g^normalizedLoopExponent (p*q) m j=
      g^((m : ℤ)^2*(I-loopPhase (p*q) m j)) := by
    unfold normalizedLoopExponent
    rw [zpow_sub,he]
    rw [←zpow_sub]
    congr 1
    ring
  have htarget : (I-loopPhase (p*q) m j).natAbs≤R+2*m := by
    have hab : |I|≤(R : ℤ) := by
      rw [←Int.natCast_natAbs]
      exact_mod_cast hI
    have hs := abs_sub I (loopPhase (p*q) m j)
    have hb : |I-loopPhase (p*q) m j|≤((R+2*m : ℕ) : ℤ) := by
      push_cast
      linarith only [hab,hc,hs]
    rw [←Int.natCast_natAbs] at hb
    exact_mod_cast hb
  rw [normalizedLoopExponent_eq hm₀ hj] at ht
  have hno := normalized_loop_no_hit g (p:=p) (q:=q) (m:=m)
    (k:=cofactorResidue (p*q) m j) (R:=R+2*m) (h:=h) hp horder hcop
    (Nat.mod_lt _ hm₀) htarget hlo hhi
  exact hno (by simpa only [Nat.cast_mul] using ht)

set_option maxRecDepth 32768 in
/-- This balanced negative control uses exactly the canonical sixth-root
prime, with all prime and coprimality claims checked by the kernel. -/
theorem control_arithmetic :
    Nat.Prime 1000003 ∧ Nat.Prime 1500007 ∧ Nat.Prime 107 ∧
      1000003*1500007=1500011500021 ∧
      1000003≤1500007 ∧ 1500007≤2*1000003 ∧
      (106 : ℕ)^6<1500011500021 ∧ 1500011500021≤(107 : ℕ)^6 ∧
      Nat.Coprime 107 1500011500021 := by
  norm_num [Nat.Coprime]

/-- The literal public base used solely for auditing the failed shortcut. -/
def controlBase : (ZMod (1000003*1500007))ˣ :=
  ZMod.unitOfCoprime 11 (by norm_num [Nat.Coprime] : Nat.Coprime 11 (1000003*1500007))

/-- First component of the same public base, used only in the proof. -/
def controlBaseP : (ZMod 1000003)ˣ :=
  ZMod.unitOfCoprime 11 (by norm_num : Nat.Coprime 11 1000003)

/-- Second component of the same public base, used only in the proof. -/
def controlBaseQ : (ZMod 1500007)ˣ :=
  ZMod.unitOfCoprime 11 (by norm_num : Nat.Coprime 11 1500007)

/-- All prime-divisor power tests for the first full local order. -/
theorem control_p_powers :
    (11 : ZMod 1000003)^1000002=1 ∧
      (11 : ZMod 1000003)^500001≠1 ∧
      (11 : ZMod 1000003)^333334≠1 ∧ (11 : ZMod 1000003)^6≠1 := by
  reduce_mod_char
  decide

/-- All prime-divisor power tests for the second full local order. -/
theorem control_q_powers :
    (11 : ZMod 1500007)^1500006=1 ∧
      (11 : ZMod 1500007)^750003≠1 ∧
      (11 : ZMod 1500007)^500002≠1 ∧
      (11 : ZMod 1500007)^28302≠1 ∧ (11 : ZMod 1500007)^16854≠1 := by
  reduce_mod_char
  decide

/-- The first local period is full, rather than assumed or inferred
from a few successful row examples. -/
theorem control_p_order : orderOf controlBaseP=1000002 := by
  have hv (k : ℕ) : (controlBaseP^k=1) ↔ (11 : ZMod 1000003)^k=1 := by
    rw [Units.ext_iff]
    simp only [controlBaseP,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,
      Units.val_one,Nat.cast_ofNat]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) ((hv _).mpr control_p_powers.1)
  intro r hr hd
  have hdiv : r∣2*3*166667 := hd
  have heq : r=2 ∨ r=3 ∨ r=166667 := by
    rcases hr.dvd_mul.mp hdiv with hfirst | hlast
    · rcases hr.dvd_mul.mp hfirst with h₂ | h₃
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h₂)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h₃))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hlast))
  rcases heq with rfl | rfl | rfl
  · intro he
    exact control_p_powers.2.1 ((hv _).mp he)
  · intro he
    exact control_p_powers.2.2.1 ((hv _).mp he)
  · intro he
    exact control_p_powers.2.2.2 ((hv _).mp he)

/-- The complete second local order includes every prime-power factor. -/
theorem control_q_order : orderOf controlBaseQ=1500006 := by
  have hv (k : ℕ) : (controlBaseQ^k=1) ↔ (11 : ZMod 1500007)^k=1 := by
    rw [Units.ext_iff]
    simp only [controlBaseQ,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,
      Units.val_one,Nat.cast_ofNat]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) ((hv _).mpr control_q_powers.1)
  intro r hr hd
  have hdiv : r∣2*3*53^2*89 := hd
  have heq : r=2 ∨ r=3 ∨ r=53 ∨ r=89 := by
    rcases hr.dvd_mul.mp hdiv with hfirst | hlast
    · rcases hr.dvd_mul.mp hfirst with hsmall | h₅₃
      · rcases hr.dvd_mul.mp hsmall with h₂ | h₃
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h₂)
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h₃))
      · exact Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp (hr.dvd_of_dvd_pow h₅₃))))
    · exact Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hlast)))
  rcases heq with rfl | rfl | rfl | rfl
  · intro he
    exact control_q_powers.2.1 ((hv _).mp he)
  · intro he
    exact control_q_powers.2.2.1 ((hv _).mp he)
  · intro he
    exact control_q_powers.2.2.2.1 ((hv _).mp he)
  · intro he
    exact control_q_powers.2.2.2.2 ((hv _).mp he)

/-- The arithmetic gap excludes every normalized loop residue in both
actual fields, throughout the full transported dense baby window. -/
theorem control_normalized_no_hits {k : ℕ} (hk : k<107) {I : ℤ}
    (hI : I.natAbs≤5*107+15) :
    controlBaseP^((107 : ℤ)*(1500011500021-k))≠controlBaseP^((107 : ℤ)^2*I) ∧
      controlBaseQ^((107 : ℤ)*(1500011500021-k))≠controlBaseQ^((107 : ℤ)^2*I) := by
  constructor
  · exact normalized_loop_no_hit controlBaseP (p:=1000003) (q:=1500007) (h:=1)
      (by norm_num) control_p_order (by norm_num [Nat.Coprime]) hk hI
      (by norm_num) (by norm_num)
  · exact normalized_loop_no_hit controlBaseQ (p:=1500007) (q:=1000003) (h:=0)
      (by norm_num) control_q_order (by norm_num [Nat.Coprime]) hk hI
      (by norm_num) (by norm_num)

/-- Every actual raw seed loop also misses both factor fields. The
bounded phase is paid explicitly, with no scan over rows or indices. -/
theorem control_raw_no_hits {j : ℕ} (hj : 0<j) (hjm : j<107) {I : ℤ}
    (hI : I.natAbs≤5*107+15) :
    controlBaseP^loopExponent 1500011500021 107 j≠controlBaseP^((107 : ℤ)^2*I) ∧
      controlBaseQ^loopExponent 1500011500021 107 j≠controlBaseQ^((107 : ℤ)^2*I) := by
  have hcop : j.Coprime 107 :=
    (Nat.coprime_comm.mp (control_arithmetic.2.2.1.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hj hjm)))
  constructor
  · exact raw_seed_loop_no_hit controlBaseP (p:=1000003) (q:=1500007) (h:=1)
      (by norm_num) (by norm_num) hcop hjm control_p_order
      (by norm_num [Nat.Coprime]) hI (by norm_num) (by norm_num)
  · exact raw_seed_loop_no_hit controlBaseQ (p:=1500007) (q:=1000003) (h:=0)
      (by norm_num) (by norm_num) hcop hjm control_q_order
      (by norm_num [Nat.Coprime]) hI (by norm_num) (by norm_num)

/-- Both choices of loop compression are retained for the negative audit. -/
def controlLoopExponent (normalized : Bool) (j : ℕ) : ℤ :=
  if normalized then normalizedLoopExponent 1500011500021 107 j
  else loopExponent 1500011500021 107 j

/-- The two actual loop constructions miss, including every incorrect
residue alias. This follows from the gap theorem rather than enumeration. -/
theorem control_no_hits {j : ℕ} (hj : 0<j) (hjm : j<107) {I : ℤ}
    (hI : I.natAbs≤5*107+15) (normalized : Bool) :
    controlBaseP^controlLoopExponent normalized j≠controlBaseP^((107 : ℤ)^2*I) ∧
      controlBaseQ^controlLoopExponent normalized j≠controlBaseQ^((107 : ℤ)^2*I) := by
  cases normalized
  · exact control_raw_no_hits hj hjm hI
  · have hcop : j.Coprime 107 :=
      (control_arithmetic.2.2.1.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt hj hjm)).symm
    simp only [controlLoopExponent,ite_true,
      normalizedLoopExponent_eq (by norm_num : 0<107) hcop]
    exact control_normalized_no_hits (Nat.mod_lt _ (by norm_num)) hI

/-- The original public base has the first audited prime reduction. -/
theorem control_base_left :
    SemiprimeLocalOrderRouting.leftUnit controlBase=controlBaseP := by
  apply Units.ext
  simp only [controlBaseP,ZMod.coe_unitOfCoprime]
  apply SemiprimeLocalOrderRouting.leftUnit_natCast
  simp [controlBase]

/-- The same original public base has the second audited reduction. -/
theorem control_base_right :
    SemiprimeLocalOrderRouting.rightUnit controlBase=controlBaseQ := by
  apply Units.ext
  simp only [controlBaseQ,ZMod.coe_unitOfCoprime]
  apply SemiprimeLocalOrderRouting.rightUnit_natCast
  simp [controlBase]

/-- Signed unit powers commute with the actual residue maps. -/
theorem map_unit_zpow {R S : Type*} [CommRing R] [CommRing S]
    (φ : R→+*S) (g : Rˣ) (e : ℤ) :
    φ ((g^e : Rˣ) : R)=(((Units.map φ.toMonoidHom g)^e : Sˣ) : S) := by
  change ((Units.map φ.toMonoidHom (g^e) : Sˣ) : S)=_
  rw [map_zpow]

/-- Literal public residual for either loop choice. -/
def controlResidual (normalized : Bool) (j : ℕ) (I : ℤ) :
    ZMod (1000003*1500007) :=
  ((controlBase^controlLoopExponent normalized j : (ZMod (1000003*1500007))ˣ) :
      ZMod (1000003*1500007))-
    ((controlBase^((107 : ℤ)^2*I) : (ZMod (1000003*1500007))ˣ) :
      ZMod (1000003*1500007))

/-- Every public loop/baby residual is a unit, so no original hit is
concealed by product aggregation or factor-field saturation. -/
theorem control_residual_isUnit {j : ℕ} (hj : 0<j) (hjm : j<107) {I : ℤ}
    (hI : I.natAbs≤5*107+15) (normalized : Bool) :
    IsUnit (controlResidual normalized j I) := by
  have hmiss := control_no_hits hj hjm hI normalized
  apply SemiprimeIntervalJet.isUnit_of_prime_reductions
    control_arithmetic.1 control_arithmetic.2.1
  · rw [controlResidual,map_sub,map_unit_zpow,map_unit_zpow]
    change ((SemiprimeLocalOrderRouting.leftUnit controlBase^
      controlLoopExponent normalized j : (ZMod 1000003)ˣ) : ZMod 1000003)-
      ((SemiprimeLocalOrderRouting.leftUnit controlBase^((107 : ℤ)^2*I) :
        (ZMod 1000003)ˣ) : ZMod 1000003)≠0
    rw [control_base_left]
    intro hz
    exact hmiss.1 (Units.ext (sub_eq_zero.mp hz))
  · rw [controlResidual,map_sub,map_unit_zpow,map_unit_zpow]
    change ((SemiprimeLocalOrderRouting.rightUnit controlBase^
      controlLoopExponent normalized j : (ZMod 1500007)ˣ) : ZMod 1500007)-
      ((SemiprimeLocalOrderRouting.rightUnit controlBase^((107 : ℤ)^2*I) :
        (ZMod 1500007)ˣ) : ZMod 1500007)≠0
    rw [control_base_right]
    intro hz
    exact hmiss.2 (Units.ext (sub_eq_zero.mp hz))

/-- The complete public loop column retains the collision OR as a product. -/
def controlColumn (normalized : Bool) (I : ℤ) : ZMod (1000003*1500007) :=
  ((List.range 106).map (fun r => controlResidual normalized (r+1) I)).prod

/-- Every complete loop column is a unit over the actual semiprime ring. -/
theorem control_column_isUnit {I : ℤ} (hI : I.natAbs≤5*107+15)
    (normalized : Bool) : IsUnit (controlColumn normalized I) := by
  apply List.prod_isUnit
  intro x hx
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
  have hrb := List.mem_range.mp hr
  exact control_residual_isUnit (by omega) (by omega) hI normalized

/-- The complete detector returns only gcd 1, for every signed baby
index and both loop choices. This does not refute the dense source. -/
theorem control_column_gcd_one {I : ℤ} (hI : I.natAbs≤5*107+15)
    (normalized : Bool) :
    (1000003*1500007).gcd (controlColumn normalized I).val=1 := by
  let : NeZero (1000003*1500007) := ⟨by norm_num⟩
  exact (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr (control_column_isUnit hI normalized)

end RiemannGaussian.SemiprimeDenseLoopObstruction
