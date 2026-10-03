/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowDerivative
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-!
# Exact local-order certificates for row derivative coverage

Sorting exponent residues and checking adjacent strict inequalities gives
a kernel-checkable certificate for the full collision-free public family.
No quadratic pair scan, probabilistic inference or compiler proof oracle
is used. This concerns the fixed positive-power family; inverse powers,
other public bases and other row constructions can have additional hits.
-/

namespace RiemannGaussian.SemiprimeDerivativeCoverage

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
  SemiprimeRowDerivative

/-- A linear adjacent-comparison pass, following a retained head. -/
def chainLT (a : ℤ) : List ℤ → Bool
  | [] => true
  | b::tail => decide (a<b) && chainLT b tail

theorem chainLT_sound {a : ℤ} {tail : List ℤ} (h : chainLT a tail=true) :
    (a::tail).IsChain (·<·) := by
  induction tail generalizing a with
  | nil => exact List.isChain_singleton _
  | cons b tail ih =>
    simp only [chainLT, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.isChain_cons_cons.mpr ⟨h.1,ih h.2⟩

/-- Structurally recursive merge used solely for kernel certificates.
Even insufficient fuel preserves the input multiset. -/
def mergeFuel : ℕ → List ℤ → List ℤ → List ℤ
  | 0, xs, ys => xs++ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | fuel+1, x::xs, y::ys =>
    if x≤y then x::mergeFuel fuel xs (y::ys) else y::mergeFuel fuel (x::xs) ys

theorem mergeFuel_perm (fuel : ℕ) (xs ys : List ℤ) :
    (mergeFuel fuel xs ys).Perm (xs++ys) := by
  induction fuel generalizing xs ys with
  | zero => rfl
  | succ fuel ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        rw [mergeFuel]
        split_ifs with h
        · exact (ih xs (y::ys)).cons x
        · exact ((ih (x::xs) ys).cons y).trans List.perm_middle.symm

/-- Balanced splitting with structural depth, avoiding proof-dependent
well-founded recursion in the audit's kernel reduction. -/
def sortFuel : ℕ → List ℤ → List ℤ
  | 0, xs => xs
  | depth+1, xs =>
    if xs.length≤1 then xs else
      let cut := (xs.length+1)/2
      mergeFuel xs.length (sortFuel depth (xs.take cut)) (sortFuel depth (xs.drop cut))

theorem sortFuel_perm (depth : ℕ) (xs : List ℤ) : (sortFuel depth xs).Perm xs := by
  induction depth generalizing xs with
  | zero => rfl
  | succ depth ih =>
    rw [sortFuel]
    split_ifs with h
    · rfl
    · exact (mergeFuel_perm _ _ _).trans
        (((ih _).append (ih _)).trans (List.Perm.of_eq (List.take_append_drop _ _)))

/-- A complete audit sort with a public list-length depth. Correctness
of a successful certificate needs only the proved permutation property. -/
def auditSort (xs : List ℤ) : List ℤ := sortFuel (xs.length.log2+1) xs

theorem auditSort_perm (xs : List ℤ) : (auditSort xs).Perm xs := sortFuel_perm _ _

/-- A collision-free residue certificate computes a sort and one scan.
Its cost is an audit cost, not the public factorizer's source budget. -/
def checkedResidues (d : ℤ) (es : List ℤ) : Bool :=
  match auditSort (es.map (fun e => e%d)) with
  | [] => true
  | a::tail => chainLT a tail

/-- Checking adjacent inequalities after sorting certifies every pair,
without using a quadratic all-pairs Boolean certificate. -/
theorem checkedResidues_nodup {d : ℤ} {es : List ℤ}
    (h : checkedResidues d es=true) : (es.map (fun e => e%d)).Nodup := by
  have hc : (auditSort (es.map (fun e => e%d))).IsChain (·<·) := by
    cases hs : auditSort (es.map (fun e => e%d)) with
    | nil => exact List.isChain_nil
    | cons a tail =>
      exact chainLT_sound (by simpa only [checkedResidues,hs] using h)
  have hp := (List.isChain_iff_pairwise).mp hc
  exact (auditSort_perm _).nodup_iff.mp (hp.imp (fun hab => ne_of_lt hab))

theorem checkedResidues_injective {d : ℤ} {es : List ℤ}
    (h : checkedResidues d es=true) {e f : ℤ} (he : e ∈ es) (hf : f ∈ es)
    (hm : e%d=f%d) : e=f :=
  List.inj_on_of_nodup_map (checkedResidues_nodup h) he hf hm

/-- A certified actual order transports the residue certificate to all
retained public powers. Equal local powers force equal source exponents. -/
theorem checkedResidues_power_injective {G : Type*} [Group G] (g : G)
    {d : ℤ} (hd : (orderOf g : ℤ)=d) {es : List ℤ}
    (h : checkedResidues d es=true) {e f : ℤ} (he : e ∈ es) (hf : f ∈ es)
    (hh : g^e=g^f) : e=f := by
  apply checkedResidues_injective h he hf
  have hm := zpow_eq_zpow_iff_modEq.mp hh
  rwa [hd] at hm

/-- Both actual component certificates prove exhaustion of the complete
public derivative observable. No prime field or order is source advice. -/
theorem publicRows_none_of_checked_orders {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (g : (ZMod (p*q))ˣ)
    {dP dQ : ℤ}
    (hP : (orderOf (SemiprimeLocalOrderRouting.leftUnit g) : ℤ)=dP)
    (hQ : (orderOf (SemiprimeLocalOrderRouting.rightUnit g) : ℤ)=dQ)
    (hcP : checkedResidues dP (publicExponents (p*q) m)=true)
    (hcQ : checkedResidues dQ (publicExponents (p*q) m)=true) :
    recoverRows (publicRoots m g)=none := by
  apply (recoverRows_none_iff_prime_separation hp hq _).mpr
  intro t ht x hx hne
  obtain ⟨wt,hwt,rfl⟩ := (publicRoots_mem_iff g t).mp ht
  obtain ⟨wx,hwx,rfl⟩ := (publicRoots_mem_iff g x).mp hx
  have het : packetExponent m wt ∈ publicExponents (p*q) m :=
    List.mem_map.mpr ⟨wt,hwt,rfl⟩
  have hex : packetExponent m wx ∈ publicExponents (p*q) m :=
    List.mem_map.mpr ⟨wx,hwx,rfl⟩
  constructor
  · intro he
    rw [map_unit_zpow, map_unit_zpow] at he
    have he' := Units.ext he
    have hsame := checkedResidues_power_injective (SemiprimeLocalOrderRouting.leftUnit g)
      hP hcP het hex he'
    exact hne (by rw [hsame])
  · intro he
    rw [map_unit_zpow, map_unit_zpow] at he
    have he' := Units.ext he
    have hsame := checkedResidues_power_injective (SemiprimeLocalOrderRouting.rightUnit g)
      hQ hcQ het hex he'
    exact hne (by rw [hsame])

set_option maxRecDepth 32768 in
/-- The stress input is a literal balanced semiprime, with the actual
public first-prime modulus and its sixth-root rounding checked. -/
theorem control_arithmetic :
    Nat.Prime 39167077933 ∧ Nat.Prime 64308254573 ∧ Nat.Prime 3691 ∧
      39167077933*64308254573=2518766418595894637609 ∧
      39167077933≤64308254573 ∧ 64308254573≤2*39167077933 ∧
      (3688 : ℕ)^6<2518766418595894637609 ∧
      2518766418595894637609≤(3689 : ℕ)^6 ∧
      ¬Nat.Prime 3689 ∧ ¬Nat.Prime 3690 ∧
      Nat.Coprime 3691 2518766418595894637609 := by
  norm_num [Nat.Coprime]

/-- The N-only public base; constructing it uses no factor field. -/
def controlBase : (ZMod (39167077933*64308254573))ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 (39167077933*64308254573))

/-- Actual first component, used only in the downstream certificate. -/
def controlBaseP : (ZMod 39167077933)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 39167077933)

/-- Actual second component, used only in the downstream certificate. -/
def controlBaseQ : (ZMod 64308254573)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 64308254573)

theorem control_p_powers :
    (2 : ZMod 39167077933)^39167077932=1 ∧
      (2 : ZMod 39167077933)^19583538966≠1 ∧
      (2 : ZMod 39167077933)^13055692644≠1 ∧
      (2 : ZMod 39167077933)^324≠1 := by
  reduce_mod_char
  decide

theorem control_q_powers :
    (2 : ZMod 64308254573)^64308254572=1 ∧
      (2 : ZMod 64308254573)^32154127286≠1 ∧
      (2 : ZMod 64308254573)^1495540804≠1 ∧
      (2 : ZMod 64308254573)^172≠1 := by
  reduce_mod_char
  decide

set_option maxRecDepth 32768 in
theorem control_p_order : orderOf controlBaseP=39167077932 := by
  have hv (k : ℕ) : (controlBaseP^k=1) ↔ (2 : ZMod 39167077933)^k=1 := by
    rw [Units.ext_iff]
    simp only [controlBaseP, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
      Units.val_one, Nat.cast_ofNat]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) ((hv _).mpr control_p_powers.1)
  intro r hr hd
  have hdiv : r∣2^2*3^4*120886043 := hd
  have heq : r=2 ∨ r=3 ∨ r=120886043 := by
    rcases hr.dvd_mul.mp hdiv with hsmall | hlast
    · rcases hr.dvd_mul.mp hsmall with htwo | hthree
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp (hr.dvd_of_dvd_pow htwo))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp (hr.dvd_of_dvd_pow hthree)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hlast))
  rcases heq with rfl | rfl | rfl
  · intro he; exact control_p_powers.2.1 ((hv _).mp he)
  · intro he; exact control_p_powers.2.2.1 ((hv _).mp he)
  · intro he; exact control_p_powers.2.2.2 ((hv _).mp he)

set_option maxRecDepth 32768 in
theorem control_q_order : orderOf controlBaseQ=64308254572 := by
  have hv (k : ℕ) : (controlBaseQ^k=1) ↔ (2 : ZMod 64308254573)^k=1 := by
    rw [Units.ext_iff]
    simp only [controlBaseQ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
      Units.val_one, Nat.cast_ofNat]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) ((hv _).mpr control_q_powers.1)
  intro r hr hd
  have hdiv : r∣2^2*43*373885201 := hd
  have heq : r=2 ∨ r=43 ∨ r=373885201 := by
    rcases hr.dvd_mul.mp hdiv with hsmall | hlast
    · rcases hr.dvd_mul.mp hsmall with htwo | hforty
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp (hr.dvd_of_dvd_pow htwo))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hforty))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hlast))
  rcases heq with rfl | rfl | rfl
  · intro he; exact control_q_powers.2.1 ((hv _).mp he)
  · intro he; exact control_q_powers.2.2.1 ((hv _).mp he)
  · intro he; exact control_q_powers.2.2.2 ((hv _).mp he)

theorem control_base_left : SemiprimeLocalOrderRouting.leftUnit controlBase=controlBaseP := by
  apply Units.ext
  simp only [controlBaseP, ZMod.coe_unitOfCoprime]
  apply SemiprimeLocalOrderRouting.leftUnit_natCast
  simp [controlBase]

theorem control_base_right : SemiprimeLocalOrderRouting.rightUnit controlBase=controlBaseQ := by
  apply Units.ext
  simp only [controlBaseQ, ZMod.coe_unitOfCoprime]
  apply SemiprimeLocalOrderRouting.rightUnit_natCast
  simp [controlBase]

/-- Closed public box values are proved once before reducing the entire
family; they are arithmetic certificates, not private factor hints. -/
theorem control_box :
    (2518766418595894637609/2 : ℕ).sqrt=35487789580 ∧
      (2518766418595894637609 : ℕ).sqrt=50187313323 ∧
      (2*2518766418595894637609 : ℕ).sqrt=70975579160 := by
  decide +kernel

/-- The structural certificate checker reduces in the kernel. This small
control certifies implementation soundness, not the large public family. -/
theorem checker_control : checkedResidues 5 [3,1,2]=true := by
  decide +kernel

end RiemannGaussian.SemiprimeDerivativeCoverage
