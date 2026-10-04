/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeDenseRowCoverage
import RiemannGaussian.SemiprimeQuotientCentering

/-!
# Exact carry representation of the dense collision source

One lifted seed per residue determines every dense row by two explicit
integer carries. The leading carry stays in the giant exponent. The
centering carry transports to the baby index, preserving the entire
residual up to a public unit and preserving the recovery quadratic.
This reduces the source to floor-filtered geometric progressions; it does
not pay the cost of finding a collision in their implicit union.
-/

namespace RiemannGaussian.SemiprimeDenseRowCarries

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeDenseRowCoverage

/-- The one actually lifted seed at each public residue. -/
def seedRow (N m j : ℕ) : QuotientRow := denseRow N m j 1 false

/-- The leading numerator reduction, including its emitted orientation. -/
def leadingCarry (N m j t : ℕ) (negative : Bool) : ℕ :=
  representative N m j 1*t/m+(if negative then 1 else 0)

/-- The uncentered linear coefficient needs only a seed and the leading carry. -/
def rawLinear (N m j t : ℕ) (negative : Bool) : ℤ :=
  (t : ℤ)*(seedRow N m j).b-(j : ℤ)*leadingCarry N m j t negative

/-- The exact integer floor used to center that linear coefficient. -/
def centeringCarry (N m j t : ℕ) (negative : Bool) : ℤ :=
  (rawLinear N m j t negative+(m/2 : ℕ))/(m : ℤ)

/-- The generator before centering has no per-denominator quotient lift. -/
def carryRow (N m j t : ℕ) (negative : Bool) : QuotientRow :=
  ⟨(t : ℤ)*(seedRow N m j).a-(m : ℤ)*leadingCarry N m j t negative,
    rawLinear N m j t negative,(t : ℤ)*(seedRow N m j).c,t,0⟩

/-- Retain the leading carry and move only the centering carry to the target. -/
def reducedExponent (N m j t : ℕ) (negative : Bool) : ℤ :=
  (t : ℤ)*giantExponent m j (seedRow N m j).a
    (seedRow N m j).b (seedRow N m j).c-
      (leadingCarry N m j t negative : ℤ)*(m : ℤ)*(1-(j : ℤ))

/-- Cached public data for one entire implicit geometric progression. -/
structure ProgressionSeed (G : Type*) where
  /-- The original residue used by recovery. -/
  residue : ℕ
  /-- The canonical numerator of the denominator-one seed. -/
  slope : ℕ
  /-- The centered linear coefficient of that seed. -/
  linear : ℤ
  /-- Its giant power. -/
  step : G
  /-- The leading-carry power, retained independently of centering. -/
  carryStep : G

/-- Build one cached descriptor, with exactly one quotient lift. -/
def progressionSeed {G : Type*} [CommGroup G] (g : G) (N m j : ℕ) :
    ProgressionSeed G :=
  let z := seedRow N m j
  ⟨j,representative N m j 1,z.b,
    g^giantExponent m j z.a z.b z.c,g^((m : ℤ)*(1-(j : ℤ)))⟩

/-- The public descriptor stream stores one seed at every original residue. -/
def progressionSeeds {G : Type*} [CommGroup G] (g : G) (N m : ℕ) :
    List (ProgressionSeed G) :=
  (List.range (m-1)).map fun r => progressionSeed g N m (r+1)

/-- Evaluate a requested denominator directly from the cached descriptor,
retaining the floor carry and both numerator orientations. -/
def progressionValue {G : Type*} [CommGroup G] (m t : ℕ) (negative : Bool)
    (s : ProgressionSeed G) : G :=
  s.step^t*s.carryStep^(-((s.slope*t/m+(if negative then 1 else 0) : ℕ) : ℤ))

/-- Candidate recovery uses the same cached descriptor and target index;
there is no full dense-row reconstruction or per-denominator lift. -/
def progressionRecovery {G : Type*} (N m t : ℕ) (negative : Bool)
    (s : ProgressionSeed G) (I : ℤ) : List ℤ :=
  let k := (s.slope*t/m+(if negative then 1 else 0) : ℕ)
  let a := (t : ℤ)*s.slope-(m : ℤ)*k
  let b := (t : ℤ)*s.linear-(s.residue : ℤ)*k
  integerRoots a (b*m-2*a*s.residue-(m : ℤ)^2*I) (t*N : ℕ)

/-- Equal modular classes have exactly the same centered representative. -/
theorem centered_congr {m : ℕ} {v w : ℤ} (h : v ≡ w [ZMOD m]) :
    centered m v=centered m w := by
  unfold centered
  rw [(h.add_right (m/2 : ℕ)).eq]

/-- Centering twice retains the actual coefficient. -/
theorem centered_idempotent (m : ℕ) (v : ℤ) :
    centered m (centered m v)=centered m v :=
  centered_congr (centered_modEq m v)

/-- Centering removes this explicit integer carry, with the literal floor
and tie convention of the source constructor. -/
theorem centered_exact_carry (m : ℕ) (v : ℤ) :
    centered m v=v-(m : ℤ)*((v+(m/2 : ℕ))/(m : ℤ)) := by
  have he := Int.emod_add_mul_ediv (v+(m/2 : ℕ)) (m : ℤ)
  unfold centered
  linear_combination he

/-- Reducing the seed numerator before multiplication retains every
canonical numerator in the dense source. -/
theorem representative_seed (N m j t : ℕ) :
    representative N m j t=(representative N m j 1*t)%m := by
  simp only [representative,Nat.mul_one,Nat.mul_mod,Nat.mod_mod]

/-- Every emitted leading coefficient is the seed multiple minus its
explicit leading carry; both numerator orientations are retained. -/
theorem denseRow_leading_carry (N m j t : ℕ) (negative : Bool) :
    (denseRow N m j t negative).a=
      (t : ℤ)*(seedRow N m j).a-(m : ℤ)*leadingCarry N m j t negative := by
  have hd := Nat.mod_add_div (representative N m j 1*t) m
  rw [←representative_seed] at hd
  have he : (representative N m j t : ℤ)+
      (m : ℤ)*(representative N m j 1*t/m : ℕ)=
        (representative N m j 1 : ℤ)*t := by exact_mod_cast hd
  simp only [Int.natCast_ediv,Nat.cast_mul] at he
  cases negative <;> simp [denseRow,liftRow,seedRow,leadingCarry]
  · linear_combination he
  · linear_combination he

/-- Removing a multiple of the public null direction (m,j,0) gives
another exact quotient row without constructing a matrix. -/
theorem carryRow_relation {N m j t : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (negative : Bool) :
    let z := carryRow N m j t negative
    quotientRelation N m j z.a z.b z.c z.t := by
  have hs := denseRow_relation (N:=N) (t:=1) hm hj false
  change quotientRelation N m j (seedRow N m j).a (seedRow N m j).b
    (seedRow N m j).c 1 at hs
  simp only [carryRow,rawLinear,quotientRelation] at ⊢
  unfold quotientRelation at hs
  linear_combination (t : ℤ)*hs

/-- Rows with the same numerator and denominator have the same linear
coefficient modulo m; the public inverse supplies the necessary cancellation. -/
theorem same_pair_linear_congruence {N m j : ℕ} (hm : 0<m)
    (hj : j.Coprime m) {u v : QuotientRow} (ha : u.a=v.a) (ht : u.t=v.t)
    (hu : quotientRelation N m j u.a u.b u.c u.t)
    (hv : quotientRelation N m j v.a v.b v.c v.t) : u.b ≡ v.b [ZMOD m] := by
  have hmz : (m : ℤ)≠0 := by exact_mod_cast hm.ne'
  have he : (m : ℤ)*(m*(v.c-u.c))=(m : ℤ)*(j*(v.b-u.b)) := by
    unfold quotientRelation at hu hv
    rw [ha,ht] at hu
    linear_combination hv-hu
  have he' := mul_left_cancel₀ hmz he
  have hd : (m : ℤ)∣(j : ℤ)*(v.b-u.b) := by
    rw [←he']
    exact dvd_mul_right _ _
  exact Int.modEq_of_dvd (hj.symm.isCoprime.dvd_of_dvd_mul_left hd)

/-- The actual dense linear coefficient equals the centered seed/carry
coefficient. This keeps the literal exact divisions in the original lift. -/
theorem denseRow_linear_centered {N m j t : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (negative : Bool) :
    (denseRow N m j t negative).b=centered m (rawLinear N m j t negative) := by
  have ha : (denseRow N m j t negative).a=(carryRow N m j t negative).a :=
    denseRow_leading_carry N m j t negative
  have hb := same_pair_linear_congruence hm hj ha rfl
    (denseRow_relation hm hj negative) (carryRow_relation hm hj negative)
  have he := centered_congr hb
  have hid : centered m (denseRow N m j t negative).b=
      (denseRow N m j t negative).b := by
    apply centered_idempotent
  rw [hid] at he
  exact he

/-- The second carry is transported through both retained coefficients. -/
theorem denseRow_linear_carry {N m j t : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (negative : Bool) :
    (denseRow N m j t negative).b=
      rawLinear N m j t negative-(m : ℤ)*centeringCarry N m j t negative := by
  rw [denseRow_linear_centered hm hj negative]
  exact centered_exact_carry m _

/-- The constant coefficient has precisely the same centering carry. -/
theorem denseRow_constant_carry {N m j t : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (negative : Bool) :
    (denseRow N m j t negative).c=
      (t : ℤ)*(seedRow N m j).c-(j : ℤ)*centeringCarry N m j t negative := by
  have hd := denseRow_relation (N:=N) (t:=t) hm hj negative
  have hs := denseRow_relation (N:=N) (t:=1) hm hj false
  change quotientRelation N m j (seedRow N m j).a (seedRow N m j).b
    (seedRow N m j).c 1 at hs
  dsimp only at hd
  unfold quotientRelation at hd hs
  rw [denseRow_leading_carry,denseRow_linear_carry hm hj negative] at hd
  simp only [rawLinear] at hd
  have ht : (denseRow N m j t negative).t=(t : ℤ) := rfl
  rw [ht] at hd
  apply mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hm.ne' : (m : ℤ)≠0))
  linear_combination hd-(t : ℤ)*hs

/-- Exact giant-exponent decomposition into one seed, the retained leading
carry, and the m² centering phase. -/
theorem denseRow_giant_carries {N m j t : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (negative : Bool) :
    giantExponent m j (denseRow N m j t negative).a
      (denseRow N m j t negative).b (denseRow N m j t negative).c=
        reducedExponent N m j t negative-
          (m : ℤ)^2*centeringCarry N m j t negative := by
  rw [denseRow_leading_carry,denseRow_linear_carry hm hj negative,
    denseRow_constant_carry hm hj negative]
  simp only [giantExponent,reducedExponent,rawLinear]
  ring

/-- The hidden index has two distinct transports: leading reduction costs
the unknown factor quotient x, while centering costs only its public carry. -/
theorem denseRow_index_carries {N m j t : ℕ} (hm : 0<m) (hj : j.Coprime m)
    (negative : Bool) {p x iSeed : ℤ} (hcoord : p=(m : ℤ)*x+j)
    (hseed : quadratic (seedRow N m j).a (seedRow N m j).b
      (seedRow N m j).c x=p*iSeed) :
    quadratic (denseRow N m j t negative).a (denseRow N m j t negative).b
        (denseRow N m j t negative).c x=
      p*((t : ℤ)*iSeed-(leadingCarry N m j t negative : ℤ)*x-
        centeringCarry N m j t negative) := by
  rw [denseRow_leading_carry,denseRow_linear_carry hm hj negative,
    denseRow_constant_carry hm hj negative]
  simp only [quadratic,rawLinear] at hseed ⊢
  linear_combination (t : ℤ)*hseed+
    ((leadingCarry N m j t negative : ℤ)*x+centeringCarry N m j t negative)*hcoord

/-- At each emitted positive denominator, the complete leading carry is
smaller than m, including the negative-numerator orientation. -/
theorem leadingCarry_bound {N m j t : ℕ} (hm : 0<m) (ht : 0<t)
    (htm : t<m) (negative : Bool) : leadingCarry N m j t negative<m := by
  have hu : representative N m j 1<m := Nat.mod_lt _ hm
  have hprod : representative N m j 1*t<t*m := by
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hu ht
  have hd : representative N m j 1*t/m<t := (Nat.div_lt_iff_lt_mul hm).mpr hprod
  cases negative <;> simp only [leadingCarry,Bool.false_eq_true,if_false,if_true]
  · omega
  · omega

/-- The centering carry has linear size. It can therefore be added to the
linear baby window instead of being dropped from the original target. -/
theorem centeringCarry_bound {N m j t : ℕ} (hm : 1<m) (hj : j.Coprime m)
    (hjm : j<m) (ht : 0<t) (htm : t<m) (negative : Bool) :
    |centeringCarry N m j t negative|≤2*(m : ℤ)+1 := by
  have hm₀ : 0<m := by omega
  have hmz : (0 : ℤ)<m := by exact_mod_cast hm₀
  have hs : |(seedRow N m j).b|≤(m : ℤ) := denseRow_b_bound hm false
  have hb := denseRow_b_bound (N:=N) (j:=j) (t:=t) hm negative
  have hk : (leadingCarry N m j t negative : ℤ)≤m := by
    exact_mod_cast (leadingCarry_bound hm₀ ht htm negative).le
  have htz : (t : ℤ)≤m := by exact_mod_cast htm.le
  have hjz : (j : ℤ)≤m := by exact_mod_cast hjm.le
  have hsb := abs_le.mp hs
  have hdb := abs_le.mp hb
  have htmul : (t : ℤ)*m≤(m : ℤ)^2 := by nlinarith only [htz,hmz]
  have hsb₀ := mul_le_mul_of_nonneg_left hsb.1 (by positivity : (0 : ℤ)≤t)
  have hsb₁ := mul_le_mul_of_nonneg_left hsb.2 (by positivity : (0 : ℤ)≤t)
  have hjk₀ : (0 : ℤ)≤(j : ℤ)*leadingCarry N m j t negative := by positivity
  have hjk₁ : (j : ℤ)*leadingCarry N m j t negative≤(m : ℤ)^2 := by
    have h := mul_le_mul hjz hk
      (by positivity : (0 : ℤ)≤leadingCarry N m j t negative)
      (by positivity : (0 : ℤ)≤m)
    simpa only [pow_two] using h
  have he := denseRow_linear_carry (N:=N) (t:=t) hm₀ hj negative
  unfold rawLinear at he
  apply abs_le.mpr
  constructor <;> nlinarith only [he,hdb.1,hdb.2,hsb₀,hsb₁,htmul,hjk₀,hjk₁,hmz]

/-- All original residuals survive as public unit multiples when the
centering carry is transferred to the baby exponent. -/
theorem denseRow_residual_transport {R : Type*} [CommRing R]
    (g : Rˣ) {N m j t : ℕ} (hm : 0<m) (hj : j.Coprime m)
    (negative : Bool) (i : ℤ) :
    ((g^giantExponent m j (denseRow N m j t negative).a
        (denseRow N m j t negative).b (denseRow N m j t negative).c : Rˣ) : R)-
          ((g^((m : ℤ)^2*i) : Rˣ) : R)=
      ((g^(-(m : ℤ)^2*centeringCarry N m j t negative) : Rˣ) : R)*
        (((g^reducedExponent N m j t negative : Rˣ) : R)-
          ((g^((m : ℤ)^2*(i+centeringCarry N m j t negative)) : Rˣ) : R)) := by
  rw [denseRow_giant_carries hm hj negative]
  have h₁ : reducedExponent N m j t negative-(m : ℤ)^2*centeringCarry N m j t negative=
      -(m : ℤ)^2*centeringCarry N m j t negative+reducedExponent N m j t negative := by ring
  have h₂ : (m : ℤ)^2*i=-(m : ℤ)^2*centeringCarry N m j t negative+
      (m : ℤ)^2*(i+centeringCarry N m j t negative) := by ring
  rw [h₁,h₂,zpow_add,zpow_add,Units.val_mul,Units.val_mul,mul_sub]

/-- The transformation preserves the entire public GCD, including prime
powers and saturated hits, rather than only a field-zero implication. -/
theorem denseRow_residual_gcd {N m j t : ℕ} (hm : 0<m) (hj : j.Coprime m)
    (g : (ZMod N)ˣ) (negative : Bool) (i : ℤ) :
    N.gcd (((g^giantExponent m j (denseRow N m j t negative).a
        (denseRow N m j t negative).b (denseRow N m j t negative).c : (ZMod N)ˣ) : ZMod N)-
          ((g^((m : ℤ)^2*i) : (ZMod N)ˣ) : ZMod N)).val=
      N.gcd (((g^reducedExponent N m j t negative : (ZMod N)ˣ) : ZMod N)-
          ((g^((m : ℤ)^2*(i+centeringCarry N m j t negative)) : (ZMod N)ˣ) : ZMod N)).val := by
  rw [denseRow_residual_transport g hm hj negative i]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq _ _

/-- Candidate recovery also survives exactly: the target index and both
retained coefficients are transported together. -/
theorem denseRow_recovery_transport {N m j t : ℕ} (hm : 0<m) (hj : j.Coprime m)
    (negative : Bool) (i : ℤ) :
    integerRoots (denseRow N m j t negative).a
        ((denseRow N m j t negative).b*m-
          2*(denseRow N m j t negative).a*j-(m : ℤ)^2*i) (t*N : ℕ)=
      integerRoots (carryRow N m j t negative).a
        ((carryRow N m j t negative).b*m-
          2*(carryRow N m j t negative).a*j-
            (m : ℤ)^2*(i+centeringCarry N m j t negative)) (t*N : ℕ) := by
  rw [denseRow_leading_carry,denseRow_linear_carry hm hj negative]
  simp only [carryRow]
  congr 1
  ring

/-- Group-valued collisions are equivalent after the exact index shift,
with no period or order assumption on the chosen base. -/
theorem denseRow_power_transport {G : Type*} [CommGroup G] (g : G)
    {N m j t : ℕ} (hm : 0<m) (hj : j.Coprime m) (negative : Bool) (i : ℤ) :
    g^giantExponent m j (denseRow N m j t negative).a
        (denseRow N m j t negative).b (denseRow N m j t negative).c=g^((m : ℤ)^2*i) ↔
      g^reducedExponent N m j t negative=
        g^((m : ℤ)^2*(i+centeringCarry N m j t negative)) := by
  rw [denseRow_giant_carries hm hj negative]
  have h₁ : reducedExponent N m j t negative-(m : ℤ)^2*centeringCarry N m j t negative=
      -(m : ℤ)^2*centeringCarry N m j t negative+reducedExponent N m j t negative := by ring
  have h₂ : (m : ℤ)^2*i=-(m : ℤ)^2*centeringCarry N m j t negative+
      (m : ℤ)^2*(i+centeringCarry N m j t negative) := by ring
  rw [h₁,h₂,zpow_add,zpow_add,mul_left_cancel_iff]

/-- The cached power is exactly the reduced giant power, for all indices.
Its floor-filtered geometric form is valid over every commutative group. -/
theorem progressionValue_eq {G : Type*} [CommGroup G] (g : G)
    (N m j t : ℕ) (negative : Bool) :
    progressionValue m t negative (progressionSeed g N m j)=
      g^reducedExponent N m j t negative := by
  simp only [progressionValue,progressionSeed,←zpow_natCast,←zpow_mul,←zpow_add]
  unfold reducedExponent leadingCarry
  congr 1
  ring

/-- The cached recovery formula is the original uncentered recovery
quadratic with the transported index, retaining its full root list. -/
theorem progressionRecovery_eq {G : Type*} [CommGroup G] (g : G)
    (N m j t : ℕ) (negative : Bool) (I : ℤ) :
    progressionRecovery N m t negative (progressionSeed g N m j) I=
      integerRoots (carryRow N m j t negative).a
        ((carryRow N m j t negative).b*m-
          2*(carryRow N m j t negative).a*j-(m : ℤ)^2*I) (t*N : ℕ) := by
  rfl

/-- The actual stored public source has linear descriptor count. The
number of parameter pairs that a naive acquisition visits remains quadratic. -/
theorem progressionSeeds_length {G : Type*} [CommGroup G] (g : G) (N m : ℕ) :
    (progressionSeeds g N m).length=m-1 := by
  simp only [progressionSeeds,List.length_map,List.length_range]

/-- Every positive original residue occurs in the actual public cache. -/
theorem progressionSeed_mem {G : Type*} [CommGroup G] (g : G)
    {N m j : ℕ} (hj : 0<j) (hjm : j<m) :
    progressionSeed g N m j∈progressionSeeds g N m := by
  apply List.mem_map.mpr
  refine ⟨j-1,List.mem_range.mpr (by omega),?_⟩
  have he : j-1+1=j := by omega
  simp only [he]

/-- Public cached values commute with every group projection, in particular
the unavailable prime-field projection used solely in the coverage proof. -/
theorem progressionValue_map {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G→*H) (g : G) (N m j t : ℕ) (negative : Bool) :
    φ (progressionValue m t negative (progressionSeed g N m j))=
      progressionValue m t negative (progressionSeed (φ g) N m j) := by
  rw [progressionValue_eq,progressionValue_eq,map_zpow]

/-- Recovery uses the public integer coefficients and target index only;
changing the ambient base group never changes its literal root list. -/
theorem progressionRecovery_base_independent {G H : Type*}
    [CommGroup G] [CommGroup H] (g : G) (h : H)
    (N m j t : ℕ) (negative : Bool) (I : ℤ) :
    progressionRecovery N m t negative (progressionSeed g N m j) I=
      progressionRecovery N m t negative (progressionSeed h N m j) I := by
  rw [progressionRecovery_eq,progressionRecovery_eq]

/-- The arithmetic forcing survives in the cached floor-filtered source,
with a linear signed baby window and the exact computable recovery list.
This is a coverage/reduction theorem, not an acquisition-cost theorem. -/
theorem progression_balanced_collision_coverage {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hq : q≤2*p) (hN : m.Coprime (p*q))
    (hsize : p*q≤m^6) (g : (ZMod p)ˣ) :
    ∃ (t : ℕ) (negative : Bool) (I : ℤ),
      0<t ∧ t<m ∧ I.natAbs≤5*m+15 ∧
      progressionValue m t negative (progressionSeed g (p*q) m (p%m))=
        g^((m : ℤ)^2*I) ∧
      (p : ℤ)∈progressionRecovery (p*q) m t negative
        (progressionSeed g (p*q) m (p%m)) I := by
  let : Fact p.Prime := ⟨hp⟩
  have hm₀ : 0<m := by omega
  obtain ⟨t,negative,i,_hmem,ha,ht,htm,hbound,_hsum,hi⟩ :=
    denseRows_index_coverage hm hp.pos hN (by omega : 0<3*m+11)
      (balanced_pigeonhole_width hm hpq hq hsize)
  have hmp : m.Coprime p := hN.of_dvd_right (dvd_mul_right p q)
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hmp
  let I := i+centeringCarry (p*q) m (p%m) t negative
  have hcarry := centeringCarry_bound (N:=p*q) hm hj (Nat.mod_lt p hm₀) ht htm negative
  have hI : I.natAbs≤5*m+15 := by
    have hsum := abs_add_le i (centeringCarry (p*q) m (p%m) t negative)
    have hb : |I|≤(5*m+15 : ℕ) := by
      dsimp only [I]
      push_cast
      push_cast at hbound
      linarith only [hsum,hbound,hcarry]
    rw [←Int.natCast_natAbs] at hb
    exact_mod_cast hb
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (denseRow (p*q) m (p%m) t negative).a (denseRow (p*q) m (p%m) t negative).b
        (denseRow (p*q) m (p%m) t negative).c (t : ℤ) := by
    have he := denseRow_relation (N:=p*q) (t:=t) hm₀ hj negative
    dsimp only at he
    have hden : (denseRow (p*q) m (p%m) t negative).t=(t : ℤ) := rfl
    rw [hden] at he
    simpa only [Nat.cast_mul] using he
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hperiod : g^((p : ℤ)-1)=1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p g
    have hz : g^((p-1 : ℕ) : ℤ)=1 := by simpa only [zpow_natCast] using h
    simpa only [Nat.cast_sub hp.one_le,Nat.cast_one] using hz
  have hhit := quotient_row_power_hit g hcoord hrel hi
    (by exact_mod_cast hp.ne_zero) hperiod
  have hreduced := (denseRow_power_transport g hm₀ hj negative i).mp hhit
  have hroot := integerRoots_complete ha (quotient_row_recovery_equation hcoord hrel hi)
  change (p : ℤ)∈integerRoots (denseRow (p*q) m (p%m) t negative).a
    ((denseRow (p*q) m (p%m) t negative).b*m-
      2*(denseRow (p*q) m (p%m) t negative).a*(p%m : ℕ)-(m : ℤ)^2*i) (t*(p*q) : ℕ) at hroot
  rw [denseRow_recovery_transport hm₀ hj negative i] at hroot
  refine ⟨t,negative,I,ht,htm,hI,?_,?_⟩
  · rw [progressionValue_eq]
    exact hreduced
  · rw [progressionRecovery_eq]
    exact hroot

/-- The actually stored N-only descriptors cover a true-factor collision,
and their public recovery function contains p. The prime projection is
proof-side data and is never used by the cache or query constructor. -/
theorem public_progression_balanced_coverage {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hq : q≤2*p) (hN : m.Coprime (p*q))
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) :
    let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
    ∃ (t : ℕ) (negative : Bool) (I : ℤ),
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      0<t ∧ t<m ∧ I.natAbs≤5*m+15 ∧
      π (progressionValue m t negative (progressionSeed g (p*q) m (p%m)))=
        (π g)^((m : ℤ)^2*I) ∧
      (p : ℤ)∈progressionRecovery (p*q) m t negative
        (progressionSeed g (p*q) m (p%m)) I := by
  let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
    Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
  obtain ⟨t,negative,I,ht,htm,hI,hhit,hroot⟩ :=
    progression_balanced_collision_coverage hm hp hpq hq hN hsize (π g)
  have hmp : m.Coprime p := hN.of_dvd_right (dvd_mul_right p q)
  have hjcop : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hmp
  have hj : 0<p%m := by
    by_contra! hz
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hjcop
    omega
  refine ⟨t,negative,I,progressionSeed_mem g hj (Nat.mod_lt p (by omega)),
    ht,htm,hI,?_,?_⟩
  · rw [progressionValue_map]
    exact hhit
  · rw [progressionRecovery_base_independent g (π g)]
    exact hroot

end RiemannGaussian.SemiprimeDenseRowCarries
