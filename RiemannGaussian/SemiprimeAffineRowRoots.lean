/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCompanionCenterSpectrum
import RiemannGaussian.SemiprimeReflectedCompanions
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Two normalized coefficient channels from the original quadratic rows

Keep every original packet before either modular normalization. The public
factor-coordinate quadratic has constant term Nt. Dividing its two-row
resultant by the known factor N before modular reduction retains two
coefficient determinants. Unit normalizations transport those determinants
to two root-polynomial difference channels, with no row-pair matrix.

The joined detector retains the signed companion family and recovers a
literal native frontier miss. No universal coverage or complete bit cost
is asserted for this amended family.
-/

namespace RiemannGaussian.SemiprimeAffineRowRoots

open Polynomial SemiprimeQuotientRows SemiprimeQuotientCentering
open SemiprimeEuclidRowFamily SemiprimeCompanionRows SemiprimeCompanionCoverage
open SemiprimeCompanionCenterSpectrum SemiprimeReflectedCompanions
open SemiprimeCartesianCompletion SemiprimeRowDerivative

/-- The original centered linear factor-coordinate coefficient. -/
def packetOffset (m : ℕ) (w : FamilyPacket) : ℤ :=
  (m : ℤ)*(centeredPacketRow m w).b-2*w.original.a*w.residue

/-- Keep the leading-coefficient and denominator normalizations separate. -/
def packetScale (w : FamilyPacket) (denominator : Bool) : ℤ :=
  if denominator then w.original.t else w.original.a

/-- A projected coordinate is used only after its scale passes the unit
check. The full original packet and its integer offset remain upstream. -/
def packetRoot (N m : ℕ) (w : FamilyPacket) (denominator : Bool) : ZMod N :=
  -(packetOffset m w : ZMod N)*(packetScale w denominator : ZMod N)⁻¹

/-- Unit normalization preserves the exact coefficient equation. -/
theorem packetRoot_coefficient {N m : ℕ} (w : FamilyPacket) (side : Bool)
    (hu : IsUnit (packetScale w side : ZMod N)) :
    (packetScale w side : ZMod N)*packetRoot N m w side=-(packetOffset m w : ZMod N) := by
  unfold packetRoot
  calc
    _ = -(packetOffset m w : ZMod N)*
        ((packetScale w side : ZMod N)*(packetScale w side : ZMod N)⁻¹) := by ring
    _ = _ := by rw [ZMod.mul_inv_of_unit _ hu,mul_one]

/-- A public coefficient equation certifies a normalized root without
evaluating a large modular inverse in the kernel. -/
theorem packetRoot_eq_of_coefficient {N m : ℕ} (w : FamilyPacket) (side : Bool)
    (hu : IsUnit (packetScale w side : ZMod N)) (v : ZMod N)
    (hv : (packetScale w side : ZMod N)*v=-(packetOffset m w : ZMod N)) :
    packetRoot N m w side=v := by
  calc
    _ = (packetScale w side : ZMod N)⁻¹*
        ((packetScale w side : ZMod N)*packetRoot N m w side) := by
      rw [←mul_assoc,ZMod.inv_mul_of_unit _ hu,one_mul]
    _ = (packetScale w side : ZMod N)⁻¹*((packetScale w side : ZMod N)*v) := by
      rw [packetRoot_coefficient w side hu,hv]
    _ = _ := by rw [←mul_assoc,ZMod.inv_mul_of_unit _ hu,one_mul]

/-- Each normalized difference retains its original coefficient minor. -/
theorem packetRoot_cross_difference {N m : ℕ} (w v : FamilyPacket) (side : Bool)
    (hw : IsUnit (packetScale w side : ZMod N))
    (hv : IsUnit (packetScale v side : ZMod N)) :
    (packetScale w side : ZMod N)*(packetScale v side : ZMod N)*
        (packetRoot N m w side-packetRoot N m v side)=
      (packetScale w side : ZMod N)*(packetOffset m v : ZMod N)-
        (packetScale v side : ZMod N)*(packetOffset m w : ZMod N) := by
  have hwl := packetRoot_coefficient (m:=m) w side hw
  have hvr := packetRoot_coefficient (m:=m) v side hv
  linear_combination (packetScale v side : ZMod N)*hwl-
    (packetScale w side : ZMod N)*hvr

/-- The public coordinate change keeps the Nt term as an exact integer
identity before any reduction modulo the whole N. -/
theorem quotient_scaled_coordinate {N m j : ℤ} {z : QuotientRow}
    (hz : quotientRelation N m j z.a z.b z.c z.t) (X : ℤ) :
    m^2*quadratic z.a z.b z.c X=
      z.a*(m*X+j)^2+(m*z.b-2*z.a*j)*(m*X+j)+N*z.t := by
  simp only [quadratic,quotientRelation] at hz ⊢
  linear_combination hz

/-- Membership discharges the original shifted quotient relation. -/
theorem residuePacket_relation {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m)
    {w : FamilyPacket} (hw : w∈residuePackets N m j) :
    quotientRelation N m w.residue (centeredPacketRow m w).a
      (centeredPacketRow m w).b (centeredPacketRow m w).c (centeredPacketRow m w).t := by
  obtain ⟨v,hv,hw⟩ := List.mem_flatMap.mp hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  have hr := (intermediate_row_correct hm hj hv).2.2
  rcases hw with rfl|rfl
  all_goals exact shiftRow_relation hr _

theorem publicPacket_relation {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) :
    quotientRelation N m w.residue (centeredPacketRow m w).a
      (centeredPacketRow m w).b (centeredPacketRow m w).c (centeredPacketRow m w).t := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw with hj
  · exact residuePacket_relation hm hj hw
  · simp only [List.not_mem_nil] at hw

/-- The leading-coefficient root is the nonzero coordinate factor of
the actual original quadratic after the known global Y factor is removed. -/
theorem publicPacket_modular_factorization {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (hu : IsUnit (w.original.a : ZMod N)) (X : ℤ) :
    ((m : ℤ)^2*quadratic (centeredPacketRow m w).a (centeredPacketRow m w).b
        (centeredPacketRow m w).c X : ZMod N)=
      (w.original.a : ZMod N)*((m : ℤ)*X+w.residue : ZMod N)*
        (((m : ℤ)*X+w.residue : ZMod N)-packetRoot N m w false) := by
  have h := quotient_scaled_coordinate (publicPacket_relation hm hw) X
  have hc := congrArg (fun z : ℤ => (z : ZMod N)) h
  have hr := packetRoot_coefficient (m:=m) w false hu
  simp only [packetScale,Bool.false_eq_true,if_false] at hr
  simp only [centeredPacketRow,shiftRow] at hc
  push_cast at hc
  simp only [ZMod.natCast_self,zero_mul,add_zero] at hc
  unfold packetOffset at hr
  simp only [centeredPacketRow,shiftRow] at hr ⊢
  push_cast at hr ⊢
  linear_combination hc+((m : ZMod N)*(X : ZMod N)+(w.residue : ZMod N))*hr

/-- The complete three-coefficient polynomial before scalar elimination. -/
noncomputable def quadraticPolynomial {R : Type*} [CommRing R] (a b c : R) : R[X] :=
  C a*X^2+C b*X+C c

/-- Connect the literal quadratic coefficient matrix to Mathlib's
Sylvester definition, rather than assuming a resultant formula. -/
theorem quadratic_sylvester {R : Type*} [CommRing R] (a b c d e f : R) :
    (quadraticPolynomial a b c).sylvester (quadraticPolynomial d e f) 2 2=
      !![f,0,c,0; e,f,b,c; d,e,a,b; 0,d,0,a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Polynomial.sylvester,quadraticPolynomial,Fin.addCases,
      Polynomial.coeff_X,Polynomial.coeff_C]

/-- The genuine degree-two resultant retains both coefficient minors. -/
theorem quadratic_resultant {R : Type*} [CommRing R] (a b c d e f : R) :
    Polynomial.resultant (quadraticPolynomial a b c) (quadraticPolynomial d e f) 2 2=
      (a*f-d*c)^2-(a*e-d*b)*(b*f-e*c) := by
  rw [Polynomial.resultant,quadratic_sylvester,Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove]
  ring

/-- The original integer resultant after its known factor N is removed.
All original leading coefficients, offsets and denominators survive. -/
def normalizedResultant (N m : ℕ) (w v : FamilyPacket) : ℤ :=
  (N : ℤ)*(w.original.a*v.original.t-v.original.a*w.original.t)^2-
    (w.original.a*packetOffset m v-v.original.a*packetOffset m w)*
      (packetOffset m w*v.original.t-packetOffset m v*w.original.t)

/-- Division by N happens over the integers before modular reduction. -/
theorem packet_resultant_exact (N m : ℕ) (w v : FamilyPacket) :
    Polynomial.resultant
        (quadraticPolynomial w.original.a (packetOffset m w) ((N : ℤ)*w.original.t))
        (quadraticPolynomial v.original.a (packetOffset m v) ((N : ℤ)*v.original.t)) 2 2=
      (N : ℤ)*normalizedResultant N m w v := by
  rw [quadratic_resultant]
  unfold normalizedResultant
  ring

theorem packet_resultant_div {N m : ℕ} (hN : 0<N) (w v : FamilyPacket) :
    Polynomial.resultant
        (quadraticPolynomial w.original.a (packetOffset m w) ((N : ℤ)*w.original.t))
        (quadraticPolynomial v.original.a (packetOffset m v) ((N : ℤ)*v.original.t)) 2 2 /
      (N : ℤ)=normalizedResultant N m w v := by
  rw [packet_resultant_exact,Int.mul_ediv_cancel_left _ (by exact_mod_cast hN.ne')]

/-- The N-divided resultant is a unit phase times the two separate
normalized difference channels. This retains exact multiplicities. -/
theorem normalizedResultant_mod {N m : ℕ} (w v : FamilyPacket)
    (hwa : IsUnit (w.original.a : ZMod N)) (hva : IsUnit (v.original.a : ZMod N))
    (hwt : IsUnit (w.original.t : ZMod N)) (hvt : IsUnit (v.original.t : ZMod N)) :
    (normalizedResultant N m w v : ZMod N)=
      (w.original.a : ZMod N)*(v.original.a : ZMod N)*
        (w.original.t : ZMod N)*(v.original.t : ZMod N)*
        (packetRoot N m w false-packetRoot N m v false)*
        (packetRoot N m w true-packetRoot N m v true) := by
  have ha := packetRoot_cross_difference (m:=m) w v false hwa hva
  have ht := packetRoot_cross_difference (m:=m) w v true hwt hvt
  simp only [packetScale,Bool.false_eq_true,if_false,if_true] at ha ht
  calc
    _ = ((w.original.a : ZMod N)*(packetOffset m v : ZMod N)-
          (v.original.a : ZMod N)*(packetOffset m w : ZMod N))*
        ((w.original.t : ZMod N)*(packetOffset m v : ZMod N)-
          (v.original.t : ZMod N)*(packetOffset m w : ZMod N)) := by
      simp only [normalizedResultant,Int.cast_sub,Int.cast_mul,Int.cast_pow,
        Int.cast_natCast,ZMod.natCast_self,zero_mul,zero_sub]
      ring
    _ = _ := by rw [←ha,←ht]; ring

/-- Public units preserve the full normalized-resultant GCD, including
prime powers and saturation. The two channels remain separately available. -/
theorem normalizedResultant_gcd {N m : ℕ} (w v : FamilyPacket)
    (hwa : IsUnit (w.original.a : ZMod N)) (hva : IsUnit (v.original.a : ZMod N))
    (hwt : IsUnit (w.original.t : ZMod N)) (hvt : IsUnit (v.original.t : ZMod N)) :
    N.gcd (normalizedResultant N m w v : ZMod N).val=
      N.gcd ((packetRoot N m w false-packetRoot N m v false)*
        (packetRoot N m w true-packetRoot N m v true)).val := by
  have hu := ((hwa.mul hva).mul hwt).mul hvt
  rw [normalizedResultant_mod w v hwa hva hwt hvt]
  rw [mul_assoc ((w.original.a : ZMod N)*(v.original.a : ZMod N)*
    (w.original.t : ZMod N)*(v.original.t : ZMod N))]
  rw [←hu.unit_spec]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq hu.unit _

/-- Keep bad scales out of modular normalization; the separate public
coefficient scan retains their GCD information. -/
noncomputable def coordinateEntry (N m : ℕ) (w : FamilyPacket) (side : Bool) : Option (ZMod N) := by
  classical
  exact if IsUnit (packetScale w side : ZMod N) then some (packetRoot N m w side) else none

/-- Each source packet contributes at most one root in each channel. -/
noncomputable def coordinateValues (N m : ℕ) (side : Bool) : List (ZMod N) :=
  (publicPackets N m).filterMap fun w => coordinateEntry N m w side

/-- Only the detector fork deduplicates modulo the whole N. -/
noncomputable def coordinateRoots (N m : ℕ) (side : Bool) : Finset (ZMod N) :=
  (coordinateValues N m side).toFinset

theorem coordinateRoots_mem {N m : ℕ} {w : FamilyPacket} (hw : w∈publicPackets N m)
    (side : Bool) (hu : IsUnit (packetScale w side : ZMod N)) :
    packetRoot N m w side∈coordinateRoots N m side := by
  classical
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  exact ⟨w,hw,by simp only [coordinateEntry,if_pos hu]⟩

theorem coordinateRoots_card_le (N m : ℕ) (side : Bool) :
    (coordinateRoots N m side).card≤(publicPackets N m).length := by
  calc
    _ ≤ (coordinateValues N m side).length := List.toFinset_card_le _
    _ ≤ _ := List.length_filterMap_le _ _

/-- Both original affine channels join the complete ordinary companions;
reflection retains all sums, differences and endpoints in one polynomial. -/
noncomputable def joinedRoots (N m : ℕ) : Finset (ZMod N) :=
  (publicCompanionRoots N m∪coordinateRoots N m false)∪coordinateRoots N m true

theorem joinedRoots_coordinate_mem {N m : ℕ} {w : FamilyPacket}
    (hw : w∈publicPackets N m) (side : Bool) (hu : IsUnit (packetScale w side : ZMod N)) :
    packetRoot N m w side∈joinedRoots N m := by
  have h := coordinateRoots_mem hw side hu
  cases side
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  · exact Finset.mem_union_right _ h

/-- The amended ordinary polynomial still has linear degree in the
complete original packet count, without constructing any pair list. -/
theorem joinedRoots_card_le (N m : ℕ) :
    (joinedRoots N m).card≤4*(publicPackets N m).length := by
  have ha := coordinateRoots_card_le N m false
  have ht := coordinateRoots_card_le N m true
  have hc := publicCompanionRoots_card_le N m
  have h1 := Finset.card_union_le (publicCompanionRoots N m) (coordinateRoots N m false)
  have h2 := Finset.card_union_le (publicCompanionRoots N m∪coordinateRoots N m false)
    (coordinateRoots N m true)
  unfold joinedRoots
  omega

/-- All original scale checks are kept before either affine projection. -/
def coefficientChecks (N m : ℕ) : List ℕ :=
  ((publicPackets N m).map fun w => w.original.a.natAbs)++
    ((publicPackets N m).map fun w => w.original.t.natAbs)

/-- The public coefficient GCD prefix precedes the shared reflected
polynomial detector. Returned divisors are always checked. -/
noncomputable def recoverJoinedAffineRows (N m : ℕ) : Option ℕ :=
  match scanProper N (coefficientChecks N m) with
  | some d => some d
  | none => recoverReflectedRows (joinedRoots N m)

theorem recoverJoinedAffineRows_sound {N m d : ℕ}
    (hd : recoverJoinedAffineRows N m=some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  unfold recoverJoinedAffineRows at hd
  cases hp : scanProper N (coefficientChecks N m) with
  | some f =>
    simp only [hp,Option.some.injEq] at hd
    subst d
    exact scanProper_sound hp
  | none => exact recoverReflectedRows_sound (by simpa only [hp] using hd)

/-- Every proper signed pair in the joined family is recovered, including
when another pair makes its product column saturate modulo N. -/
theorem recoverJoinedAffineRows_of_proper_pair {N m : ℕ} [NeZero N]
    {x t : ZMod N} (hx : x∈signedRoots (joinedRoots N m))
    (ht : t∈signedRoots (joinedRoots N m))
    (hp : SemiprimeGroupSelection.ProperDivisor N (N.gcd (t-x).val)) :
    ∃ d, recoverJoinedAffineRows N m=some d := by
  unfold recoverJoinedAffineRows
  cases hf : scanProper N (coefficientChecks N m) with
  | some d => exact ⟨d,rfl⟩
  | none =>
    obtain ⟨d,hd⟩ := recoverRows_succeeds_of_proper_pair hx ht hp
    cases hr : recoverReflectedRows (joinedRoots N m) with
    | some f => exact ⟨f,rfl⟩
    | none =>
      have hn := (recoverReflectedRows_none_iff_signed _).mp hr
      rw [hd] at hn
      contradiction

/-- Enlarging the ordinary source preserves every existing signed
companion success; the first returned divisor may change. -/
theorem recoverJoinedAffineRows_preserves_companions {N m d : ℕ} [NeZero N]
    (hd : recoverSignedCompanions N m=some d) :
    ∃ f, recoverJoinedAffineRows N m=some f := by
  cases hs : recoverJoinedAffineRows N m with
  | some f => exact ⟨f,rfl⟩
  | none =>
    have hp : recoverReflectedRows (joinedRoots N m)=none := by
      unfold recoverJoinedAffineRows at hs
      cases hf : scanProper N (coefficientChecks N m) <;> simp_all
    have hu := (recoverReflectedRows_none_iff _).mp hp
    have hsub : publicCompanionRoots N m⊆joinedRoots N m := by
      intro x hx
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    have hold : recoverReflectedCompanions N m=none := by
      apply (recoverReflectedRows_none_iff _).mpr
      intro x hx
      have h := (reflectedColumn_isUnit_iff _ _).mp (hu x (hsub hx))
      apply (reflectedColumn_isUnit_iff _ _).mpr
      exact ⟨h.1,fun y hy hne => h.2.1 y (hsub hy) hne,
        fun y hy hne => h.2.2 y (hsub hy) hne⟩
    have hn := recoverReflectedCompanions_none_iff_signed.mp hold
    rw [hd] at hn
    contradiction

/-- The GCD-query ledger includes all original coefficient checks and
the reflected recovery, only when its prefix has not returned a factor. -/
noncomputable def joinedGcdCount (N m : ℕ) : ℕ :=
  scanGcdCount N (coefficientChecks N m)+
    match scanProper N (coefficientChecks N m) with
    | some _ => 0
    | none => recoveryGcdCount N (fun i => reflectedLeaves (joinedRoots N m) (i : ZMod N))
        (reflectedColumns (joinedRoots N m))

/-- This is a complete GCD-query envelope, not a bit-cost theorem. -/
theorem joinedGcdCount_le (N m : ℕ) :
    joinedGcdCount N m≤14*(publicPackets N m).length+1 := by
  have hp := scanGcdCount_le N (coefficientChecks N m)
  have hlen : (coefficientChecks N m).length=2*(publicPackets N m).length := by
    simp only [coefficientChecks,List.length_append,List.length_map,two_mul]
  rw [hlen] at hp
  have hr := recoverReflectedRows_gcd_bound (joinedRoots N m)
  have hc := joinedRoots_card_le N m
  unfold joinedGcdCount
  cases scanProper N (coefficientChecks N m) <;> dsimp only <;> omega

theorem joinedGcdCount_prime_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    joinedGcdCount N m≤112*m*(Nat.log2 m+1)^2+1 := by
  calc
    _ ≤ 14*(publicPackets N m).length+1 := joinedGcdCount_le N m
    _ ≤ 14*(8*m*(Nat.log2 m+1)^2)+1 := Nat.add_le_add_right
      (Nat.mul_le_mul_left 14 (SemiprimeEuclidRowBudget.publicPackets_length_le N hm)) 1
    _ = _ := by ring

/-- A literal smaller-center packet from one original public vector. -/
def smallerPacket (N m j : ℕ) (v : ℤ×ℕ) : FamilyPacket :=
  let z := liftRow N m j (publicInverse m j) v.1 v.2
  ⟨j,z,publicShift N m j z.a z.b z.t⟩

/-- The public residue and vector constructors certify full membership
without enumerating every residue in the kernel. -/
theorem smallerPacket_mem_of_pair {N m j : ℕ} (hj : j<m) (hc : j.Coprime m)
    {v : ℤ×ℕ} (hv : v∈publicPairs N m j) :
    smallerPacket N m j v∈publicPackets N m := by
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  change smallerPacket N m j v∈(if j.Coprime m then residuePackets N m j else [])
  rw [if_pos hc]
  apply List.mem_flatMap.mpr
  exact ⟨v,hv,List.mem_cons_self⟩

/-- First original row in the affine repair of the frozen native miss. -/
def frontierFirstPacket : FamilyPacket :=
  smallerPacket 6798061565397654183415201602281 137639 85189 (-2,87345)

/-- Second original row in the same public source. -/
def frontierSecondPacket : FamilyPacket :=
  smallerPacket 6798061565397654183415201602281 137639 95998 (64004,4909)

set_option maxRecDepth 32768 in
/-- Both witness vectors come from the literal public Euclidean stream. -/
theorem frontier_control_vectors :
    ((-2 : ℤ),87345)∈publicPairs 6798061565397654183415201602281 137639 85189 ∧
      ((64004 : ℤ),4909)∈publicPairs 6798061565397654183415201602281 137639 95998 := by
  decide +kernel

theorem frontier_control_membership :
    frontierFirstPacket∈publicPackets 6798061565397654183415201602281 137639 ∧
      frontierSecondPacket∈publicPackets 6798061565397654183415201602281 137639 := by
  exact ⟨smallerPacket_mem_of_pair (by norm_num) (by norm_num [Nat.Coprime]) frontier_control_vectors.1,
    smallerPacket_mem_of_pair (by norm_num) (by norm_num [Nat.Coprime]) frontier_control_vectors.2⟩

set_option maxRecDepth 32768 in
/-- The exact original shifts and offsets are checked before projection. -/
theorem frontier_control_offsets :
    packetOffset 137639 frontierFirstPacket=-274896527429303546246 ∧
      packetOffset 137639 frontierSecondPacket=-157889571041042645902 := by
  decide +kernel

/-- The two actual leading coefficients pass public unit checks. -/
theorem frontier_control_units :
    IsUnit (packetScale frontierFirstPacket false : ZMod 6798061565397654183415201602281) ∧
      IsUnit (packetScale frontierSecondPacket false : ZMod 6798061565397654183415201602281) := by
  constructor
  · change IsUnit (-2 : ZMod 6798061565397654183415201602281)
    exact ((ZMod.isUnit_iff_coprime 2 _).mpr (by norm_num [Nat.Coprime])).neg
  · change IsUnit (64004 : ZMod 6798061565397654183415201602281)
    exact (ZMod.isUnit_iff_coprime 64004 _).mpr (by norm_num [Nat.Coprime])

/-- Both public normalized roots are certified by their coefficient
equations, retaining the sign of the first row. -/
theorem frontier_control_roots :
    packetRoot 6798061565397654183415201602281 137639 frontierFirstPacket false=
      (-137448263714651773123 : ZMod 6798061565397654183415201602281) ∧
    packetRoot 6798061565397654183415201602281 137639 frontierSecondPacket false=
      (4222394529573440758344149827194 : ZMod 6798061565397654183415201602281) := by
  constructor
  · apply packetRoot_eq_of_coefficient _ _ frontier_control_units.1
    rw [frontier_control_offsets.1]
    change (-2 : ZMod 6798061565397654183415201602281)*(-137448263714651773123)=
      -(-274896527429303546246 : ℤ)
    norm_num
  · apply packetRoot_eq_of_coefficient _ _ frontier_control_units.2
    rw [frontier_control_offsets.2]
    change (64004 : ZMod 6798061565397654183415201602281)*4222394529573440758344149827194=
      -(-157889571041042645902 : ℤ)
    reduce_mod_char

/-- The signed pair has this exact public GCD, independently of the
private-field witness search and the earlier native failure classifier. -/
theorem frontier_control_gcd :
    (6798061565397654183415201602281 : ℕ).gcd
        (packetRoot 6798061565397654183415201602281 137639 frontierFirstPacket false+
          packetRoot 6798061565397654183415201602281 137639 frontierSecondPacket false).val=
      2245327606949267 := by
  rw [frontier_control_roots.1,frontier_control_roots.2]
  norm_num [ZMod.val]
  decide +kernel

/-- The certified GCD is proper on the literal 103-bit frontier input. -/
theorem frontier_control_proper_sum : SemiprimeGroupSelection.ProperDivisor
    6798061565397654183415201602281
      ((6798061565397654183415201602281 : ℕ).gcd
        (packetRoot 6798061565397654183415201602281 137639 frontierFirstPacket false+
          packetRoot 6798061565397654183415201602281 137639 frontierSecondPacket false).val) := by
  rw [frontier_control_gcd]
  norm_num [SemiprimeGroupSelection.ProperDivisor]

/-- The complete joined N-only row source recovers this literal input.
Neither a factor, private field, residue nor pair is an algorithm input. -/
theorem frontier_joined_recovers :
    ∃ d, recoverJoinedAffineRows 6798061565397654183415201602281 137639=some d := by
  apply recoverJoinedAffineRows_of_proper_pair
    (signedRoots_neg_mem (joinedRoots_coordinate_mem frontier_control_membership.1 false
      frontier_control_units.1))
    (signedRoots_mem (joinedRoots_coordinate_mem frontier_control_membership.2 false
      frontier_control_units.2))
  simpa only [sub_neg_eq_add,add_comm] using frontier_control_proper_sum

/-- The canonical public prime selector supplies the modulus. -/
noncomputable def recoverPublicAffineRows (N : ℕ) : Option ℕ :=
  recoverJoinedAffineRows N (SemiprimeEuclidRowBudget.publicRowModulus N)

theorem recoverPublicAffineRows_sound {N d : ℕ} (hd : recoverPublicAffineRows N=some d) :
    SemiprimeGroupSelection.ProperDivisor N d := recoverJoinedAffineRows_sound hd

theorem frontier_public_recovers : ∃ d, recoverPublicAffineRows 6798061565397654183415201602281=some d := by
  unfold recoverPublicAffineRows
  rw [frontier_control_public_modulus]
  exact frontier_joined_recovers

end RiemannGaussian.SemiprimeAffineRowRoots
