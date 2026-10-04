/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHyperbolicWrapCoverage

/-!
# Merge the exact short index and linear wrap into one common-base interval

The linear wrap bound permits public period folding without discarding
the original quadratic: at most three full wrap lifts are retained. The
merged index uses the SAME base g^m at every cached residue. Two intervals
below the routed local periods cover it, reducing the target records to
residue/denominator pairs. Full acquisition and bit costs remain separate.
-/

namespace RiemannGaussian.SemiprimeMergedIndexAcquisition

open SemiprimeQuotientRows SemiprimeDenseRowCarries SemiprimeWideWrapCoverage
open SemiprimeHyperbolicWrapCoverage SemiprimeWrapIndexRecovery
open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeIntervalJet
open Polynomial

/-- One public base is shared by every residue and denominator. -/
def commonStep {G : Type*} [CommGroup G] (g : G) (m : ℕ) : G := g^(m : ℤ)

/-- Fold both original tags into one signed index, retaining their exact
integer linear relation for subsequent reconstruction. -/
def combinedIndex (m j k : ℕ) (i : ℤ) : ℤ :=
  (m : ℤ)*i+(1-(j : ℤ))*(k : ℤ)

/-- The original row's carry is a known power of the common base. -/
theorem carryStep_common {G : Type*} [CommGroup G] (g : G) (N m j : ℕ) :
    (progressionSeed g N m j).carryStep=(commonStep g m)^(1-(j : ℤ)) := by
  simp only [progressionSeed,commonStep,zpow_mul]

/-- The folded power still contains the complete original wrap and index. -/
theorem combined_power {G : Type*} [CommGroup G] (g : G) (N m j k : ℕ) (i : ℤ) :
    (commonStep g m)^combinedIndex m j k i=
      g^((m : ℤ)^2*i)*(progressionSeed g N m j).carryStep^k := by
  simp only [commonStep,combinedIndex,progressionSeed,←zpow_natCast,
    ←zpow_mul,←zpow_add]
  congr 1
  ring

/-- Original power collisions are exactly common-base interval hits. -/
theorem merged_hit_iff {G : Type*} [CommGroup G] (g : G) (N m j t k : ℕ) (i : ℤ) :
    wrappedValue t k (progressionSeed g N m j)=g^((m : ℤ)^2*i) ↔
      (progressionSeed g N m j).step^t=(commonStep g m)^combinedIndex m j k i := by
  rw [wrappedValue,zpow_neg,zpow_natCast,mul_inv_eq_iff_eq_mul,←combined_power]

/-- Linear wrap and short-index bounds give a single quadratic signed
range, independent of the original residue and denominator. -/
theorem combinedIndex_bounds {m j k : ℕ} {i : ℤ} (hm : 1<m)
    (hj : 1≤j) (hjm : j<m) (hk : k≤2*m+1) (hi : i.natAbs<2*m) :
    -4*(m : ℤ)^2≤combinedIndex m j k i ∧ combinedIndex m j k i<2*(m : ℤ)^2 := by
  have hmz : (0 : ℤ)<m := by exact_mod_cast (by omega : 0<m)
  have hjz : (1 : ℤ)≤j := by exact_mod_cast hj
  have hjmz : (j : ℤ)≤m := by exact_mod_cast hjm.le
  have hkz : (k : ℤ)≤2*(m : ℤ)+1 := by exact_mod_cast hk
  have hiz : |i|<(2*m : ℕ) := by
    simpa only [Int.natCast_natAbs] using
      (show (i.natAbs : ℤ)<(2*m : ℕ) by exact_mod_cast hi)
  have hi' := abs_lt.mp hiz
  push_cast at hi'
  have hlo := mul_lt_mul_of_pos_left hi'.1 hmz
  have hhi := mul_lt_mul_of_pos_left hi'.2 hmz
  have hprod := mul_le_mul (by linarith only [hjmz] : (j : ℤ)-1≤(m : ℤ)-1)
    hkz (by positivity : (0 : ℤ)≤k) (by linarith only [hmz] : (0 : ℤ)≤(m : ℤ)-1)
  have hneg : (1-(j : ℤ))*(k : ℤ)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [hjz]) (by positivity)
  unfold combinedIndex
  constructor <;> nlinarith only [hlo,hhi,hprod,hneg,hmz]

/-- Each half is shorter than the existing routed long local periods. -/
def mergedLength (m : ℕ) : ℕ := 3*m^2

/-- Adjacent lower and upper intervals cover every proved combined index. -/
def mergedStart (m : ℕ) (upper : Bool) : ℤ :=
  if upper then -(m : ℤ)^2 else -4*(m : ℤ)^2

/-- The whole signed range is covered by two public simple-root intervals. -/
theorem combinedIndex_half {m : ℕ} {z : ℤ}
    (hz₀ : -4*(m : ℤ)^2≤z) (hz₁ : z<2*(m : ℤ)^2) :
    ∃ (upper : Bool) (r : ℕ), r<mergedLength m ∧ z=mergedStart m upper+r := by
  by_cases hz : z < -(m : ℤ)^2
  · let r := (z+4*(m : ℤ)^2).toNat
    have hr : (r : ℤ)=z+4*(m : ℤ)^2 := Int.toNat_of_nonneg (by omega)
    have hr₁ : (r : ℤ)<(mergedLength m : ℤ) := by
      unfold mergedLength
      push_cast
      nlinarith only [hr,hz]
    exact ⟨false,r,by exact_mod_cast hr₁,by simp only [mergedStart,Bool.false_eq_true,if_false]; omega⟩
  · let r := (z+(m : ℤ)^2).toNat
    have hr : (r : ℤ)=z+(m : ℤ)^2 := Int.toNat_of_nonneg (by omega)
    have hr₁ : (r : ℤ)<(mergedLength m : ℤ) := by
      unfold mergedLength
      push_cast
      nlinarith only [hr,hz₁]
    exact ⟨true,r,by exact_mod_cast hr₁,by simp only [mergedStart,if_true]; omega⟩

/-- Invert the known coefficient 1-j modulo the public modulus. -/
def wrapResidue (m j : ℕ) (z : ℤ) : ℕ :=
  ((-publicInverse m (j-1)*z)%(m : ℤ)).toNat

/-- The merged integer index determines the true wrap residue exactly. -/
theorem wrapResidue_eq {m j k : ℕ} {i : ℤ} (hj : 1≤j)
    (hcop : (j-1).Coprime m) :
    wrapResidue m j (combinedIndex m j k i)=k%m := by
  let w := publicInverse m (j-1)
  have hInv := (publicInverse_correct hcop).mul_right (k : ℤ)
  have he : -w*combinedIndex m j k i=
      (m : ℤ)*(-w*i)+((j-1 : ℕ) : ℤ)*w*k := by
    have hjz : ((j-1 : ℕ) : ℤ)=(j : ℤ)-1 := by omega
    unfold combinedIndex
    rw [hjz]
    ring
  have hzero : (m : ℤ)*(-w*i) ≡ 0 [ZMOD m] :=
    Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
  have hw : -w*combinedIndex m j k i ≡ (k : ℤ) [ZMOD m] := by
    rw [he]
    simpa only [zero_add,one_mul] using hzero.add hInv
  unfold wrapResidue
  rw [hw.eq,←Int.natCast_mod,Int.toNat_natCast]

/-- Retain all three full wraps, rather than choosing one modular alias. -/
def mergedWraps (m j : ℕ) (z : ℤ) : List ℕ :=
  (List.range 3).map fun l => wrapResidue m j z+l*m

/-- Every proved linear wrap occurs among the three retained lifts. -/
theorem mergedWraps_mem {m j k : ℕ} {i : ℤ} (hm : 1<m) (hj : 1≤j)
    (hcop : (j-1).Coprime m) (hk : k≤2*m+1) :
    k∈mergedWraps m j (combinedIndex m j k i) := by
  have hm₀ : 0<m := by omega
  have hl : k/m<3 := (Nat.div_lt_iff_lt_mul hm₀).mpr (by omega)
  unfold mergedWraps
  apply List.mem_map.mpr
  refine ⟨k/m,List.mem_range.mpr hl,?_⟩
  rw [wrapResidue_eq hj hcop]
  simpa only [Nat.mul_comm] using Nat.mod_add_div k m

/-- Reconstruct the original exact short index at each retained full wrap. -/
def unmergeIndex (m j k : ℕ) (z : ℤ) : ℤ :=
  (z-(1-(j : ℤ))*(k : ℤ))/(m : ℤ)

/-- No integer recovery information is lost by the two index transports. -/
theorem unmergeIndex_exact {m : ℕ} (hm : 0<m) (j k : ℕ) (i : ℤ) :
    unmergeIndex m j k (combinedIndex m j k i)=i := by
  unfold unmergeIndex combinedIndex
  rw [add_sub_cancel_right,Int.mul_ediv_cancel_left _ (by exact_mod_cast hm.ne')]

/-- The decoder keeps the complete quadratic root list at every retained
full wrap, including a common global power collision. -/
def mergedRecovery {G : Type*} (N m t : ℕ) (s : ProgressionSeed G) (z : ℤ) : List ℤ :=
  (mergedWraps m s.residue z).flatMap fun k =>
    wrappedRecovery N m t k s (unmergeIndex m s.residue k z)

/-- An original exact recovery root survives the finite alias bundle. -/
theorem mergedRecovery_preserves_root {G : Type*} {N m t k : ℕ}
    (s : ProgressionSeed G) (i p : ℤ) (hm : 1<m) (hj : 1≤s.residue)
    (hcop : (s.residue-1).Coprime m) (hk : k≤2*m+1)
    (hroot : p∈wrappedRecovery N m t k s i) :
    p∈mergedRecovery N m t s (combinedIndex m s.residue k i) := by
  apply List.mem_flatMap.mpr
  refine ⟨k,mergedWraps_mem hm hj hcop hk,?_⟩
  rw [unmergeIndex_exact (by omega)]
  exact hroot

/-- There are exactly three retained wraps at any decoded index. -/
theorem mergedWraps_length (m j : ℕ) (z : ℤ) : (mergedWraps m j z).length=3 := by
  simp only [mergedWraps,List.length_map,List.length_range]

/-- Complete literal quadratic recovery requires at most six candidates. -/
theorem mergedRecovery_length_le_six {G : Type*} (N m t : ℕ)
    (s : ProgressionSeed G) (z : ℤ) : (mergedRecovery N m t s z).length≤6 := by
  unfold mergedRecovery
  rw [List.length_flatMap]
  have hb : ∀ k∈mergedWraps m s.residue z,
      (wrappedRecovery N m t k s (unmergeIndex m s.residue k z)).length≤2 := by
    intro k _
    exact wrappedRecovery_length_le_two _ _ _ _ _ _
  have hh := List.sum_le_card_nsmul
    ((mergedWraps m s.residue z).map fun k =>
      (wrappedRecovery N m t k s (unmergeIndex m s.residue k z)).length) 2
    (by intro n hn; obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hn; exact hb k hk)
  simpa only [List.length_map,mergedWraps_length,smul_eq_mul] using hh

/-- Normalize a signed half interval to the nonnegative interval reader. -/
def mergedTarget {G : Type*} [CommGroup G] (g : G) (m t : ℕ)
    (s : ProgressionSeed G) (upper : Bool) : G :=
  s.step^t*(commonStep g m)^(-mergedStart m upper)

/-- The normalized reader retains the original absolute signed index. -/
theorem mergedTarget_root {G : Type*} [CommGroup G] (g : G) (m t : ℕ)
    (s : ProgressionSeed G) (upper : Bool) (r : ℕ) {z : ℤ}
    (hz : z=mergedStart m upper+r) (hhit : s.step^t=(commonStep g m)^z) :
    mergedTarget g m t s upper=(commonStep g m)^r := by
  simp only [mergedTarget,hhit,hz,←zpow_natCast,←zpow_add]
  congr 1
  ring

/-- The merged target is constructed over the original public global
ring and commutes with the unavailable factor-field projection. -/
theorem mergedTarget_map {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G→*H) (g : G) (N m j t : ℕ) (upper : Bool) :
    φ (mergedTarget g m t (progressionSeed g N m j) upper)=
      mergedTarget (φ g) m t (progressionSeed (φ g) N m j) upper := by
  simp only [mergedTarget,commonStep,progressionSeed,map_mul,map_pow,map_zpow]

/-- A retained original collision gives the corresponding common-base
root in either half, with no division by the vanishing detector. -/
theorem mergedTarget_map_root {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G→*H) (g : G) (N m j t k : ℕ) (i : ℤ) (upper : Bool) (r : ℕ)
    (hz : combinedIndex m j k i=mergedStart m upper+r)
    (hhit : φ (wrappedValue t k (progressionSeed g N m j))=(φ g)^((m : ℤ)^2*i)) :
    φ (mergedTarget g m t (progressionSeed g N m j) upper)=
      (φ (commonStep g m))^r := by
  rw [wrappedValue_map] at hhit
  have he := (merged_hit_iff (φ g) N m j t k i).mp hhit
  rw [mergedTarget_map]
  simpa only [commonStep,map_zpow] using
    mergedTarget_root (φ g) m t (progressionSeed (φ g) N m j) upper r hz he

/-- The common base keeps both routed rough local periods, so each
merged half has simple roots without a new order oracle or stronger route. -/
theorem long_common_periods {p q m : ℕ} (hm : 1<m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let beta := commonStep (projectedUnit g m) m
    mergedLength m≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (beta : ZMod (p*q))) ∧
    mergedLength m≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (beta : ZMod (p*q))) := by
  have heP : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((commonStep (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)))=
      orderOf (leftUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
      ((projectedUnit g m)^m) : (ZMod p)ˣ) : ZMod p)=_
    rw [orderOf_units,map_pow]
    exact (rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.1).orderOf_pow
  have heQ : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((commonStep (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)))=
      orderOf (rightUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom)
      ((projectedUnit g m)^m) : (ZMod q)ˣ) : ZMod q)=_
    rw [orderOf_units,map_pow]
    exact (rough_coprime_small (by omega : 0<m) le_rfl hlong.2.2.2.2.2.2).orderOf_pow
  dsimp only
  rw [heP,heQ]
  have hP := hlong.2.2.2.1.1
  have hQ := hlong.2.2.2.1.2
  unfold mergedLength
  constructor <;> nlinarith only [hP,hQ]

/-- The old bounded integer-index stage covers either merged half. -/
theorem merged_interval_cover (m : ℕ) : mergedLength m≤(2*m)^2 := by
  unfold mergedLength
  nlinarith

/-- One merged half reads three scalars, then retains all possible full
wrap tags if the collision is globally shared. Every candidate is checked. -/
noncomputable def recoverMergedHalf {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool) : Option ℕ :=
  match recoverTaggedInterval (commonStep g m) (mergedTarget g m t s upper)
      (mergedLength m) (2*m) with
  | none => none
  | some (Sum.inl d) => some d
  | some (Sum.inr r) => recoverCandidates N (mergedRecovery N m t s (mergedStart m upper+r))

/-- Every merged half result is a checked proper divisor. -/
theorem recoverMergedHalf_sound {N m t d : ℕ} (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool)
    (h : recoverMergedHalf g m t s upper=some d) : ProperDivisor N d := by
  unfold recoverMergedHalf at h
  split at h
  · cases h
  · rename_i e he
    have hd := Option.some.inj h
    subst d
    exact recoverTaggedInterval_factor_sound _ _ he
  · exact recoverCandidates_sound h

/-- At a proved original witness, the half reader succeeds through
nonsaturation, mixed-index saturation and an exact common global index. -/
theorem recoverMergedHalf_succeeds_of_exact_hit {p q m t k : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p<q) (hm : 1<m) (g : (ZMod (p*q))ˣ)
    (j : ℕ) (hj : 1≤j) (hcop : (j-1).Coprime m) (i : ℤ) (hk : k≤2*m+1)
    (upper : Bool) (r : ℕ) (hr : r<mergedLength m)
    (hz : combinedIndex m j k i=mergedStart m upper+r)
    (hLP : mergedLength m≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((commonStep g m : (ZMod (p*q))ˣ) : ZMod (p*q))))
    (hLQ : mergedLength m≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((commonStep g m : (ZMod (p*q))ˣ) : ZMod (p*q))))
    (hhit : (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
      (wrappedValue t k (progressionSeed g (p*q) m j))=
        ((Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom) g)^((m : ℤ)^2*i))
    (hroot : (p : ℤ)∈wrappedRecovery (p*q) m t k (progressionSeed g (p*q) m j) i) :
    ∃ d, recoverMergedHalf g m t (progressionSeed g (p*q) m j) upper=some d := by
  have hpow := mergedTarget_map_root
    (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
    g (p*q) m j t k i upper r hz hhit
  have hval := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hpow
  simp only [Units.coe_map,Units.val_pow_eq_pow_val] at hval
  have hd := recoverTaggedInterval_preserves_root hp hq hpq _ _ hr
    (merged_interval_cover m) hLP hLQ hval
  rcases hd with ⟨d,hd⟩|hd
  · exact ⟨d,by simp only [recoverMergedHalf,hd]⟩
  · have hproper : ProperDivisor (p*q) p :=
      ⟨hp.one_lt,by nlinarith only [hq.one_lt,hp.pos],dvd_mul_right p q⟩
    have hmem := mergedRecovery_preserves_root (progressionSeed g (p*q) m j) i p
      hm hj hcop hk hroot
    change (p : ℤ)∈mergedRecovery (p*q) m t (progressionSeed g (p*q) m j)
      (combinedIndex m j k i) at hmem
    rw [hz] at hmem
    obtain ⟨d,he⟩ := recoverCandidates_succeeds hproper hmem
    exact ⟨d,by simpa only [recoverMergedHalf,hd] using he⟩

/-- Acquire a merged half from one common m-root polynomial and 3m
normalized points, without expanding its quadratic interval. -/
noncomputable def mergedJet {R : Type*} [CommRing R] (beta : Rˣ) (x : R)
    (m : ℕ) : R×R×R :=
  SemiprimeSharedIntervalJet.sharedBlockedJet beta x m (3*m)

/-- The same shared polynomial works for every residue, denominator and
half, and its product and marked derivatives are exact through zeros. -/
theorem mergedJet_exact {R : Type*} [CommRing R] (beta : Rˣ) (x : R)
    {m : ℕ} (hm : 0<m) :
    mergedJet beta x m=(intervalProduct (beta : R) x (mergedLength m),
      targetDerivative (beta : R) x (mergedLength m),
      baseDerivative (beta : R) x (mergedLength m)) := by
  unfold mergedJet
  rw [SemiprimeSharedIntervalJet.sharedBlockedJet_exact beta x hm]
  have he : (3*m)*m=mergedLength m := by unfold mergedLength; ring
  rw [he]

/-- Read the three acquired merged-half scalars with the exact tag decoder. -/
noncomputable def recoverBlockedMergedHalf {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool) : Option ℕ :=
  let beta := commonStep g m
  let x := mergedTarget g m t s upper
  match recoverTaggedJet beta x (mergedLength m) (2*m)
      (mergedJet beta (x : ZMod N) m) with
  | none => none
  | some (Sum.inl d) => some d
  | some (Sum.inr r) => recoverCandidates N (mergedRecovery N m t s (mergedStart m upper+r))

/-- Blocked acquisition preserves the precise saturation-complete reader. -/
theorem recoverBlockedMergedHalf_eq {N m t : ℕ} (hm : 0<m) (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool) :
    recoverBlockedMergedHalf g m t s upper=recoverMergedHalf g m t s upper := by
  simp only [recoverBlockedMergedHalf,mergedJet_exact _ _ hm,
    recoverMergedHalf,recoverTaggedInterval]

/-- The reduced public target stream contains only residue/denominator
pairs and two half flags. Cached seeds are retained without an i axis. -/
def mergedColumns {G : Type*} [CommGroup G] (g : G) (N m : ℕ) :
    List (ℕ×ProgressionSeed G×Bool) :=
  (progressionSeeds g N m).flatMap fun s =>
    (List.range (m-1)).flatMap fun r => [(r+1,s,false),(r+1,s,true)]

/-- Every cached seed and positive denominator is queried in both halves. -/
theorem mergedColumn_mem {G : Type*} [CommGroup G] {g : G} {N m t : ℕ}
    {s : ProgressionSeed G} (hs : s∈progressionSeeds g N m) (ht : 0<t) (htm : t<m)
    (upper : Bool) : (t,s,upper)∈mergedColumns g N m := by
  apply List.mem_flatMap.mpr
  refine ⟨s,hs,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨t-1,List.mem_range.mpr (by omega),?_⟩
  have he : t-1+1=t := by omega
  rw [he]
  cases upper <;> simp

/-- Exact target record count; the former short-index axis is absent. -/
theorem mergedColumns_length {G : Type*} [CommGroup G] (g : G) (N m : ℕ) :
    (mergedColumns g N m).length=2*(m-1)^2 := by
  simp [mergedColumns,progressionSeeds,List.length_flatMap,pow_two,Function.comp_def]
  ring

/-- A public scan of the reduced target stream, using the blocked common
polynomial reader. Its executable backend and whole bit bound remain open. -/
noncomputable def scanMergedColumns {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)→Option ℕ
  | [] => none
  | (t,s,upper)::xs => match recoverBlockedMergedHalf g m t s upper with
    | some d => some d
    | none => scanMergedColumns g m xs

/-- Every factor returned by the complete reduced stream is proper. -/
theorem scanMergedColumns_sound {N m d : ℕ} (hm : 0<m) (g : (ZMod N)ˣ)
    {xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)}
    (h : scanMergedColumns g m xs=some d) : ProperDivisor N d := by
  induction xs with
  | nil => simp only [scanMergedColumns] at h; cases h
  | cons a xs ih =>
    rcases a with ⟨t,s,upper⟩
    unfold scanMergedColumns at h
    split at h
    · rename_i e he
      have hd := Option.some.inj h
      subst d
      rw [recoverBlockedMergedHalf_eq hm] at he
      exact recoverMergedHalf_sound _ _ _ he
    · exact ih h

/-- A successful member guarantees success of the entire public stream,
without an assumed tie order or a hidden successful tag supplied as input. -/
theorem scanMergedColumns_succeeds_of_member {N m t d : ℕ} (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool)
    {xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)}
    (hmem : (t,s,upper)∈xs) (hd : recoverBlockedMergedHalf g m t s upper=some d) :
    ∃ e, scanMergedColumns g m xs=some e := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons a xs ih =>
    rcases a with ⟨t',s',upper'⟩
    rw [scanMergedColumns]
    cases he : recoverBlockedMergedHalf g m t' s' upper' with
    | some e => exact ⟨e,rfl⟩
    | none =>
      have hh := List.mem_cons.mp hmem
      rcases hh with hh|hh
      · cases hh
        rw [hd] at he
        cases he
      · exact ih hh

/-- The actual matched-width long route has a successful merged target.
Every factor ratio and exact quadratic witness comes from the arithmetic
forcing theorem, not from a supplied successful collision certificate. -/
theorem long_public_route_merged_column {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ (t : ℕ) (upper : Bool),
        (t,progressionSeed h (p*q) m (p%m),upper)∈mergedColumns h (p*q) m ∧
        ∃ d, recoverBlockedMergedHalf h m t (progressionSeed h (p*q) m (p%m)) upper=some d := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 1<m := by dsimp only [m]; omega
  have hsize : p*q≤m^6 := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  have hcover : m^2<p*q := public_modulus_prefix_below_input hN hB
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hj : 1<p%m := by
    have he := long_true_residue_ne_one hp hpq.le hm hprefix.le hsize g hlong
    have hmm : m≤m^2 := by nlinarith only [hm]
    have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer
      hcover hnone (by omega : 0<m) hmm
    have hjcop : (p%m).Coprime m := by
      change Nat.gcd (p%m) m=1
      rw [←Nat.gcd_rec]
      exact hcop.symm.of_dvd_right (dvd_mul_right p q)
    have hjpos : 0<p%m := by
      by_contra! hn
      have hz : p%m=0 := by omega
      simp only [hz,Nat.coprime_zero_left] at hjcop
      omega
    omega
  have hmprime : m.Prime := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcop : (p%m-1).Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
      (by omega : 0<p%m-1) (by have hh := Nat.mod_lt p (by omega : 0<m); omega))).symm
  have hperiods := long_common_periods hm g hlong
  obtain ⟨t,k,i,hcache,_hrow,ht,htm,_htx,hk,hi,hhit,hroot⟩ :=
    actual_public_hyperbolic_after_prefix hp hq hpq.le hB hnone (projectedUnit g m)
  have hz := combinedIndex_bounds hm hj.le (Nat.mod_lt p (by omega)) hk hi
  obtain ⟨upper,r,hr,hz⟩ := combinedIndex_half hz.1 hz.2
  obtain ⟨d,hd⟩ := recoverMergedHalf_succeeds_of_exact_hit hp hq hpq hm
    (projectedUnit g m) (p%m) hj.le hcop i hk upper r hr hz
      hperiods.1 hperiods.2 hhit hroot
  refine ⟨hc,t,upper,mergedColumn_mem hcache ht htm upper,d,?_⟩
  rw [recoverBlockedMergedHalf_eq (by omega)]
  exact hd

/-- A finite N-only scan of the reduced target records is complete on
the actual long branch, including saturated and common global hits. -/
theorem long_public_route_scan_succeeds {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ d, scanMergedColumns h m (mergedColumns h (p*q) m)=some d ∧ ProperDivisor (p*q) d := by
  obtain ⟨hc,t,upper,hmem,d,hd⟩ := long_public_route_merged_column hp hq hpq hB hnone hroute
  obtain ⟨e,he⟩ := scanMergedColumns_succeeds_of_member _ _ _ hmem hd
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds (Nat.mul_pos hp.pos hq.pos)
  exact ⟨hc,e,he,scanMergedColumns_sound (by omega) _ he⟩

/-- A SINGLE common interval polynomial, its target derivative and its
marked base derivative serve every merged target. This is a specification
of their coefficients; a fast executable construction is not assumed. -/
noncomputable def mergedPolynomials {R : Type*} [CommRing R] (beta : R) (m : ℕ) :
    R[X]×R[X]×R[X] :=
  let P := SemiprimeCartesianCompletion.rootPolynomial (Finset.range (mergedLength m))
    (fun r => beta^r)
  (P,P.derivative,SemiprimeSharedIntervalJet.babyBasePolynomial beta (mergedLength m))

/-- Evaluate the three separately retained channels at one public target. -/
noncomputable def evaluateMergedPolynomials {R : Type*} [CommRing R]
    (P : R[X]×R[X]×R[X]) (x : R) : R×R×R :=
  (P.1.eval x,P.2.1.eval x,P.2.2.eval x)

/-- Batch polynomial evaluation supplies each original merged detector
and both exact derivatives over EVERY commutative ring, through all zeros. -/
theorem mergedPolynomials_eval_exact {R : Type*} [CommRing R] (beta x : R) (m : ℕ) :
    evaluateMergedPolynomials (mergedPolynomials beta m) x=
      (intervalProduct beta x (mergedLength m),targetDerivative beta x (mergedLength m),
        baseDerivative beta x (mergedLength m)) := by
  simp only [evaluateMergedPolynomials,mergedPolynomials,
    ←targetDerivative_eq_derivative,SemiprimeSharedIntervalJet.babyBasePolynomial_eval]
  simp only [SemiprimeCartesianCompletion.rootPolynomial,Polynomial.eval_prod,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,intervalProduct]

/-- Read a supplied triple alongside its ORIGINAL target record. Scalar
acquisition can be shared while the two index channels stay unpooled. -/
noncomputable def readMergedJet {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (c : ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool) (jet : ZMod N×ZMod N×ZMod N) : Option ℕ :=
  match recoverTaggedJet (commonStep g m) (mergedTarget g m c.1 c.2.1 c.2.2)
      (mergedLength m) (2*m) jet with
  | none => none
  | some (Sum.inl d) => some d
  | some (Sum.inr r) => recoverCandidates N
      (mergedRecovery N m c.1 c.2.1 (mergedStart m c.2.2+r))

/-- Shared polynomial evaluation gives the original tag-preserving reader. -/
theorem readMergedJet_exact {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool) :
    readMergedJet g m (t,s,upper)
      (evaluateMergedPolynomials
        (mergedPolynomials ((commonStep g m : (ZMod N)ˣ) : ZMod N) m)
        ((mergedTarget g m t s upper : (ZMod N)ˣ) : ZMod N))=
      recoverMergedHalf g m t s upper := by
  simp only [readMergedJet,mergedPolynomials_eval_exact,recoverMergedHalf,recoverTaggedInterval]

/-- Retain the target tag beside each of the three evaluated scalars.
The three common polynomials are constructed once before the target map. -/
noncomputable def mergedBatchJets {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List ((ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)×(ZMod N×ZMod N×ZMod N)) :=
  let P := mergedPolynomials ((commonStep g m : (ZMod N)ˣ) : ZMod N) m
  (mergedColumns g N m).map fun c =>
    (c,evaluateMergedPolynomials P ((mergedTarget g m c.1 c.2.1 c.2.2 : (ZMod N)ˣ) : ZMod N))

/-- Read an aligned batch of tagged triples. No sum or product of the
different zero targets replaces their separately retained index channels. -/
noncomputable def scanMergedJetBatch {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List ((ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)×(ZMod N×ZMod N×ZMod N))→Option ℕ
  | [] => none
  | (c,jet)::xs => match readMergedJet g m c jet with
    | some d => some d
    | none => scanMergedJetBatch g m xs

/-- Aligned common-polynomial acquisition equals the proved blocked
scan on every public target list, including saturation and global matches. -/
theorem scanMergedJetBatch_map_exact {N m : ℕ} (hm : 0<m) (g : (ZMod N)ˣ)
    (xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)) :
    scanMergedJetBatch g m (xs.map fun c =>
      (c,evaluateMergedPolynomials
        (mergedPolynomials ((commonStep g m : (ZMod N)ˣ) : ZMod N) m)
        ((mergedTarget g m c.1 c.2.1 c.2.2 : (ZMod N)ˣ) : ZMod N)))=
      scanMergedColumns g m xs := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    rcases c with ⟨t,s,upper⟩
    simp only [List.map_cons,scanMergedJetBatch,readMergedJet_exact,
      scanMergedColumns,recoverBlockedMergedHalf_eq hm]
    cases he : recoverMergedHalf g m t s upper with
    | some d => rfl
    | none => exact ih

/-- The whole labelled batch computes the same complete public scan. -/
theorem mergedBatch_scan_exact {N m : ℕ} (hm : 0<m) (g : (ZMod N)ˣ) :
    scanMergedJetBatch g m (mergedBatchJets g m)=
      scanMergedColumns g m (mergedColumns g N m) := by
  exact scanMergedJetBatch_map_exact hm g _

/-- Every factor returned after common-polynomial acquisition is proper. -/
theorem mergedBatch_scan_sound {N m d : ℕ} (hm : 0<m) (g : (ZMod N)ˣ)
    (h : scanMergedJetBatch g m (mergedBatchJets g m)=some d) : ProperDivisor N d := by
  rw [mergedBatch_scan_exact hm] at h
  exact scanMergedColumns_sound hm g h

/-- Shared whole-batch acquisition preserves the guaranteed factor on
every actual public long output and every remaining factor ratio. -/
theorem long_public_route_batch_succeeds {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ d, scanMergedJetBatch h m (mergedBatchJets h m)=some d ∧ ProperDivisor (p*q) d := by
  obtain ⟨hc,d,hd,hproper⟩ := long_public_route_scan_succeeds hp hq hpq hB hnone hroute
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds (Nat.mul_pos hp.pos hq.pos)
  exact ⟨hc,d,by rwa [mergedBatch_scan_exact (by omega)],hproper⟩

/-- There is one triple per reduced target, retaining every target tag. -/
theorem mergedBatchJets_length {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    (mergedBatchJets g m).length=2*(m-1)^2 := by
  simp only [mergedBatchJets,List.length_map,mergedColumns_length]

/-- Root inputs, target points, cached seeds and one constant have a
quadratic whole-family count. No per-residue wrap polynomial is needed.
This input count is not a polynomial arithmetic or bit-cost certificate. -/
theorem merged_whole_input_bound {G : Type*} [CommGroup G] (g : G) (N m : ℕ) (hm : 0<m) :
    mergedLength m+(mergedColumns g N m).length+(progressionSeeds g N m).length+1≤
      5*m^2+m := by
  rw [mergedColumns_length,progressionSeeds_length,mergedLength]
  have he : m-1+1=m := by omega
  have hs := Nat.pow_le_pow_left (Nat.sub_le m 1) 2
  nlinarith only [he,hs]

/-- A full common-interval polynomial necessarily has quadratic degree
on the actual long branch. This restricts that representation, not every
implicit circuit capable of acquiring the required collision. -/
theorem common_polynomial_degree_floor {p q m : ℕ} (hm : 1<m) (hp : p.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (P : (ZMod p)[X]) (hP : P≠0)
    (hzero : ∀ r<mergedLength m, P.eval
      ((ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((commonStep (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)))^r)=0) :
    mergedLength m≤P.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  exact interval_annihilator_degree _ (long_common_periods hm g hlong).1 P hP hzero

end RiemannGaussian.SemiprimeMergedIndexAcquisition
