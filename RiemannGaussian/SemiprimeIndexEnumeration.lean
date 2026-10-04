/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeIndexLattice

/-!
# Direct enumeration in the public short CRT-index basis

Signed floor/ceiling bounds enumerate the basis lines intersecting the
original coefficient rectangle. Each line is clipped before its integer
coordinates are visited. Native iteration counts are separate from a
Boolean bit clock and from the unpaid original interval-jet acquisition.
-/

namespace RiemannGaussian.SemiprimeIndexEnumeration

open SemiprimeIndexLattice
open scoped BigOperators

/-- Inclusive signed bounds of a directly enumerated interval. -/
structure IntegerInterval where
  /-- First possible integer coordinate. -/
  lower : ℤ
  /-- Last possible integer coordinate; below lower for an empty interval. -/
  upper : ℤ

/-- Ceiling division, with a positive denominator in its correctness lemmas. -/
def ceilDivide (a d : ℤ) : ℤ := -((-a)/d)

/-- Native signed maximum, used only for clipping integer bounds. -/
def maxInteger (a b : ℤ) : ℤ := if a≤b then b else a

/-- Native signed minimum, used only for clipping integer bounds. -/
def minInteger (a b : ℤ) : ℤ := if a≤b then a else b

/-- The explicit impossible bounds [1,0]. -/
def emptyInterval : IntegerInterval := ⟨1,0⟩

/-- Directly visit every integer in inclusive signed bounds once. -/
def IntegerInterval.entries (bounds : IntegerInterval) : List ℤ :=
  (List.range (bounds.upper+1-bounds.lower).toNat).map
    (fun i : ℕ => bounds.lower+(i : ℤ))

/-- Clip two signed intervals without constructing either source list. -/
def intersectInterval (first second : IntegerInterval) : IntegerInterval :=
  ⟨maxInteger first.lower second.lower,minInteger first.upper second.upper⟩

/-- Exact positive-denominator ceiling inequality, including negative
numerators. -/
theorem ceilDivide_le_iff {a d i : ℤ} (hd : 0<d) :
    ceilDivide a d ≤ i ↔ a ≤ i*d := by
  unfold ceilDivide
  have hh := Int.le_ediv_iff_mul_le hd (a:= -i) (b:= -a)
  constructor
  · intro h
    have hi : -i ≤ (-a)/d := by omega
    have hm := hh.mp hi
    nlinarith
  · intro h
    have hm : (-i)*d≤-a := by nlinarith
    have hi := hh.mpr hm
    omega

/-- Literal interval membership is the original pair of inclusive
integer inequalities; there is no retained rectangle filter. -/
theorem mem_interval_entries (bounds : IntegerInterval) (i : ℤ) :
    i∈bounds.entries ↔ bounds.lower ≤ i ∧ i ≤ bounds.upper := by
  constructor
  · intro hi
    obtain ⟨n,hn,he⟩ := List.mem_map.mp hi
    have hn' := List.mem_range.mp hn
    change bounds.lower+(n : ℤ)=i at he
    omega
  · intro hi
    apply List.mem_map.mpr
    refine ⟨(i-bounds.lower).toNat,?_,?_⟩
    · apply List.mem_range.mpr
      omega
    · omega

/-- Native interval length counts actual integer visits, including empty
or entirely negative intervals. -/
theorem interval_entries_length (bounds : IntegerInterval) :
    bounds.entries.length=(bounds.upper+1-bounds.lower).toNat := by
  simp [IntegerInterval.entries]

/-- Every directly enumerated integer coordinate occurs once. -/
theorem interval_entries_nodup (bounds : IntegerInterval) : bounds.entries.Nodup := by
  dsimp only [IntegerInterval.entries]
  apply List.Nodup.map _ List.nodup_range
  intro x y h
  dsimp only at h
  omega

/-- The impossible interval makes no visits. -/
theorem emptyInterval_entries : emptyInterval.entries=[] := by
  simp [emptyInterval,IntegerInterval.entries]

/-- A clipped interval visits exactly the simultaneous source bounds. -/
theorem mem_intersectInterval_entries (first second : IntegerInterval) (i : ℤ) :
    i∈(intersectInterval first second).entries ↔
      i∈first.entries ∧ i∈second.entries := by
  simp only [mem_interval_entries,intersectInterval,maxInteger,minInteger]
  split <;> split <;> omega

/-- The signed coordinate interval for lower<=offset+i*step<=upper,
when step is positive. -/
def positiveLinearInterval (offset step lower upper : ℤ) : IntegerInterval :=
  ⟨ceilDivide (lower-offset) step,(upper-offset)/step⟩

/-- Positive-step clipping uses exact floor/ceiling quotients. -/
theorem mem_positiveLinearInterval {offset step lower upper i : ℤ} (hstep : 0<step) :
    i∈(positiveLinearInterval offset step lower upper).entries ↔
      lower ≤ offset+i*step ∧ offset+i*step ≤ upper := by
  rw [mem_interval_entries]
  change ceilDivide (lower-offset) step ≤ i ∧ i ≤ (upper-offset)/step ↔ _
  rw [ceilDivide_le_iff hstep,Int.le_ediv_iff_mul_le hstep]
  omega

/-- Exact signed line clipping; a zero step is handled by one constant
coordinate test before constructing any integer list. -/
def linearInterval (offset step lower upper : ℤ) (initial : IntegerInterval) : IntegerInterval :=
  if 0<step then
    intersectInterval initial (positiveLinearInterval offset step lower upper)
  else if step<0 then
    intersectInterval initial (positiveLinearInterval (-offset) (-step) (-upper) (-lower))
  else if lower≤offset ∧ offset≤upper then initial else emptyInterval

/-- Signed and zero-step line clipping preserves exactly both coordinate
inequalities, and every original initial bound. -/
theorem mem_linearInterval (offset step lower upper i : ℤ) (initial : IntegerInterval) :
    i∈(linearInterval offset step lower upper initial).entries ↔
      i∈initial.entries ∧ lower ≤ offset+i*step ∧ offset+i*step ≤ upper := by
  unfold linearInterval
  split
  · rw [mem_intersectInterval_entries,mem_positiveLinearInterval (by assumption)]
  · split
    · rw [mem_intersectInterval_entries,mem_positiveLinearInterval (by omega)]
      have he : -offset+i*(-step)= -(offset+i*step) := by ring
      rw [he]
      constructor
      · rintro ⟨hi,hlo,hhi⟩
        exact ⟨hi,by omega,by omega⟩
      · rintro ⟨hi,hlo,hhi⟩
        exact ⟨hi,by omega,by omega⟩
    · have hz : step=0 := by omega
      rw [hz,mul_zero,add_zero]
      split
      · tauto
      · rw [emptyInterval_entries]
        simp only [List.not_mem_nil,false_iff]
        tauto

/-- The signed determinant of the actual public basis. -/
def basisDeterminant (basis : ShortRelationReport) : ℤ :=
  (basis.coefficient : ℤ)*basis.companionSecond-basis.second*basis.previousCoefficient

/-- Lowest possible short-vector determinant over the original rectangle. -/
def rectangleDeterminantLower (s L : ℕ) (basis : ShortRelationReport) : ℤ :=
  (basis.coefficient : ℤ)*(s : ℤ)^2+
    minInteger 0 (-basis.second)*(2*(L : ℤ)-1)

/-- Highest possible short-vector determinant over the original rectangle. -/
def rectangleDeterminantUpper (s L : ℕ) (basis : ShortRelationReport) : ℤ :=
  (basis.coefficient : ℤ)*((s : ℤ)^2+(L : ℤ)^2-1)+
    maxInteger 0 (-basis.second)*(2*(L : ℤ)-1)

/-- Directly bound the possible basis lines, retaining determinant sign. -/
def bandInterval (N s L : ℕ) (basis : ShortRelationReport) : IntegerInterval :=
  if basis.negative then
    positiveLinearInterval 0 N (rectangleDeterminantLower s L basis)
      (rectangleDeterminantUpper s L basis)
  else
    positiveLinearInterval 0 N (-rectangleDeterminantUpper s L basis)
      (-rectangleDeterminantLower s L basis)

/-- Recover the original sum/product coefficient point, retaining its
integer basis coordinates and exact affine origin. -/
def coefficientPoint (s : ℕ) (basis : ShortRelationReport) (t : ℤ×ℤ) : ℤ×ℤ :=
  (t.1*(basis.coefficient : ℤ)+t.2*basis.previousCoefficient,
    -(s : ℤ)^2+t.1*basis.second+t.2*basis.companionSecond)

/-- Intersect both original rectangle constraints before visiting a line. -/
def lineInterval (s L : ℕ) (basis : ShortRelationReport) (j : ℤ) : IntegerInterval :=
  let first := positiveLinearInterval (j*(basis.previousCoefficient : ℤ)) basis.coefficient
    0 (2*(L : ℤ)-1)
  linearInterval (-(s : ℤ)^2+j*basis.companionSecond) basis.second
    0 ((L : ℤ)^2-1) first

/-- Direct nested enumeration visits only clipped integer coordinates. -/
def enumerateCoordinates (N s L : ℕ) (basis : ShortRelationReport) : List (ℤ×ℤ) :=
  (bandInterval N s L basis).entries.flatMap (fun j =>
    (lineInterval s L basis j).entries.map (fun i => (i,j)))

/-- Actual public native enumeration, with its retained basis, coordinates,
points and actual loop-iteration counts. -/
structure EnumerationReport where
  /-- The one actual early-Euclid basis run. -/
  basis : ShortRelationReport
  /-- Original signed integer coordinates of every visited point. -/
  coordinates : List (ℤ×ℤ)
  /-- Original sum/product pairs in the coefficient rectangle. -/
  points : List (ℤ×ℤ)
  /-- Actual number of basis lines initialized, including empty lines. -/
  lines : ℕ
  /-- Actual number of integer coordinates visited on those lines. -/
  visits : ℕ

/-- Compute the short basis once, then enumerate the exact signed bands
and clipped lines. No rectangle product or candidate filter is constructed. -/
def enumerateCoefficients (N s L : ℕ) : EnumerationReport :=
  let basis := shortRelation N s (2*L)
  let bands := (bandInterval N s L basis).entries
  let coordinates := bands.flatMap (fun j =>
    (lineInterval s L basis j).entries.map (fun i => (i,j)))
  ⟨basis,coordinates,coordinates.map (coefficientPoint s basis),
    bands.length,coordinates.length⟩

/-- A line interval visits exactly the original rectangle coordinates. -/
theorem mem_lineInterval {s L : ℕ} {basis : ShortRelationReport}
    (hu : 0<basis.coefficient) (i j : ℤ) :
    i∈(lineInterval s L basis j).entries ↔
      inCoefficientRectangle L (coefficientPoint s basis (i,j)).1
        (coefficientPoint s basis (i,j)).2 := by
  have hui : (0 : ℤ)<basis.coefficient := by exact_mod_cast hu
  rw [lineInterval,mem_linearInterval,mem_positiveLinearInterval hui]
  dsimp only [coefficientPoint,inCoefficientRectangle]
  constructor
  · rintro ⟨⟨h1,h2⟩,h3,h4⟩
    exact ⟨by omega,by omega,by omega,by omega⟩
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨⟨by omega,by omega⟩,by omega,by omega⟩

/-- The coefficient rectangle lies inside the exact signed determinant
extrema used to initialize the public basis-line loop. -/
theorem rectangle_determinant_bounds {s L : ℕ} {basis : ShortRelationReport}
    {a b : ℤ} (ha : inCoefficientRectangle L a b) :
    rectangleDeterminantLower s L basis≤(basis.coefficient : ℤ)*(b+(s : ℤ)^2)-basis.second*a ∧
      (basis.coefficient : ℤ)*(b+(s : ℤ)^2)-basis.second*a≤rectangleDeterminantUpper s L basis := by
  obtain ⟨ha0,ha1,hb0,hb1⟩ := ha
  dsimp only [rectangleDeterminantLower,rectangleDeterminantUpper,minInteger,maxInteger]
  have hu : (0 : ℤ)≤basis.coefficient := by positivity
  split <;> constructor <;> nlinarith

/-- The native band interval is exactly the determinant inequality,
with the original positive or negative orientation. -/
theorem mem_bandInterval {N s L : ℕ} (hN : 0<N) (basis : ShortRelationReport)
    (hdet : basisDeterminant basis=if basis.negative then (N : ℤ) else -(N : ℤ)) (j : ℤ) :
    j∈(bandInterval N s L basis).entries ↔
      rectangleDeterminantLower s L basis≤j*basisDeterminant basis ∧
        j*basisDeterminant basis≤rectangleDeterminantUpper s L basis := by
  have hn : (0 : ℤ)<N := by exact_mod_cast hN
  unfold bandInterval
  split
  · rename_i hnegative
    rw [if_pos hnegative] at hdet
    rw [mem_positiveLinearInterval hn,hdet]
    simp only [zero_add]
  · rename_i hnegative
    rw [if_neg hnegative] at hdet
    rw [mem_positiveLinearInterval hn,hdet]
    simp only [zero_add]
    constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]

/-- Native nested-list membership exposes exactly its original band and
line coordinates, without a full-matrix predicate. -/
theorem mem_enumerateCoordinates (N s L : ℕ) (basis : ShortRelationReport) (t : ℤ×ℤ) :
    t∈enumerateCoordinates N s L basis ↔
      t.2∈(bandInterval N s L basis).entries ∧ t.1∈(lineInterval s L basis t.2).entries := by
  constructor
  · intro h
    obtain ⟨j,hj,ht⟩ := List.mem_flatMap.mp h
    obtain ⟨i,hi,he⟩ := List.mem_map.mp ht
    cases he
    exact ⟨hj,hi⟩
  · intro h
    exact List.mem_flatMap.mpr ⟨t.2,h.1,List.mem_map.mpr ⟨t.1,h.2,Prod.eta t⟩⟩

/-- The point formula and its second coordinate retain the actual signed
short-vector determinant. -/
theorem coefficientPoint_determinant (s : ℕ) (basis : ShortRelationReport) (t : ℤ×ℤ) :
    (basis.coefficient : ℤ)*((coefficientPoint s basis t).2+(s : ℤ)^2)-
      basis.second*(coefficientPoint s basis t).1=t.2*basisDeterminant basis := by
  dsimp only [coefficientPoint,basisDeterminant]
  ring

/-- Orientation of the one actual public basis, including zero current
remainder and every public numerator. -/
theorem public_basis_determinant (N s L : ℕ) :
    let basis := shortRelation N s (2*L)
    basisDeterminant basis=if basis.negative then (N : ℤ) else -(N : ℤ) := by
  exact shortRelationLoop_determinant (N/(2*L+1)) N (s%N) 0 1 false
    (show N*1+(s%N)*0=N by omega)

/-- Every visited coordinate gives a point in the original rectangle
and original affine congruence. No downstream candidate filter is needed. -/
theorem enumerateCoordinates_sound {N s L : ℕ} (hN : 0<N) (hL : 0<L)
    (t : ℤ×ℤ) (ht : t∈enumerateCoordinates N s L (shortRelation N s (2*L))) :
    coefficientCandidate (s : ZMod N) L
      (coefficientPoint s (shortRelation N s (2*L)) t).1
      (coefficientPoint s (shortRelation N s (2*L)) t).2 := by
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  have hmem := (mem_enumerateCoordinates _ _ _ _ _).mp ht
  have hr := (mem_lineInterval hb.2.2.1 t.1 t.2).mp hmem.2
  refine ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,?_⟩
  have hfirst := hb.1
  have hsecond := hb.2.1
  unfold indexRelation at hfirst hsecond
  push_cast at hfirst hsecond
  dsimp only [coefficientPoint]
  push_cast
  linear_combination -(t.1 : ZMod N)*hfirst-(t.2 : ZMod N)*hsecond

/-- Every original candidate is reached through its concrete public
Cramer coordinates, not through a supplied coordinate witness. -/
theorem enumerateCoordinates_complete {N s L : ℕ} (hN : 0<N) (hL : 0<L)
    (point : ℤ×ℤ) (hpoint : coefficientCandidate (s : ZMod N) L point.1 point.2) :
    let basis := shortRelation N s (2*L)
    let t := publicCoefficientCoordinates N s L point
    t∈enumerateCoordinates N s L basis ∧ coefficientPoint s basis t=point := by
  let basis := shortRelation N s (2*L)
  let t := publicCoefficientCoordinates N s L point
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  have he := publicCoefficientCoordinates_exact hN hL s point hpoint
  have hp : coefficientPoint s basis t=point := Prod.ext he.1.symm he.2.symm
  have hrect : inCoefficientRectangle L point.1 point.2 :=
    ⟨hpoint.1,hpoint.2.1,hpoint.2.2.1,hpoint.2.2.2.1⟩
  refine ⟨(mem_enumerateCoordinates _ _ _ _ _).mpr ⟨?_,?_⟩,hp⟩
  · rw [mem_bandInterval hN basis (public_basis_determinant N s L)]
    rw [← coefficientPoint_determinant s basis t,hp]
    exact rectangle_determinant_bounds hrect
  · apply (mem_lineInterval hb.2.2.1 t.1 t.2).mpr
    rw [hp]
    exact hrect

/-- The public native point list is exactly the original coefficient
candidate specification, including all saturated and aliased cases. -/
theorem mem_enumerateCoefficients_points {N s L : ℕ} (hN : 0<N) (hL : 0<L)
    (point : ℤ×ℤ) :
    point∈(enumerateCoefficients N s L).points ↔
      coefficientCandidate (s : ZMod N) L point.1 point.2 := by
  change point∈(enumerateCoordinates N s L (shortRelation N s (2*L))).map
    (coefficientPoint s (shortRelation N s (2*L))) ↔ _
  constructor
  · intro hp
    obtain ⟨t,ht,he⟩ := List.mem_map.mp hp
    exact he ▸ enumerateCoordinates_sound hN hL t ht
  · intro hp
    obtain ⟨ht,he⟩ := enumerateCoordinates_complete hN hL point hp
    exact List.mem_map.mpr ⟨publicCoefficientCoordinates N s L point,ht,he⟩

/-- Native lines and points retain the visited-loop counts exactly. -/
theorem enumerateCoefficients_counts (N s L : ℕ) :
    (enumerateCoefficients N s L).points.length=(enumerateCoefficients N s L).visits ∧
      (enumerateCoefficients N s L).coordinates.length=(enumerateCoefficients N s L).visits ∧
      (enumerateCoefficients N s L).lines=
        (bandInterval N s L (shortRelation N s (2*L))).entries.length := by
  simp [enumerateCoefficients]

/-- The width of the two native extrema is the original signed magnitude. -/
theorem integer_extrema_width (x : ℤ) : maxInteger 0 x-minInteger 0 x=|x| := by
  unfold maxInteger minInteger
  by_cases hx : 0≤x
  · rw [if_pos hx,if_pos hx,abs_of_nonneg hx]
    ring
  · rw [if_neg hx,if_neg hx,abs_of_nonpos (by omega)]
    ring

/-- Exact determinant width of the original closed integer rectangle. -/
theorem rectangleDeterminant_width (s L : ℕ) (basis : ShortRelationReport) :
    rectangleDeterminantUpper s L basis-rectangleDeterminantLower s L basis=
      (basis.coefficient : ℤ)*((L : ℤ)^2-1)+|basis.second| * (2*(L : ℤ)-1) := by
  have he := integer_extrema_width (-basis.second)
  rw [abs_neg] at he
  dsimp only [rectangleDeterminantUpper,rectangleDeterminantLower]
  linear_combination (2*(L : ℤ)-1)*he

/-- Direct interval enumeration charges at most one more visit than its
proved pairwise coordinate span, including empty intervals. -/
theorem interval_entries_length_le (bounds : IntegerInterval) (H : ℕ)
    (hspan : ∀ i∈bounds.entries, ∀ j∈bounds.entries, |i-j|≤(H : ℤ)) :
    bounds.entries.length≤H+1 := by
  rw [interval_entries_length]
  by_cases horder : bounds.lower≤bounds.upper
  · have hlo := (mem_interval_entries bounds bounds.lower).mpr ⟨le_rfl,horder⟩
    have hhi := (mem_interval_entries bounds bounds.upper).mpr ⟨horder,le_rfl⟩
    have hh := hspan bounds.upper hhi bounds.lower hlo
    rw [abs_of_nonneg (by omega)] at hh
    omega
  · omega

/-- The short determinant rectangle has constant width in modulus
units whenever the original coefficient volume is bounded. -/
theorem rectangleDeterminant_width_le {N L C s : ℕ} {basis : ShortRelationReport}
    (hub : basis.coefficient≤2*L) (hvb : |basis.second| * (2*(L : ℤ))≤N)
    (hvolume : L^3≤C*N) :
    rectangleDeterminantUpper s L basis-rectangleDeterminantLower s L basis≤
      (2*C+1 : ℕ)*(N : ℤ) := by
  rw [rectangleDeterminant_width]
  have hu : (0 : ℤ)≤basis.coefficient := by positivity
  have hub' : (basis.coefficient : ℤ)≤2*(L : ℤ) := by exact_mod_cast hub
  have hvol : (L : ℤ)^3≤(C : ℤ)*N := by exact_mod_cast hvolume
  push_cast
  nlinarith [abs_nonneg basis.second,Int.natCast_nonneg L,sq_nonneg (L : ℤ)]

/-- Every initialized native band, including empty lines, lies in a
constant-span interval. This bounds the actual OUTER loop length. -/
theorem bandInterval_length_le {N s L C : ℕ} (hN : 0<N) (basis : ShortRelationReport)
    (hub : basis.coefficient≤2*L) (hvb : |basis.second| * (2*(L : ℤ))≤N)
    (hdet : basisDeterminant basis=if basis.negative then (N : ℤ) else -(N : ℤ))
    (hvolume : L^3≤C*N) :
    (bandInterval N s L basis).entries.length≤2*C+2 := by
  have hn : (0 : ℤ)<N := by exact_mod_cast hN
  have habs : |basisDeterminant basis|=(N : ℤ) := by
    rw [hdet]
    split <;> simp only [abs_neg,abs_of_nonneg hn.le]
  have hw := rectangleDeterminant_width_le hub hvb hvolume (s:=s)
  have hlen := interval_entries_length_le (bandInterval N s L basis) (2*C+1) (by
    intro i hi j hj
    have hfirst := (mem_bandInterval hN basis hdet i).mp hi
    have hsecond := (mem_bandInterval hN basis hdet j).mp hj
    have hd : |(i-j)*basisDeterminant basis|≤
        rectangleDeterminantUpper s L basis-rectangleDeterminantLower s L basis := by
      apply abs_le.mpr
      constructor <;> nlinarith [hfirst.1,hfirst.2,hsecond.1,hsecond.2]
    rw [abs_mul,habs] at hd
    nlinarith)
  omega

/-- The actual public short vector meets the magnitude bound used to
charge every outer-loop line initialization. -/
theorem public_short_second_bound {N s L : ℕ} (hN : 0<N) (hL : 0<L) :
    |(shortRelation N s (2*L)).second| * (2*(L : ℤ))≤N := by
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  have hv := hb.2.2.2.2.1
  have ht : ((N/(2*L+1) : ℕ) : ℤ)*(2*(L : ℤ))≤N := by
    exact_mod_cast ((Nat.mul_le_mul_left (N/(2*L+1)) (show 2*L≤2*L+1 by omega)).trans
      (Nat.div_mul_le_self N (2*L+1)))
  nlinarith [Int.natCast_nonneg L]

/-- Public native enumeration has a bounded number of line
initializations, without knowing whether any particular line succeeds. -/
theorem enumerateCoefficients_lines_le {N s L C : ℕ} (hN : 0<N) (hL : 0<L)
    (hvolume : L^3≤C*N) : (enumerateCoefficients N s L).lines≤2*C+2 := by
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  exact bandInterval_length_le hN _ hb.2.2.2.1 (public_short_second_bound hN hL)
    (public_basis_determinant N s L) hvolume

/-- Arithmetic spacing bounds every directly clipped INNER loop;
the algorithm does not need p, q or the local indices to compute its bounds. -/
theorem mixed_index_line_visits_le {p q L k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L) (hLp : L≤p) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) (j : ℤ) :
    (lineInterval s L (shortRelation (p*q) s (2*L)) j).entries.length≤3+3*L^2/q := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hL : 0<L := by omega
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  have hlen := interval_entries_length_le
    (lineInterval s L (shortRelation (p*q) s (2*L)) j) (2+3*L^2/q) (by
      intro i hi i' hi'
      have hfirst := (mem_lineInterval hb.2.2.1 i j).mp hi
      have hsecond := (mem_lineInterval hb.2.2.1 i' j).mp hi'
      apply mixed_index_line_span hp hq hk hl hLp hkl (s : ZMod (p*q))
        (by simpa only [map_natCast] using hP) (by simpa only [map_natCast] using hQ)
        (a0:=j*((shortRelation (p*q) s (2*L)).previousCoefficient : ℤ))
        (b0:= -(s : ℤ)^2+j*(shortRelation (p*q) s (2*L)).companionSecond)
        (i:=i) (i':=i') (by exact_mod_cast hb.2.2.1) hb.1
      · convert hfirst using 1 <;> dsimp only [coefficientPoint] <;> ring
      · convert hsecond using 1 <;> dsimp only [coefficientPoint] <;> ring)
  omega

/-- Bound the actual traversal length of a nested list by the outer
length times the proved uniform length of each inner list. -/
theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (M : ℕ)
    (hf : ∀ x∈xs, (f x).length≤M) : (xs.flatMap f).length≤xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (by intro y hy; exact hf y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

/-- The ACTUAL native enumerator visits only linearly many coordinates
under the original mixed-index arithmetic, including all initialized
empty lines. A full Boolean clock remains a separate refinement. -/
theorem mixed_index_enumeration_visits_le {p q L C k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L) (hLp : L≤p) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q))
    (hvolume : L^3≤C*(p*q)) :
    (enumerateCoefficients (p*q) s L).lines≤2*C+2 ∧
      (enumerateCoefficients (p*q) s L).visits≤(2*C+2)*(3+3*L^2/q) := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hL : 0<L := by omega
  have hlines := enumerateCoefficients_lines_le (s:=s) hN hL hvolume
  refine ⟨hlines,?_⟩
  change (enumerateCoordinates (p*q) s L (shortRelation (p*q) s (2*L))).length≤_
  unfold enumerateCoordinates
  have hlength := flatMap_length_le (bandInterval (p*q) s L (shortRelation (p*q) s (2*L))).entries
    (fun j => (lineInterval s L (shortRelation (p*q) s (2*L)) j).entries.map (fun i => (i,j)))
    (3+3*L^2/q) (by
      intro j _
      rw [List.length_map]
      exact mixed_index_line_visits_le hp hq hk hl hLp hkl hP hQ j)
  exact hlength.trans (Nat.mul_le_mul_right _ hlines)

/-- Direct nested interval enumeration has no repeated integer
coordinate, even when several initialized lines are empty. -/
theorem enumerateCoordinates_nodup (N s L : ℕ) (basis : ShortRelationReport) :
    (enumerateCoordinates N s L basis).Nodup := by
  unfold enumerateCoordinates
  apply List.nodup_flatMap.mpr
  constructor
  · intro j _
    exact (interval_entries_nodup _).map (by
      intro i i' h
      exact congrArg Prod.fst h)
  · apply (interval_entries_nodup _).imp
    intro j j' hj t ht ht'
    obtain ⟨i,_,he⟩ := List.mem_map.mp ht
    obtain ⟨i',_,he'⟩ := List.mem_map.mp ht'
    exact hj ((congrArg Prod.snd he).trans (congrArg Prod.snd he').symm)

/-- The retained full basis maps coordinates injectively to original
sum/product pairs, including its negative determinant orientation. -/
theorem coefficientPoint_injective {N s L : ℕ} (hN : 0<N) (hL : 0<L) :
    Function.Injective (coefficientPoint s (shortRelation N s (2*L))) := by
  let basis := shortRelation N s (2*L)
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  have hn : (N : ℤ)≠0 := by exact_mod_cast hN.ne'
  have hd : basisDeterminant basis≠0 := by
    rw [public_basis_determinant N s L]
    split
    · exact hn
    · exact neg_ne_zero.mpr hn
  intro x y h
  have ha := congrArg Prod.fst h
  have hb' := congrArg Prod.snd h
  have hdx := coefficientPoint_determinant s basis x
  have hdy := coefficientPoint_determinant s basis y
  have hj : x.2=y.2 := by
    apply mul_right_cancel₀ hd
    rw [← hdx,← hdy,ha,hb']
  have hu : (basis.coefficient : ℤ)≠0 := by exact_mod_cast hb.2.2.1.ne'
  have hi : x.1=y.1 := by
    apply mul_right_cancel₀ hu
    dsimp only [coefficientPoint] at ha
    rw [hj] at ha
    linear_combination ha
  exact Prod.ext hi hj

/-- Every original coefficient pair appears exactly once in the actual
native enumerator's output list. -/
theorem enumerateCoefficients_points_nodup {N s L : ℕ} (hN : 0<N) (hL : 0<L) :
    (enumerateCoefficients N s L).points.Nodup := by
  exact (enumerateCoordinates_nodup _ _ _ _).map (coefficientPoint_injective hN hL)

/-- The actual enumerated list and the frozen rectangle-filter set have
the same members. This is a specification refinement, not a filter in
the native implementation. -/
theorem enumerateCoefficients_finset_eq {N s L : ℕ} (hN : 0<N) (hL : 0<L) :
    (enumerateCoefficients N s L).points.toFinset=coefficientCandidates N s L := by
  ext point
  rw [List.mem_toFinset,mem_enumerateCoefficients_points hN hL,mem_coefficientCandidates]

/-- Original mixed-index arithmetic bounds actual native line
initializations and coordinate visits at the public matched width. -/
theorem public_mixed_index_enumeration_counts {p q k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hk : k<SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hl : l<SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hLp : SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))≤p) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    let out := enumerateCoefficients (p*q) s (SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    out.lines≤524290 ∧ out.visits≤
      524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hc := mixed_index_enumeration_visits_le hp hq hk hl hLp hkl hP hQ
    (public_seed_coefficient_volume hN hB)
  have hqbound := public_seed_line_quotient hp.pos hq.pos hpq hB
  have hmbound := (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).2
  norm_num only at hc
  refine ⟨hc.1,hc.2.trans ?_⟩
  apply Nat.mul_le_mul_left
  nlinarith

/-- The loop budget exposes both initialized lines and visited points,
as well as the actual native early-Euclid division count. It is not a
Boolean gate, serialization or working-memory clock. -/
def EnumerationReport.iterationBudget (report : EnumerationReport) : ℕ :=
  report.basis.steps+report.lines+report.visits

/-- Every counted loop in this native enumeration stage is bounded
at the actual public matched width; initial scalar work and full bit
operations remain explicit separate obligations. -/
theorem public_mixed_index_iteration_budget {p q k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hk : k<SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hl : l<SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hLp : SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))≤p) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    (enumerateCoefficients (p*q) s (SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))).iterationBudget≤
        2*Nat.clog 2 (s%(p*q)+1)+
          524290*(4+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
  have hc := public_mixed_index_enumeration_counts hp hq hpq hB hk hl hLp hkl hP hQ
  have hs := shortRelation_steps (p*q) s
    (2*SemiprimeSeedSumAcquisition.seedLength (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
  change _+_+_≤_
  dsimp only [enumerateCoefficients] at hc ⊢
  nlinarith [hc.1,hc.2]

/-- Original local-root witnesses put their genuine symmetric pair in
the executed native output, including either zero index. -/
theorem mixed_index_genuine_point_visited {p q L k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hk : k<L) (hl : l<L)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    ((k : ℤ)+l,(k : ℤ)*l)∈(enumerateCoefficients (p*q) s L).points := by
  apply (mem_enumerateCoefficients_points (Nat.mul_pos hp.pos hq.pos) (by omega) _).mpr
  exact mixed_index_coefficient_candidate hp hq hpq hk hl (s : ZMod (p*q))
    (by simpa only [map_natCast] using hP) (by simpa only [map_natCast] using hQ)

/-- The original marked decoder on the actual public matched-width
long route feeds a complete native enumeration with no repeated points
and bounded actual loop counts. The arithmetic is a native specification;
Boolean refinement, integer-root reading and jet acquisition remain open. -/
theorem actual_public_route_native_enumeration {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : SemiprimeWrapIndexRecovery.routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let g := ZMod.unitOfCoprime a hc
      let alpha := SemiprimeSeedSumAcquisition.seedBase
        (SemiprimeCentreFreeCover.projectedUnit g m) m
      let L := SemiprimeSeedSumAcquisition.seedLength m
      ∀ (x : ZMod (p*q)) (denom : (ZMod (p*q))ˣ),
        (denom : ZMod (p*q))=x*SemiprimeIntervalJet.targetDerivative (alpha : ZMod (p*q)) x L →
        ∀ k l : ℕ, k<L → l<L → k≠l →
        ZMod.castHom (dvd_mul_right p q) (ZMod p) x=
          (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q)))^k →
        ZMod.castHom (dvd_mul_left q p) (ZMod q) x=
          (ZMod.castHom (dvd_mul_left q p) (ZMod q) (alpha : ZMod (p*q)))^l →
        let s := SemiprimeIntervalJet.decodedIndex (alpha : ZMod (p*q)) x L denom
        let out := enumerateCoefficients (p*q) s.val L
        ((k : ℤ)+l,(k : ℤ)*l)∈out.points ∧ out.points.Nodup ∧ out.lines≤524290 ∧
          out.visits≤524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)) ∧
          out.iterationBudget≤2*Nat.clog 2 (s.val%(p*q)+1)+
            524290*(4+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hdata := SemiprimeWrapIndexRecovery.routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hdata
  obtain ⟨hc,hlong⟩ := hdata
  have hN := Nat.mul_pos hp.pos hq.pos
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  let alpha := SemiprimeSeedSumAcquisition.seedBase
    (SemiprimeCentreFreeCover.projectedUnit g m) m
  let L := SemiprimeSeedSumAcquisition.seedLength m
  have hm : 4≤m := hB.trans (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).1
  have hperiods := SemiprimeSeedSumAcquisition.long_seed_interval_periods hm g hlong
  have hLp : L≤p := hperiods.1.trans
    (SemiprimeIntervalJet.local_unit_period_lt_prime hp (dvd_mul_right p q) alpha).le
  have hL : 0<L := by
    have hh := (SemiprimeSeedSumAcquisition.seedLength_bounds hm).1
    omega
  refine ⟨hc,?_⟩
  dsimp only
  intro x denom hdenom k l hk hl hkl hP hQ
  let s := SemiprimeIntervalJet.decodedIndex (alpha : ZMod (p*q)) x L denom
  have hpr := SemiprimeIntervalJet.decodedIndex_map_root
    (ZMod.castHom (dvd_mul_right p q) (ZMod p)) (alpha : ZMod (p*q)) x L denom hdenom hk hP
  have hqr := SemiprimeIntervalJet.decodedIndex_map_root
    (ZMod.castHom (dvd_mul_left q p) (ZMod q)) (alpha : ZMod (p*q)) x L denom hdenom hl hQ
  have hsP : (s.val : ZMod p)=(k : ZMod p) := by
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_right p q)]
    exact hpr
  have hsQ : (s.val : ZMod q)=(l : ZMod q) := by
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_left q p)]
    exact hqr
  have hcounts := public_mixed_index_enumeration_counts hp hq hpq.le hB hk hl hLp hkl hsP hsQ
  exact ⟨mixed_index_genuine_point_visited hp hq hpq.ne hk hl hsP hsQ,
    enumerateCoefficients_points_nodup hN hL,hcounts.1,hcounts.2,
    public_mixed_index_iteration_budget hp hq hpq.le hB hk hl hLp hkl hsP hsQ⟩

/-- The actual Euclidean predecessor coefficient never exceeds the
returned coefficient; its remainder never exceeds the initial remainder. -/
theorem shortRelationLoop_predecessor_bounds {T r0 r1 c0 c1 : ℕ}
    (horder : r1<r0) (hc : c0≤c1) (negative : Bool) :
    let out := shortRelationLoop T r0 r1 c0 c1 negative
    out.previousCoefficient≤out.coefficient ∧ out.previousRemainder≤r0 := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 negative with
  | h r1 ih =>
    dsimp only
    by_cases hs : r1≤T
    · rw [shortRelationLoop,dif_pos hs]
      exact ⟨hc,le_rfl⟩
    · rw [shortRelationLoop,dif_neg hs]
      dsimp only
      have hquot : 0<r0/r1 := Nat.div_pos horder.le (by omega)
      have hc' : c1≤c0+(r0/r1)*c1 := by nlinarith
      have ht := ih (r0%r1) (Nat.mod_lt r0 (by omega))
        (r0:=r1) (c0:=c1) (c1:=c0+(r0/r1)*c1)
        (Nat.mod_lt r0 (by omega)) hc' (!negative)
      exact ⟨ht.1,ht.2.trans horder.le⟩

/-- All four unsigned words of the actual public basis have explicit
native magnitude bounds. Physical bit cells and peak working memory
are separate obligations of the Boolean refinement. -/
theorem public_basis_operand_bounds {N s L : ℕ} (hN : 0<N) (hL : 0<L) :
    let out := shortRelation N s (2*L)
    out.coefficient≤2*L ∧ out.previousCoefficient≤2*L ∧
      out.remainder≤N ∧ out.previousRemainder≤N := by
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  have hp := shortRelationLoop_predecessor_bounds (Nat.mod_lt s hN) (show 0≤1 by omega) false
    (T:=N/(2*L+1))
  have ht := shortRelationLoop_bounds rfl (show N*1+(s%N)*0=N by omega)
    (Nat.div_lt_self hN (show 1<2*L+1 by omega)) (show 0<1 by omega) (Nat.mod_lt s hN) false
  exact ⟨hb.2.2.2.1,hp.1.trans hb.2.2.2.1,
    ht.2.2.trans (Nat.div_le_self _ _),hp.2⟩

/-- A continuing early-Euclid coefficient update and its unreduced
product are already bounded by A. No large hidden coefficient is
introduced before the next positive-threshold stopping test. -/
theorem shortRelation_step_coefficient_bounds {N A r0 r1 c0 c1 : ℕ}
    (hdet : r0*c1+r1*c0=N) (hcontinue : N/(A+1)<r1) :
    c0+(r0/r1)*c1≤A ∧ (r0/r1)*c1≤A := by
  have hd := shortRelation_step_determinant r0 r1 c0 c1
  have hsum := Nat.mod_add_div N (A+1)
  have hmod := Nat.mod_lt N (show 0<A+1 by omega)
  have hc : c0+(r0/r1)*c1≤A := by
    by_contra h
    have hprod : (N/(A+1)+1)*(A+1)≤r1*(c0+(r0/r1)*c1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hNle : r1*(c0+(r0/r1)*c1)≤N := by omega
    have hstrict : N<(N/(A+1)+1)*(A+1) := by nlinarith
    omega
  exact ⟨hc,by omega⟩

/-- Every actual coordinate visit contributes exactly one original
coefficient candidate. Cardinality appears only in this proof-side
identity, never as an input or executable enumeration filter. -/
theorem enumerateCoefficients_visits_eq_card {N s L : ℕ} (hN : 0<N) (hL : 0<L) :
    (enumerateCoefficients N s L).visits=(coefficientCandidates N s L).card := by
  calc
    (enumerateCoefficients N s L).visits=(enumerateCoefficients N s L).points.length :=
      (enumerateCoefficients_counts N s L).1.symm
    _ = (enumerateCoefficients N s L).points.toFinset.card :=
      (List.toFinset_card_of_nodup (enumerateCoefficients_points_nodup hN hL)).symm
    _ = (coefficientCandidates N s L).card := congrArg Finset.card
      (enumerateCoefficients_finset_eq hN hL)

end RiemannGaussian.SemiprimeIndexEnumeration
