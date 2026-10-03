/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowStructure
import RiemannGaussian.SemiprimeGroupSelection
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Root-preserving Cartesian batches and their centre boundary

Two root lists give an exact detector for every Cartesian pair. This does
not assert that the literal weighted centres separate into two lists.
The mixed centre increment quantifies the correction that must be retained.
Shared roots can be deflated before recovery. The resulting recovery scan
has a linear GCD-query bound for supplied roots, including coherent batches.
This does not bound the cost of constructing the literal centre-coupled roots.
The algebra is checked in the ordinary library and CI; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimeCartesianCompletion

open scoped BigOperators
open Polynomial

/-- The small input polynomial, retaining every root with multiplicity. -/
noncomputable def rootPolynomial {R ι : Type*} [CommRing R] (A : Finset ι) (x : ι → R) : R[X] :=
  ∏ a ∈ A, (X-C (x a))

/-- A Cartesian root product is one resultant of two small polynomials.
No hidden prime, field inversion or pair list occurs in this identity. -/
theorem grid_resultant_eq {R ι κ : Type*} [CommRing R] [Nontrivial R]
    (A : Finset ι) (B : Finset κ) (x : ι → R) (y : κ → R) :
    (rootPolynomial A x).resultant (rootPolynomial B y) A.card B.card =
      ∏ a ∈ A, ∏ b ∈ B, (x a-y b) := by
  classical
  have hA : (rootPolynomial A x).natDegree = A.card :=
    natDegree_finsetProd_X_sub_C_eq_card A x
  have hB : (rootPolynomial B y).natDegree = B.card :=
    natDegree_finsetProd_X_sub_C_eq_card B y
  rw [← hA]
  unfold rootPolynomial
  rw [resultant_prod_left A (fun a => X-C (x a)) _ B.card
    (by simp) (by simpa only [rootPolynomial] using hB.le)]
  simp only [natDegree_X_sub_C]
  simp_rw [resultant_X_sub_C_left _ _ _ (by simpa only [rootPolynomial] using hB.le)]
  simp only [eval_prod, eval_sub, eval_X, eval_C]

/-- Over either hidden prime field, the entire Cartesian detector has
exactly the union of the original pair collisions as its zero set. -/
theorem grid_resultant_eq_zero_iff {R ι κ : Type*} [CommRing R] [IsDomain R]
    (A : Finset ι) (B : Finset κ) (x : ι → R) (y : κ → R) :
    (rootPolynomial A x).resultant (rootPolynomial B y) A.card B.card = 0 ↔
      ∃ a ∈ A, ∃ b ∈ B, x a=y b := by
  classical
  rw [grid_resultant_eq]
  simp only [Finset.prod_eq_zero_iff, sub_eq_zero]

/-- Separated integer centres yield exactly the two small root lists.
The equality is not licensed for a general square-root centre. -/
theorem rowAnchor_separatedCentre {G : Type*} [CommGroup G]
    (g : G) (N a b r c : ℤ) :
    SemiprimeRowStructure.rowAnchor g N a b (r+c) =
      g^(a*N-r) / g^(c-b) := by
  simp only [SemiprimeRowStructure.rowAnchor, div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1
  ring

/-- Unrounded literal centre, written to expose its mixed increment. -/
noncomputable def realCentre (N a b : ℝ) : ℝ :=
  2*Real.sqrt N*Real.sqrt a*Real.sqrt b

/-- Exact integer centre. No floating-point rounding enters the theorem. -/
noncomputable def roundedCentre (N a b : ℝ) : ℤ := ⌈realCentre N a b⌉

/-- The literal square-root formula agrees with the separated square
roots under the original nonnegative input conditions. -/
theorem realCentre_eq_sqrt {N a b : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    realCentre N a b = Real.sqrt (4*N*a*b) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 4*N*a),
    Real.sqrt_mul (by positivity : 0 ≤ 4*N), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  norm_num [realCentre]

/-- Centre curvature is a positive product of square-root increments.
It survives even on an adjacent four-corner block. -/
theorem realCentre_mixed_increment (N a b h : ℝ) :
    realCentre N a b + realCentre N (a+h) (b+h) -
      realCentre N a (b+h) - realCentre N (a+h) b =
      2*Real.sqrt N*(Real.sqrt (a+h)-Real.sqrt a)*
        (Real.sqrt (b+h)-Real.sqrt b) := by
  unfold realCentre
  ring

/-- A uniform square-root increment estimate on the actual weight box. -/
theorem sqrt_increment_lower {a h B : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hab : a+h ≤ B) :
    h ≤ 2*Real.sqrt B*(Real.sqrt (a+h)-Real.sqrt a) := by
  have hah : 0 ≤ a+h := by linarith
  have hB : 0 ≤ B := by linarith
  have hd : 0 ≤ Real.sqrt (a+h)-Real.sqrt a :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have he : (Real.sqrt (a+h)-Real.sqrt a)*
      (Real.sqrt (a+h)+Real.sqrt a)=h := by
    nlinarith [Real.sq_sqrt hah, Real.sq_sqrt ha]
  have hs : Real.sqrt (a+h)+Real.sqrt a ≤ 2*Real.sqrt B := by
    have h1 := Real.sqrt_le_sqrt hab
    have h2 := Real.sqrt_le_sqrt (show a ≤ B by linarith)
    linarith
  have hm := mul_le_mul_of_nonneg_left hs hd
  nlinarith

/-- Even a tiny block retains curvature on the sqrt(N)/B scale.
This is an integer-exponent completion bound, not a complexity lower
bound for every modular or resultant algorithm. -/
theorem realCentre_mixed_lower {N a b h B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hB : 0 < B) (haB : a+h ≤ B) (hbB : b+h ≤ B) :
    Real.sqrt N*h^2/(2*B) ≤
      2*Real.sqrt N*(Real.sqrt (a+h)-Real.sqrt a)*
        (Real.sqrt (b+h)-Real.sqrt b) := by
  have h1 := sqrt_increment_lower ha hh haB
  have h2 := sqrt_increment_lower hb hh hbB
  have hd : 0 ≤ Real.sqrt (a+h)-Real.sqrt a :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hm := mul_le_mul h1 h2 hh (by positivity)
  have hm' : h^2 ≤ 4*B*(Real.sqrt (a+h)-Real.sqrt a)*
      (Real.sqrt (b+h)-Real.sqrt b) := by
    calc
      h^2 = h*h := by ring
      _ ≤ (2*Real.sqrt B*(Real.sqrt (a+h)-Real.sqrt a))*
          (2*Real.sqrt B*(Real.sqrt (b+h)-Real.sqrt b)) := hm
      _ = 4*(Real.sqrt B)^2*(Real.sqrt (a+h)-Real.sqrt a)*
          (Real.sqrt (b+h)-Real.sqrt b) := by ring
      _ = _ := by rw [Real.sq_sqrt hB.le]
  apply (div_le_iff₀ (by positivity : 0 < 2*B)).mpr
  have hmN := mul_le_mul_of_nonneg_left hm' (Real.sqrt_nonneg N)
  nlinarith

/-- Rounding changes the mixed increment by less than two. -/
theorem roundedCentre_mixed_gt (N a b h : ℝ) :
    2*Real.sqrt N*(Real.sqrt (a+h)-Real.sqrt a)*
        (Real.sqrt (b+h)-Real.sqrt b)-2 <
      (roundedCentre N a b : ℝ) + (roundedCentre N (a+h) (b+h) : ℝ) -
        (roundedCentre N a (b+h) : ℝ) - (roundedCentre N (a+h) b : ℝ) := by
  have h00 := Int.le_ceil (realCentre N a b)
  have h11 := Int.le_ceil (realCentre N (a+h) (b+h))
  have h01 := Int.ceil_lt_add_one (realCentre N a (b+h))
  have h10 := Int.ceil_lt_add_one (realCentre N (a+h) b)
  have he := realCentre_mixed_increment N a b h
  change _ < _+_-(Int.ceil (realCentre N a (b+h)) : ℝ)-
    (Int.ceil (realCentre N (a+h) b) : ℝ)
  simp only [roundedCentre]
  linarith

/-- The explicit curvature lower bound also holds for literal integer
centres, paying the full two-unit rounding boundary. -/
theorem roundedCentre_mixed_lower {N a b h B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hB : 0 < B) (haB : a+h ≤ B) (hbB : b+h ≤ B) :
    Real.sqrt N*h^2/(2*B)-2 <
      (roundedCentre N a b : ℝ) + (roundedCentre N (a+h) (b+h) : ℝ) -
        (roundedCentre N a (b+h) : ℝ) - (roundedCentre N (a+h) b : ℝ) := by
  have hl := realCentre_mixed_lower (N := N) ha hb hh hB haB hbB
  have hr := roundedCentre_mixed_gt N a b h
  linarith

/-- Every additive row/column centre fit retains at least half the
mixed increment as the width of its literal correction interval. -/
theorem separated_correction_width {c00 c01 c10 c11 r0 r1 s0 s1 lo hi : ℝ}
    (h00 : lo ≤ c00-r0-s0) (h00' : c00-r0-s0 ≤ hi)
    (h01 : lo ≤ c01-r0-s1) (h01' : c01-r0-s1 ≤ hi)
    (h10 : lo ≤ c10-r1-s0) (h10' : c10-r1-s0 ≤ hi)
    (h11 : lo ≤ c11-r1-s1) (h11' : c11-r1-s1 ≤ hi) :
    |c00+c11-c01-c10| ≤ 2*(hi-lo) := by
  rw [abs_le]
  constructor <;> linarith

/-- In the sixth-root weight regime, even a step-two block cannot be
flattened using one correction interval of width at most B. This does
not rule out a sublinear algorithm for a longer interval or a different
root-preserving nonlinear completion. -/
theorem sixth_regime_correction_gt_budget {N a b B r0 r1 s0 s1 lo hi : ℝ}
    (hB : 4 ≤ B) (hN : (B-1)^6 ≤ N) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haB : a+2 ≤ B) (hbB : b+2 ≤ B)
    (h00 : lo ≤ (roundedCentre N a b : ℝ)-r0-s0)
    (h00' : (roundedCentre N a b : ℝ)-r0-s0 ≤ hi)
    (h01 : lo ≤ (roundedCentre N a (b+2) : ℝ)-r0-s1)
    (h01' : (roundedCentre N a (b+2) : ℝ)-r0-s1 ≤ hi)
    (h10 : lo ≤ (roundedCentre N (a+2) b : ℝ)-r1-s0)
    (h10' : (roundedCentre N (a+2) b : ℝ)-r1-s0 ≤ hi)
    (h11 : lo ≤ (roundedCentre N (a+2) (b+2) : ℝ)-r1-s1)
    (h11' : (roundedCentre N (a+2) (b+2) : ℝ)-r1-s1 ≤ hi) :
    B < hi-lo := by
  have hBp : 0 < B := by linarith
  have hs : (B-1)^3 ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hN]
  have hp : B+1 < (B-1)^3/B := by
    apply (lt_div_iff₀ hBp).mpr
    have hpos : 0 ≤ B^2*(B-4) := mul_nonneg (sq_nonneg B) (by linarith)
    nlinarith
  have hr : (B-1)^3/B ≤ Real.sqrt N/B :=
    div_le_div_of_nonneg_right hs hBp.le
  have hd := roundedCentre_mixed_lower (N := N) ha hb (by norm_num : (0:ℝ) ≤ 2)
    hBp haB hbB
  have he : Real.sqrt N*2^2/(2*B)-2=2*(Real.sqrt N/B-1) := by field_simp
  rw [he] at hd
  have hw := separated_correction_width h00 h00' h01 h01' h10 h10' h11 h11'
  have habs := le_abs_self ((roundedCentre N a b : ℝ)+
    (roundedCentre N (a+2) (b+2) : ℝ)-(roundedCentre N a (b+2) : ℝ)-
    (roundedCentre N (a+2) b : ℝ))
  linarith

set_option exponentiation.threshold 600 in
/-- Three exact edge centres do not license flattening the last centre.
All four weight pairs are primitive and in the balanced cone. Even the
two-unit omitted curvature can erase the proper original factor hit. -/
theorem flattening_can_erase_hit :
    Nat.Coprime 8 11 ∧ Nat.Coprime 8 13 ∧
      Nat.Coprime 10 11 ∧ Nat.Coprime 10 13 ∧
      164^2 < 4*77*8*11 ∧ 4*77*8*11 ≤ 165^2 ∧
      178^2 < 4*77*8*13 ∧ 4*77*8*13 ≤ 179^2 ∧
      184^2 < 4*77*10*11 ∧ 4*77*10*11 ≤ 185^2 ∧
      200^2 < 4*77*10*13 ∧ 4*77*10*13 ≤ 201^2 ∧
      179+185-165=199 ∧
      (2:ℕ)^(10*77+13-201)%77=15 ∧ (2:ℕ)^(10*77+13-199)%77=60 ∧
      Nat.gcd 77 (15-1)=7 ∧ Nat.gcd 77 (60-1)=1 := by
  norm_num [Nat.Coprime]

/-- Evaluate the distinct-root polynomial, using its derivative at a
globally shared root. Multiplicity is discarded only in this recovery
observable; the earlier exact resultant still retains every multiplicity. -/
noncomputable def deflatedColumn {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) (t : R) : R :=
  if t ∈ S then (rootPolynomial S id).derivative.eval t
  else (rootPolynomial S id).eval t

/-- Deflation deletes precisely the whole-ring equal pair, over any
commutative ring. It retains every off-diagonal pair difference. -/
theorem deflatedColumn_eq_product {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) (t : R) :
    deflatedColumn S t = ∏ x ∈ S.erase t, (t-x) := by
  by_cases ht : t ∈ S
  · simpa [deflatedColumn, ht, rootPolynomial, SemiprimeRoughProjection.collisionPolynomial]
      using SemiprimeRoughProjection.derivative_strips_shared_root S ht
  · rw [deflatedColumn, if_neg ht, Finset.erase_eq_of_notMem ht]
    simp only [rootPolynomial, eval_prod, eval_sub, eval_X, eval_C, id_eq]

/-- After reduction to either prime field, the deflated column vanishes
exactly at the collisions between globally unequal residues. -/
theorem deflatedColumn_map_zero_iff {R F : Type*} [CommRing R] [DecidableEq R]
    [CommRing F] [IsDomain F] (φ : R →+* F) (S : Finset R) (t : R) :
    φ (deflatedColumn S t) = 0 ↔ ∃ x ∈ S, x ≠ t ∧ φ x = φ t := by
  rw [deflatedColumn_eq_product, map_prod]
  simp only [map_sub, Finset.prod_eq_zero_iff, Finset.mem_erase, sub_eq_zero]
  constructor
  · rintro ⟨x, ⟨hne, hx⟩, he⟩
    exact ⟨x, hx, hne, he.symm⟩
  · rintro ⟨x, hx, hne, he⟩
    exact ⟨x, ⟨hne, hx⟩, he.symm⟩

/-- The leaf list is constructed only for the first ambiguous column.
Every entry is the canonical residue of an off-diagonal difference. -/
noncomputable def residueLeaves {n : ℕ} (S : Finset (ZMod n)) (t : ZMod n) : List ℕ :=
  (S.erase t).toList.map fun x => (t-x).val

theorem residueLeaves_length_le {n : ℕ} (S : Finset (ZMod n)) (t : ZMod n) :
    (residueLeaves S t).length ≤ S.card := by
  simp only [residueLeaves, List.length_map, Finset.length_toList]
  exact Finset.card_erase_le

theorem residueLeaves_bounds {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (t : ZMod n) :
    ∀ v ∈ residueLeaves S t, 0 < v ∧ v < n := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
  have hne : x ≠ t := (Finset.mem_erase.mp (Finset.mem_toList.mp hx)).1
  exact ⟨ZMod.val_pos.mpr (sub_ne_zero.mpr hne.symm), ZMod.val_lt _⟩

/-- The polynomial implementation and the lazy recovery leaf list have
exactly the same modular product, including at a globally shared root. -/
theorem deflatedColumn_val_eq {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (t : ZMod n) :
    (deflatedColumn S t).val = (residueLeaves S t).prod % n := by
  have he : ((residueLeaves S t).prod : ZMod n) = deflatedColumn S t := by
    rw [residueLeaves, Finset.prod_map_toList, deflatedColumn_eq_product]
    simp only [Nat.cast_prod, ZMod.natCast_zmod_val]
  rw [← he, ZMod.val_natCast]

theorem deflatedColumn_gcd_eq {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (t : ZMod n) :
    n.gcd (deflatedColumn S t).val = n.gcd (residueLeaves S t).prod := by
  rw [deflatedColumn_val_eq, Nat.gcd_rec n, Nat.gcd_rec n ((residueLeaves S t).prod),
    Nat.mod_mod]

/-- A nonunit product of nonzero canonical residues always has a proper
factor leaf. No semiprime assumption or lucky separating branch is needed. -/
theorem proper_leaf_of_product_gcd {n : ℕ} {values : List ℕ}
    (hb : ∀ v ∈ values, 0 < v ∧ v < n) (hh : n.gcd values.prod ≠ 1) :
    ∃ v ∈ values, SemiprimeGroupSelection.ProperDivisor n (n.gcd v) := by
  have hn : ¬ ∀ v ∈ values, Nat.Coprime n v := by
    intro hall
    exact hh (Nat.coprime_list_prod_right_iff.mpr hall)
  push Not at hn
  obtain ⟨v, hv, hnc⟩ := hn
  have hg : n.gcd v ≠ 1 := hnc
  have hp := Nat.gcd_pos_of_pos_right n (hb v hv).1
  refine ⟨v, hv, ?_, (Nat.gcd_le_right n (hb v hv).1).trans_lt (hb v hv).2,
    Nat.gcd_dvd_left n v⟩
  omega

/-- A lazy, checked scan used only after the first full-modulus column. -/
def scanProper (n : ℕ) : List ℕ → Option ℕ
  | [] => none
  | v :: tail =>
    match SemiprimeGroupSelection.checkedSignal n v with
    | some d => some d
    | none => scanProper n tail

/-- Number of GCD queries in the scan; this is not a bit-cost model. -/
def scanGcdCount (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: tail =>
    1 + match SemiprimeGroupSelection.checkedSignal n v with
      | some _ => 0
      | none => scanGcdCount n tail

theorem scanProper_sound {n d : ℕ} {values : List ℕ}
    (hs : scanProper n values = some d) : SemiprimeGroupSelection.ProperDivisor n d := by
  induction values with
  | nil => simp [scanProper] at hs
  | cons v tail ih =>
    cases hc : SemiprimeGroupSelection.checkedSignal n v with
    | none => exact ih (by simpa [scanProper, hc] using hs)
    | some d' =>
      have he : d' = d := by simpa [scanProper, hc] using hs
      subst d'
      exact SemiprimeGroupSelection.checkedSignal_sound hc

theorem scanProper_none_iff (n : ℕ) (values : List ℕ) :
    scanProper n values = none ↔
      ∀ v ∈ values, SemiprimeGroupSelection.checkedSignal n v = none := by
  induction values with
  | nil => simp [scanProper]
  | cons v tail ih =>
    cases hc : SemiprimeGroupSelection.checkedSignal n v <;> simp [scanProper, hc, ih]

theorem scanProper_succeeds_of_product {n : ℕ} {values : List ℕ}
    (hb : ∀ v ∈ values, 0 < v ∧ v < n) (hh : n.gcd values.prod ≠ 1) :
    ∃ d, scanProper n values = some d := by
  obtain ⟨v, hv, hg⟩ := proper_leaf_of_product_gcd hb hh
  have hc : SemiprimeGroupSelection.checkedSignal n v = some (n.gcd v) := by
    simp [SemiprimeGroupSelection.checkedSignal, hg.1, hg.2.1]
  cases hs : scanProper n values with
  | some d => exact ⟨d, rfl⟩
  | none =>
    have hn := (scanProper_none_iff n values).mp hs v hv
    rw [hc] at hn
    contradiction

theorem scanGcdCount_le (n : ℕ) (values : List ℕ) :
    scanGcdCount n values ≤ values.length := by
  induction values with
  | nil => simp [scanGcdCount]
  | cons v tail ih =>
    cases hc : SemiprimeGroupSelection.checkedSignal n v with
    | none =>
      simp only [scanGcdCount, hc, List.length_cons]
      omega
    | some d => simp [scanGcdCount, hc]

/-- Scan evaluated columns once. A nonunit column either supplies a proper
GCD directly or triggers one lazy leaf scan, after which recovery stops. -/
def recoverColumns (n : ℕ) (leaves : ℕ → List ℕ) : List (ℕ × ℕ) → Option ℕ
  | [] => none
  | (t, v) :: tail =>
    if n.gcd v = 1 then recoverColumns n leaves tail
    else if 1 < n.gcd v ∧ n.gcd v < n then some (n.gcd v)
    else scanProper n (leaves t)

/-- GCD queries made by recovery after polynomial evaluation. -/
def recoveryGcdCount (n : ℕ) (leaves : ℕ → List ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (t, v) :: tail =>
    1 + if n.gcd v = 1 then recoveryGcdCount n leaves tail
    else if 1 < n.gcd v ∧ n.gcd v < n then 0
    else scanGcdCount n (leaves t)

theorem recoverColumns_sound {n d : ℕ} {leaves : ℕ → List ℕ}
    {columns : List (ℕ × ℕ)} (hs : recoverColumns n leaves columns = some d) :
    SemiprimeGroupSelection.ProperDivisor n d := by
  induction columns with
  | nil => simp [recoverColumns] at hs
  | cons column tail ih =>
    rcases column with ⟨t, v⟩
    by_cases hu : n.gcd v = 1
    · exact ih (by simpa [recoverColumns, hu] using hs)
    · by_cases hp : 1 < n.gcd v ∧ n.gcd v < n
      · have he : n.gcd v = d := by simpa [recoverColumns, hu, hp] using hs
        rw [← he]
        exact ⟨hp.1, hp.2, Nat.gcd_dvd_left n v⟩
      · exact scanProper_sound (by simpa [recoverColumns, hu, hp] using hs)

/-- Correct deflated evaluation guarantees recovery from every nonunit
column. Existence of a nonunit column remains a separate coverage issue. -/
theorem recoverColumns_succeeds {n : ℕ} {leaves : ℕ → List ℕ}
    {columns : List (ℕ × ℕ)}
    (he : ∀ c ∈ columns, n.gcd c.2 = n.gcd (leaves c.1).prod)
    (hb : ∀ c ∈ columns, ∀ v ∈ leaves c.1, 0 < v ∧ v < n)
    (hh : ∃ c ∈ columns, n.gcd c.2 ≠ 1) :
    ∃ d, recoverColumns n leaves columns = some d := by
  induction columns with
  | nil => simp at hh
  | cons column tail ih =>
    rcases column with ⟨t, v⟩
    by_cases hu : n.gcd v = 1
    · obtain ⟨c, hc, hg⟩ := hh
      have hm : c ∈ tail := by
        rcases List.mem_cons.mp hc with heq | hmem
        · cases heq
          exact (hg hu).elim
        · exact hmem
      obtain ⟨d, hd⟩ := ih (fun c hc => he c (List.mem_cons_of_mem _ hc))
        (fun c hc => hb c (List.mem_cons_of_mem _ hc)) ⟨c, hm, hg⟩
      exact ⟨d, by simpa [recoverColumns, hu] using hd⟩
    · by_cases hp : 1 < n.gcd v ∧ n.gcd v < n
      · exact ⟨n.gcd v, by simp [recoverColumns, hu, hp]⟩
      · obtain ⟨d, hd⟩ := scanProper_succeeds_of_product (hb (t, v) (by simp))
          (by rwa [← he (t, v) (by simp)])
        exact ⟨d, by simpa [recoverColumns, hu, hp] using hd⟩

/-- At most one root scan is charged, even for arbitrarily many shared
roots and coherent columns. This proves a GCD-query bound, not the cost of
constructing roots, multipoint evaluation, or universal hit coverage. -/
theorem recoveryGcdCount_le {n cap : ℕ} {leaves : ℕ → List ℕ}
    {columns : List (ℕ × ℕ)}
    (hb : ∀ c ∈ columns, (leaves c.1).length ≤ cap) :
    recoveryGcdCount n leaves columns ≤ columns.length+cap := by
  induction columns with
  | nil => simp [recoveryGcdCount]
  | cons column tail ih =>
    rcases column with ⟨t, v⟩
    have ht := ih (fun c hc => hb c (List.mem_cons_of_mem _ hc))
    have hl := (scanGcdCount_le n (leaves t)).trans (hb (t, v) (by simp))
    by_cases hu : n.gcd v = 1
    · simp only [recoveryGcdCount, hu, if_true, List.length_cons]
      omega
    · rw [recoveryGcdCount, if_neg hu]
      split_ifs with hp
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega

/-- Actual evaluated columns, with canonical integer point identifiers. -/
noncomputable def evaluatedColumns {n : ℕ} (S : Finset (ZMod n))
    (targets : List (ZMod n)) : List (ℕ × ℕ) :=
  targets.map fun t => (t.val, (deflatedColumn S t).val)

/-- Recovery applied to the proved polynomial detector, rather than an
arbitrary supplied signal. The leaf callback is used only on demand. -/
noncomputable def recoverResidueBatch {n : ℕ} (S : Finset (ZMod n))
    (targets : List (ZMod n)) : Option ℕ :=
  recoverColumns n (fun i => residueLeaves S (i : ZMod n)) (evaluatedColumns S targets)

theorem recoverResidueBatch_sound {n d : ℕ} {S : Finset (ZMod n)}
    {targets : List (ZMod n)} (hs : recoverResidueBatch S targets = some d) :
    SemiprimeGroupSelection.ProperDivisor n d := recoverColumns_sound hs

/-- End-to-end recovery for the exact deflated columns. This theorem
discharges evaluation/leaf consistency; it does not assume it as advice. -/
theorem recoverResidueBatch_succeeds_of_nonunit {n : ℕ} [NeZero n]
    {S : Finset (ZMod n)} {targets : List (ZMod n)} {t : ZMod n}
    (ht : t ∈ targets) (hh : n.gcd (deflatedColumn S t).val ≠ 1) :
    ∃ d, recoverResidueBatch S targets = some d := by
  apply recoverColumns_succeeds
  · intro c hc
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc
    simpa only [ZMod.natCast_zmod_val] using deflatedColumn_gcd_eq S u
  · intro c hc
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc
    exact residueLeaves_bounds S (u.val : ZMod n)
  · exact ⟨(t.val, (deflatedColumn S t).val), List.mem_map.mpr ⟨t, ht, rfl⟩, hh⟩

/-- Every proper original pair hit survives distinct-root deflation and
is recovered, even if many earlier pairs are equal modulo the whole input.
The theorem applies to all composite moduli, including prime squares. -/
theorem recoverResidueBatch_succeeds_of_proper_pair {n : ℕ} [NeZero n]
    {S : Finset (ZMod n)} {targets : List (ZMod n)} {x t : ZMod n}
    (hx : x ∈ S) (ht : t ∈ targets)
    (hp : SemiprimeGroupSelection.ProperDivisor n (n.gcd (t-x).val)) :
    ∃ d, recoverResidueBatch S targets = some d := by
  have hne : x ≠ t := by
    intro he
    have hl := hp.2.1
    simp [he] at hl
  have hm : (t-x).val ∈ residueLeaves S t :=
    List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hne, hx⟩), rfl⟩
  apply recoverResidueBatch_succeeds_of_nonunit ht
  rw [deflatedColumn_gcd_eq]
  intro he
  have hc := Nat.coprime_list_prod_right_iff.mp he (t-x).val hm
  have hl := hp.1
  change n.gcd (t-x).val = 1 at hc
  omega

/-- Recovery uses at most one GCD per target plus one per distinct root.
All square-root centres, root construction and polynomial costs are outside
this query count and must be charged separately in a factoring bound. -/
theorem recoverResidueBatch_gcd_bound {n : ℕ} (S : Finset (ZMod n))
    (targets : List (ZMod n)) :
    recoveryGcdCount n (fun i => residueLeaves S (i : ZMod n))
      (evaluatedColumns S targets) ≤ targets.length+S.card := by
  have h := recoveryGcdCount_le (n := n) (cap := S.card)
    (columns := evaluatedColumns S targets) (leaves := fun i => residueLeaves S (i : ZMod n))
    (fun c _ => residueLeaves_length_le S (c.1 : ZMod n))
  simpa only [evaluatedColumns, List.length_map] using h

/-- Removing duplicate global residues cannot erase a proper pair hit.
The existing multiplicity-preserving resultant is a different observable. -/
theorem recoverResidueList_succeeds_of_proper_pair {n : ℕ} [NeZero n]
    {roots targets : List (ZMod n)} {x t : ZMod n}
    (hx : x ∈ roots) (ht : t ∈ targets)
    (hp : SemiprimeGroupSelection.ProperDivisor n (n.gcd (t-x).val)) :
    ∃ d, recoverResidueBatch roots.toFinset targets = some d :=
  recoverResidueBatch_succeeds_of_proper_pair (List.mem_toFinset.mpr hx) ht hp

theorem recoverResidueList_gcd_bound {n : ℕ} (roots targets : List (ZMod n)) :
    recoveryGcdCount n (fun i => residueLeaves roots.toFinset (i : ZMod n))
      (evaluatedColumns roots.toFinset targets) ≤ targets.length+roots.length :=
  (recoverResidueBatch_gcd_bound roots.toFinset targets).trans
    (Nat.add_le_add_left roots.toFinset_card_le targets.length)

/-- Weight pairs visited before the literal replay's coprimality filter.
This records that implementation's construction, not all possible covers. -/
def candidateWeights (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 B ×ˢ Finset.Icc 1 B).filter fun w => w.1 ≤ w.2 ∧ w.2 ≤ 2*w.1

/-- A whole t-by-t rectangle is visited by the literal weight enumeration.
Consequently its input construction already has quadratic width cost,
irrespective of how efficiently its collision product is evaluated. -/
theorem candidateWeights_card_lower {B t : ℕ} (ht : 0 < t) (hB : 4*t ≤ B) :
    t^2 ≤ (candidateWeights B).card := by
  have hs : (Finset.Ico (2*t) (3*t) ×ˢ Finset.Ico (3*t) (4*t)) ⊆
      candidateWeights B := by
    rintro ⟨a, b⟩ hw
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hw
    obtain ⟨ha₀, ha₁⟩ := Finset.mem_Ico.mp ha
    obtain ⟨hb₀, hb₁⟩ := Finset.mem_Ico.mp hb
    simp only [candidateWeights, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  have hc := Finset.card_le_card hs
  have h3 : 3*t-2*t = t := by omega
  have h4 : 4*t-3*t = t := by omega
  simpa only [Finset.card_product, Nat.card_Ico, h3, h4, pow_two] using hc

/-- A concrete width check for the quadratic construction. This rules out
charging the literal pair enumeration as one operation per axis value;
it is not a complexity lower bound for other exact implicit constructions. -/
theorem candidateWeights_card_gt_width {B : ℕ} (hB : 20 ≤ B) :
    B < (candidateWeights B).card := by
  have ht : 5 ≤ B/4 := by omega
  have hm : 5*(B/4) ≤ (B/4)^2 := by
    simpa [pow_two] using Nat.mul_le_mul_right (B/4) ht
  have hl : B < (B/4)^2 := by omega
  exact hl.trans_le (candidateWeights_card_lower (by omega : 0 < B/4) (by omega))

end RiemannGaussian.SemiprimeCartesianCompletion
