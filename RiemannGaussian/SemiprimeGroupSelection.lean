/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRoughProjection

/-!
# Certified group selection over a finite menu

Small-to-large probes select the minimum successful scale in a fixed
curve menu, without local orders or factors as advice. The selected GCD
is a proper divisor. Dyadic covers have a geometric total width bound,
including a final truncated cap. Projective signals commute with ring
reduction; a checked signal from the nominal 80-bit control is included.

The finite menu must contain a successful probe for a coverage guarantee.
These results do not assert a globally optimal elliptic curve, universal
one-sixth factoring, the full Montgomery group law, or the Python program's
bit-complexity. This optional side-project module is outside the RH root.
-/

namespace RiemannGaussian.SemiprimeGroupSelection

/-- The check performed before returning a recovered divisor. -/
def ProperDivisor (n d : ℕ) : Prop := 1 < d ∧ d < n ∧ d ∣ n

/-- A residue supplies a certified factor only when its GCD is proper. -/
def checkedSignal (n x : ℕ) : Option ℕ :=
  if 1 < n.gcd x ∧ n.gcd x < n then some (n.gcd x) else none

theorem checkedSignal_sound {n x d : ℕ} (h : checkedSignal n x = some d) :
    ProperDivisor n d := by
  unfold checkedSignal at h
  split_ifs at h with hd
  · cases h
    exact ⟨hd.1, hd.2, Nat.gcd_dvd_left n x⟩

/-- Curve index, successful cover width, and the certified factor. -/
structure Selection where
  /-- Public identifier of the successful group candidate. -/
  group : ℕ
  /-- First successful cover width in the ordered probe schedule. -/
  width : ℕ
  /-- Proper divisor certified by the selected residue. -/
  factor : ℕ
  deriving DecidableEq

/-- Search the public ordered list of curve/width trials. -/
def search (probe : ℕ → ℕ → Option ℕ) : List (ℕ × ℕ) → Option Selection
  | [] => none
  | (g, w) :: tail =>
    match probe g w with
    | some d => some ⟨g, w, d⟩
    | none => search probe tail

/-- Cover width actually visited before the first successful probe. -/
def searchWidth (probe : ℕ → ℕ → Option ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (g, w) :: tail =>
    w + match probe g w with
    | some _ => 0
    | none => searchWidth probe tail

theorem search_append_of_success (probe : ℕ → ℕ → Option ℕ)
    {earlier : List (ℕ × ℕ)} {result : Selection}
    (hs : search probe earlier = some result) (suffix : List (ℕ × ℕ)) :
    search probe (earlier ++ suffix) = some result ∧
      searchWidth probe (earlier ++ suffix) = searchWidth probe earlier := by
  induction earlier with
  | nil => simp [search] at hs
  | cons head tail ih =>
    rcases head with ⟨g, w⟩
    cases hp : probe g w with
    | some d =>
      constructor
      · simpa [search, hp] using hs
      · simp [searchWidth, hp]
    | none =>
      obtain ⟨hsearch, hcost⟩ := ih (by simpa [search, hp] using hs)
      simpa [search, searchWidth, hp, hcost] using hsearch

theorem search_sound (probe : ℕ → ℕ → Option ℕ)
    (hprobe : ∀ g w d, probe g w = some d → ProperDivisor n d)
    {trials : List (ℕ × ℕ)} {result : Selection}
    (h : search probe trials = some result) : ProperDivisor n result.factor := by
  induction trials with
  | nil => simp [search] at h
  | cons trial tail ih =>
    rcases trial with ⟨g, w⟩
    cases hp : probe g w with
    | none => exact ih (by simpa [search, hp] using h)
    | some d =>
      have he : ({ group := g, width := w, factor := d } : Selection) = result := by
        simpa [search, hp] using h
      rw [← he]
      exact hprobe g w d hp

theorem search_returns_trial (probe : ℕ → ℕ → Option ℕ)
    {trials : List (ℕ × ℕ)} {result : Selection}
    (h : search probe trials = some result) :
    (result.group, result.width) ∈ trials ∧
      probe result.group result.width = some result.factor := by
  induction trials with
  | nil => simp [search] at h
  | cons trial tail ih =>
    rcases trial with ⟨g, w⟩
    cases hp : probe g w with
    | none =>
      obtain ⟨hm, hv⟩ := ih (by simpa [search, hp] using h)
      exact ⟨List.mem_cons_of_mem _ hm, hv⟩
    | some d =>
      have he : ({ group := g, width := w, factor := d } : Selection) = result := by
        simpa [search, hp] using h
      rw [← he]
      exact ⟨by simp, hp⟩

theorem search_none_iff (probe : ℕ → ℕ → Option ℕ) (trials : List (ℕ × ℕ)) :
    search probe trials = none ↔ ∀ t ∈ trials, probe t.1 t.2 = none := by
  induction trials with
  | nil => simp [search]
  | cons trial tail ih =>
    rcases trial with ⟨g, w⟩
    cases hp : probe g w <;> simp [search, hp, ih]

/-- Coverage is relative to a successful trial in the explicit finite
menu. Existence of that trial is not inferred from semiprimality. -/
theorem search_succeeds_of_menu_hit (probe : ℕ → ℕ → Option ℕ)
    {trials : List (ℕ × ℕ)} {g w d : ℕ} (hm : (g, w) ∈ trials)
    (hh : probe g w = some d) : ∃ result, search probe trials = some result := by
  cases hs : search probe trials with
  | some result => exact ⟨result, rfl⟩
  | none =>
    have hn := (search_none_iff probe trials).mp hs (g, w) hm
    rw [hh] at hn
    contradiction

/-- The first successful probe has minimum scale among all successful
trials, provided trials are sorted by scale. This is not minimum runtime
among all possible curves. -/
theorem search_minimum_scale (probe : ℕ → ℕ → Option ℕ)
    {trials : List (ℕ × ℕ)} {result : Selection}
    (ho : trials.Pairwise (fun a b => a.2 ≤ b.2))
    (hs : search probe trials = some result) {g w d : ℕ}
    (hm : (g, w) ∈ trials) (hh : probe g w = some d) : result.width ≤ w := by
  induction trials with
  | nil => simp at hm
  | cons trial tail ih =>
    rcases trial with ⟨g₀, w₀⟩
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp ho
    cases hp : probe g₀ w₀ with
    | some d₀ =>
      have he : ({ group := g₀, width := w₀, factor := d₀ } : Selection) = result := by
        simpa [search, hp] using hs
      rw [← he]
      rcases List.mem_cons.mp hm with heq | hm
      · cases heq
        exact le_rfl
      · exact hhead (g, w) hm
    | none =>
      have hmem : (g, w) ∈ tail := by
        rcases List.mem_cons.mp hm with heq | hmem
        · cases heq
          rw [hh] at hp
          contradiction
        · exact hmem
      exact ih htail (by simpa [search, hp] using hs) hmem

/-- Every curve is probed at one width before advancing the width. -/
def trials (groups widths : List ℕ) : List (ℕ × ℕ) :=
  widths.flatMap fun w => groups.map fun g => (g, w)

theorem mem_trials {groups widths : List ℕ} {g w : ℕ} :
    (g, w) ∈ trials groups widths ↔ g ∈ groups ∧ w ∈ widths := by
  simp only [trials, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨w', hw', g', hg', he⟩
    cases he
    exact ⟨hg', hw'⟩
  · rintro ⟨hg, hw⟩
    exact ⟨w, hw, g, hg, rfl⟩

theorem trials_ordered (groups : List ℕ) {widths : List ℕ}
    (ho : widths.Pairwise (· ≤ ·)) :
    (trials groups widths).Pairwise (fun a b => a.2 ≤ b.2) := by
  induction widths with
  | nil => simp [trials]
  | cons w widths ih =>
    obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp ho
    rw [trials, List.flatMap_cons]
    apply List.pairwise_append.mpr
    refine ⟨?_, ih hrest, ?_⟩
    · exact List.pairwise_map.mpr (List.pairwise_of_forall (by simp))
    · intro a ha b hb
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
      have hmem := (mem_trials.mp hb).2
      exact hfirst b.2 hmem

/-- Exact total cover width; scalar-bit and polynomial-operation counters
are separately charged by the implementation. -/
def coverWidth (ts : List (ℕ × ℕ)) : ℕ := (ts.map Prod.snd).sum

theorem searchWidth_le_coverWidth (probe : ℕ → ℕ → Option ℕ)
    (ts : List (ℕ × ℕ)) : searchWidth probe ts ≤ coverWidth ts := by
  induction ts with
  | nil => simp [searchWidth, coverWidth]
  | cons head tail ih =>
    rcases head with ⟨g, w⟩
    change searchWidth probe tail ≤ (tail.map Prod.snd).sum at ih
    cases hp : probe g w with
    | some d => simp [searchWidth, coverWidth, hp]
    | none => simpa [searchWidth, coverWidth, hp] using ih

theorem coverWidth_trials (groups widths : List ℕ) :
    coverWidth (trials groups widths) = groups.length * widths.sum := by
  induction widths with
  | nil => simp [coverWidth, trials]
  | cons w widths ih =>
    simp only [trials, List.flatMap_cons, coverWidth, List.map_append, List.sum_append] at *
    rw [ih]
    simp [List.map_map, Function.comp_def, Nat.mul_add, Nat.mul_comm]

/-- Untruncated dyadic stages up to and including index k. -/
def dyadicWidths (b k : ℕ) : List ℕ :=
  (List.range (k+1)).map fun i => b*2^i

theorem dyadicWidths_ordered (b k : ℕ) : (dyadicWidths b k).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp _ List.pairwise_lt_range
  intro i j hij
  exact Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by decide) hij.le)

theorem dyadic_sum_exact (b k : ℕ) :
    (dyadicWidths b k).sum + b = 2*(b*2^k) := by
  induction k with
  | zero => simp [dyadicWidths, two_mul]
  | succ k ih =>
    have he : dyadicWidths b (k+1) = dyadicWidths b k ++ [b*2^(k+1)] := by
      simp [dyadicWidths, List.range_succ]
    rw [he, List.sum_append]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    rw [pow_succ]
    nlinarith

theorem dyadic_coverWidth_bound (groups : List ℕ) (b k : ℕ) :
    coverWidth (trials groups (dyadicWidths b k)) ≤
      2*groups.length*(b*2^k) := by
  rw [coverWidth_trials]
  have hs := dyadic_sum_exact b k
  nlinarith

/-- The final exact cap may follow a smaller dyadic stage. Its entire
cover-width cost is at most three menu sizes times that cap. -/
theorem capped_coverWidth_bound (groups : List ℕ) (b k cap : ℕ)
    (hc : b*2^k ≤ cap) :
    coverWidth (trials groups (dyadicWidths b k ++ [cap])) ≤
      3*groups.length*cap := by
  rw [coverWidth_trials, List.sum_append]
  simp only [List.sum_cons, List.sum_nil, add_zero]
  have hs := dyadic_sum_exact b k
  have hsum : (dyadicWidths b k).sum + cap ≤ 3*cap := by omega
  exact (Nat.mul_le_mul_left groups.length hsum).trans_eq (by ring)

/-- Returning a GCD never needs to assume that either hidden group order
is smooth. The signal itself certifies a proper divisor. -/
theorem tournament_sound (n : ℕ) (signal : ℕ → ℕ → ℕ)
    {groups widths : List ℕ} {result : Selection}
    (hs : search (fun g w => checkedSignal n (signal g w))
      (trials groups widths) = some result) : ProperDivisor n result.factor :=
  search_sound _ (fun _ _ _ h => checkedSignal_sound h) hs

/-- If one candidate succeeds at a dyadic width, the full tournament
returns a certified factor without examining later stages. Its visited
cover width is at most twice the menu size times that candidate's width.
The assumption is an actual GCD probe hit, not hidden smoothness advice. -/
theorem dyadic_tournament_guarantee (n : ℕ) (signal : ℕ → ℕ → ℕ)
    (groups : List ℕ) (b k : ℕ) (suffix : List (ℕ × ℕ))
    {g d : ℕ} (hg : g ∈ groups)
    (hh : checkedSignal n (signal g (b*2^k)) = some d) :
    ∃ result,
      search (fun g w => checkedSignal n (signal g w))
        (trials groups (dyadicWidths b k) ++ suffix) = some result ∧
      ProperDivisor n result.factor ∧ result.width ≤ b*2^k ∧
      searchWidth (fun g w => checkedSignal n (signal g w))
        (trials groups (dyadicWidths b k) ++ suffix) ≤
          2*groups.length*(b*2^k) := by
  let probe := fun g w => checkedSignal n (signal g w)
  have hm : (g, b*2^k) ∈ trials groups (dyadicWidths b k) := by
    apply mem_trials.mpr
    refine ⟨hg, ?_⟩
    apply List.mem_map.mpr
    exact ⟨k, List.mem_range.mpr (by omega), rfl⟩
  obtain ⟨result, hs⟩ := search_succeeds_of_menu_hit probe hm hh
  have happend := search_append_of_success probe hs suffix
  refine ⟨result, happend.1, tournament_sound n signal hs, ?_, ?_⟩
  · exact search_minimum_scale probe (trials_ordered groups (dyadicWidths_ordered b k))
      hs hm hh
  · rw [happend.2]
    exact (searchWidth_le_coverWidth probe _).trans (dyadic_coverWidth_bound groups b k)

/-- Cross multiplication retains a projective collision without affine
division over the composite ring. -/
def projectiveSignal {R : Type*} [CommRing R] (a b : R × R) : R :=
  a.1*b.2-b.1*a.2

theorem projectiveSignal_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R × R) :
    f (projectiveSignal a b) =
      projectiveSignal (f a.1, f a.2) (f b.1, f b.2) := by
  simp [projectiveSignal]

/-- Exact polynomial doubling formula used by the public curve probes. -/
def montgomeryDouble {R : Type*} [CommRing R] (a24 : R) (p : R × R) : R × R :=
  let a := (p.1+p.2)^2
  let b := (p.1-p.2)^2
  let c := a-b
  (a*b, c*(b+a24*c))

theorem montgomeryDouble_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a24 : R) (p : R × R) :
    (f (montgomeryDouble a24 p).1, f (montgomeryDouble a24 p).2) =
      montgomeryDouble (f a24) (f p.1, f p.2) := by
  simp [montgomeryDouble]

/-- Differential addition is polynomial, with the difference point retained. -/
def montgomeryAdd {R : Type*} [CommRing R] (p q difference : R × R) : R × R :=
  let a := (p.1+p.2)*(q.1-q.2)
  let b := (p.1-p.2)*(q.1+q.2)
  (difference.2*(a+b)^2, difference.1*(a-b)^2)

theorem montgomeryAdd_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p q difference : R × R) :
    (f (montgomeryAdd p q difference).1, f (montgomeryAdd p q difference).2) =
      montgomeryAdd (f p.1, f p.2) (f q.1, f q.2) (f difference.1, f difference.2) := by
  simp [montgomeryAdd]

theorem affine_eq_iff_projectiveSignal_zero {F : Type*} [Field F]
    {a b : F × F} (ha : a.2 ≠ 0) (hb : b.2 ≠ 0) :
    a.1/a.2 = b.1/b.2 ↔ projectiveSignal a b = 0 := by
  rw [div_eq_div_iff ha hb]
  exact sub_eq_zero.symm

/-- Arithmetic certificate produced by the public adaptive run on the
four-rough control, at sigma=6 and cover width 256. This checks the GCD
and factor, not an oracle-supplied curve-order assertion. -/
theorem four_rough_control_factor_certificate :
    checkedSignal 477209897193541203289441 474427418761119040057631 =
      some 661911275027 := by
  norm_num [checkedSignal]

theorem four_rough_control_proper_divisor :
    ProperDivisor 477209897193541203289441 661911275027 :=
  checkedSignal_sound four_rough_control_factor_certificate

end RiemannGaussian.SemiprimeGroupSelection
