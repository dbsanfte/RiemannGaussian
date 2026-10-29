/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-! Actual finite weighted-budget enumeration. Scratch-only, no supplied catalogue. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1WeightedTuples

/-- Literal weighted degree, including the length agreement in `Admissible`. -/
def degree : List ℕ → List ℕ → ℕ
  | w::ws,e::es => w*e+degree ws es
  | _,_ => 0

/-- Positive input weights are checked separately from a tuple. -/
def Admissible (ws es : List ℕ) (P : ℕ) : Prop := es.length=ws.length ∧ degree ws es≤P

/-- Enumerate only feasible branches; order is coordinate-major ascending exponent. -/
def tuples : List ℕ → ℕ → List (List ℕ)
  | [],_ => [[]]
  | w::ws,P => (List.range (P/w+1)).flatMap fun e =>
      (tuples ws (P-w*e)).map (e::·)

/-- Actual visited recursion nodes, not a unit-price tuple catalogue. -/
def visits : List ℕ → ℕ → ℕ
  | [],_ => 1
  | w::ws,P => 1+((List.range (P/w+1)).map fun e => visits ws (P-w*e)).sum

/-- Every branch has its deterministic zero completion. -/
theorem nonempty (ws : List ℕ) (P : ℕ) : ∃ es, es ∈ tuples ws P := by
  induction ws generalizing P with
  | nil => simp [tuples]
  | cons w ws ih =>
    obtain ⟨es,hes⟩ := ih P
    refine ⟨0::es,?_⟩
    simp only [tuples,List.mem_flatMap,List.mem_range,List.mem_map]
    exact ⟨0,Nat.zero_lt_succ _,es,by simpa using hes,rfl⟩

/-- Exact all-input membership, with no external list of feasible exponents. -/
theorem mem_tuples {ws es : List ℕ} {P : ℕ}
    (hw : ∀w∈ws,0<w) : es∈tuples ws P ↔ Admissible ws es P := by
  induction ws generalizing es P with
  | nil => cases es <;> simp [tuples,Admissible,degree]
  | cons w ws ih =>
    have hp : 0<w := hw w (by simp)
    have ht : ∀v∈ws,0<v := fun v hv => hw v (by simp [hv])
    cases es with
    | nil => simp [tuples,Admissible]
    | cons e es =>
      simp only [tuples,List.mem_flatMap,List.mem_range,List.mem_map]
      constructor
      · rintro ⟨k,hk,ys,hy,hke⟩
        cases hke
        obtain ⟨hlen,hd⟩ := (ih ht).mp hy
        have hek : w*e≤P := by
          have : e≤P/w := by omega
          simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp this
        exact ⟨by simpa using hlen,by dsimp [degree];omega⟩
      · rintro ⟨hlen,hd⟩
        have hek : w*e≤P := by dsimp [degree] at hd;omega
        have he : e<P/w+1 := by
          have : e≤P/w := (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using hek)
          omega
        refine ⟨e,he,es,(ih ht).mpr ⟨by simpa using hlen,?_⟩,rfl⟩
        dsimp [degree] at hd
        omega

/-- Branch lists do not overlap, including zero exponents. -/
theorem nodup (ws : List ℕ) (P : ℕ) : (tuples ws P).Nodup := by
  induction ws generalizing P with
  | nil => simp [tuples]
  | cons w ws ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨?_,?_⟩
    · intro e he
      exact (ih _).map (by intro a b h;exact List.cons.inj h |>.2)
    · apply (List.nodup_range).pairwise_of_forall_ne
      intro e he f hf hne
      apply List.disjoint_left.mpr
      intro a ha hb
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,hy,h⟩ := List.mem_map.mp hb
      exact hne (List.cons.inj h).1.symm

/-- No branch is a dead end: internal-node count is at most depth times leaves. -/
theorem visits_le (ws : List ℕ) (P : ℕ) :
    visits ws P ≤ (ws.length+1)*(tuples ws P).length := by
  induction ws generalizing P with
  | nil => simp [visits,tuples]
  | cons w ws ih =>
    have hsum : ((List.range (P/w+1)).map fun e => visits ws (P-w*e)).sum ≤
      ((List.range (P/w+1)).map fun e => (ws.length+1)*(tuples ws (P-w*e)).length).sum :=
      List.sum_le_sum fun e he => ih _
    have hlen : (tuples (w::ws) P).length =
      ((List.range (P/w+1)).map fun e => (tuples ws (P-w*e)).length).sum := by
      simp [tuples,List.length_flatMap]
    have hmul : ((List.range (P/w+1)).map fun e => (ws.length+1)*(tuples ws (P-w*e)).length).sum =
      (ws.length+1)*(tuples (w::ws) P).length := by
      rw [hlen, List.sum_map_mul_left]
    have hpos : 0<(tuples (w::ws) P).length := by obtain ⟨es,hes⟩ := nonempty (w::ws) P; exact List.length_pos_of_mem hes
    simp only [visits,List.length_cons]
    rw [hmul] at hsum
    nlinarith

/-- Precision one admits only the all-zero mode tuple, including empty modes. -/
theorem tuples_zero (ws : List ℕ) : tuples ws 0=[List.replicate ws.length 0] := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [tuples,ih,List.replicate_succ]

/-- Concrete cached execution report; `work` counts native arithmetic/list cells,
not a primitive bit/tape clock for unbounded input integers. -/
structure Report where
  /-- Actual exponent tuples in deterministic recursion order. -/
  values : List (List ℕ)
  /-- Literal number of visited recursion frames. -/
  nodes : ℕ
  /-- Retained native arithmetic/list-cell report. -/
  work : ℕ
  deriving Repr

/-- Each child is acquired once and its output and report are shared. -/
def acquire : List ℕ → ℕ → Report
  | [],_ => ⟨[[]],1,2⟩
  | w::ws,P =>
    let children := (List.range (P/w+1)).map fun e => (e,acquire ws (P-w*e))
    let values := children.flatMap fun child => child.2.values.map (child.1::·)
    let nodes := 1+(children.map fun child => child.2.nodes).sum
    let work := 10*(P/w+1)+10+
      (children.map fun child => child.2.work+(P+10)*child.2.values.length).sum
    ⟨values,nodes,work⟩

/-- Acquired tuples are the actual feasible ordered recursion above. -/
theorem acquire_values (ws : List ℕ) (P : ℕ) : (acquire ws P).values=tuples ws P := by
  induction ws generalizing P with
  | nil => rfl
  | cons w ws ih => simp only [acquire,List.flatMap_map,ih,tuples]

/-- Acquired node count is the same execution tree, not an external count oracle. -/
theorem acquire_nodes (ws : List ℕ) (P : ℕ) : (acquire ws P).nodes=visits ws P := by
  induction ws generalizing P with
  | nil => rfl
  | cons w ws ih => simp only [acquire,List.map_map,Function.comp_def,ih,visits]

/-- Every acquired leaf is one visited recursion node. -/
theorem length_le_visits (ws : List ℕ) (P : ℕ) :
    (tuples ws P).length≤visits ws P := by
  induction ws generalizing P with
  | nil => simp [tuples,visits]
  | cons w ws ih =>
    have hs := List.sum_le_sum (fun e (_ : e∈List.range (P/w+1)) => ih (P-w*e))
    simpa [tuples,List.length_flatMap,visits,Nat.add_comm] using hs.trans (Nat.le_succ _)

/-- Even an empty-coordinate suffix has its acquired zero leaf. -/
theorem visits_positive (ws : List ℕ) (P : ℕ) : 0<visits ws P := by
  obtain ⟨es,hes⟩ := nonempty ws P
  exact lt_of_lt_of_le (List.length_pos_of_mem hes) (length_le_visits ws P)

/-- Native arithmetic/list-control cost is polynomial per actually visited node.
The original weight and precision binary lowering remains a separate task. -/
theorem acquire_work_le {ws : List ℕ} (P : ℕ) (hw : ∀w∈ws,0<w) :
    (acquire ws P).work≤20*(P+10)*(ws.length+1)*visits ws P := by
  induction ws generalizing P with
  | nil => simp [acquire,visits];omega
  | cons w ws ih =>
    have hwp := hw w (by simp)
    have hws : ∀v∈ws,0<v := fun v hv => hw v (by simp [hv])
    have hterm (e : ℕ) (he : e∈List.range (P/w+1)) :
      (acquire ws (P-w*e)).work+(P+10)*(acquire ws (P-w*e)).values.length ≤
        (20*(P+10)*(ws.length+1)+(P+10))*visits ws (P-w*e) := by
      have hih := ih (P-w*e) hws
      have hsize := length_le_visits ws (P-w*e)
      rw [acquire_values]
      have hc : 20*(P-w*e+10)*(ws.length+1)≤20*(P+10)*(ws.length+1) := by gcongr;omega
      nlinarith
    have hs := List.sum_le_sum hterm
    have hnodes : P/w+1≤((List.range (P/w+1)).map fun e => visits ws (P-w*e)).sum := by
      have hh := List.sum_le_sum (fun e (_ : e∈List.range (P/w+1)) =>
        Nat.succ_le_of_lt (visits_positive ws (P-w*e)))
      simpa using hh
    simp only [acquire,List.map_map,Function.comp_def]
    simp only [List.sum_map_mul_left] at hs
    simp only [visits,List.length_cons]
    have hp : 10≤19*(P+10) := by omega
    have hslack := Nat.mul_le_mul_right
      ((List.range (P/w+1)).map fun e => visits ws (P-w*e)).sum hp
    have hcst : 10≤20*(P+10)*(ws.length+2) := by nlinarith
    nlinarith

/-- Concrete acquired output is complete, exact and duplicate free. -/
theorem acquire_correct {ws es : List ℕ} {P : ℕ} (hw : ∀w∈ws,0<w) :
    (es∈(acquire ws P).values ↔ Admissible ws es P) ∧ (acquire ws P).values.Nodup := by
  rw [acquire_values]
  exact ⟨mem_tuples hw,nodup ws P⟩

/-- Acquired internal states have a leaf extension; no exponential dead scan. -/
theorem acquire_nodes_le (ws : List ℕ) (P : ℕ) :
    (acquire ws P).nodes≤(ws.length+1)*(acquire ws P).values.length := by
  rw [acquire_nodes,acquire_values]
  exact visits_le ws P

end RiemannGaussian.SemiprimeD1WeightedTuples
