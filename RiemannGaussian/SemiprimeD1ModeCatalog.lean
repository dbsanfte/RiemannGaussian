/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WeightedTuples

/-! Explicit padded D1 mode labels; packet construction itself is not assumed complete. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1ModeCatalog
open SemiprimeD1WeightedTuples

/-- Slot is the flattened (packet,tile) label; order gives weight=order+1. -/
structure Mode where
  /-- Flattened packet/tile index. -/
  slot : ℕ
  /-- Nonnegative order with positive weight order+1. -/
  order : ℕ
  deriving Repr,DecidableEq

/-- Actual deterministic finite mode catalogue, no supplied catalogue or histogram. -/
def catalog (slots K : ℕ) : List Mode :=
  (List.range K).flatMap fun j => (List.range slots).map fun slot => ⟨slot,j⟩

/-- Exact mode-label membership, preserving all finite slot/order indices. -/
theorem mem_catalog (slots K : ℕ) (mode : Mode) :
    mode∈catalog slots K ↔ mode.slot<slots ∧ mode.order<K := by
  cases mode with
  | mk slot order => simp [catalog,Mode.mk.injEq,and_comm]

/-- Different actual slot/order labels never alias in the acquired catalogue. -/
theorem catalog_nodup (slots K : ℕ) : (catalog slots K).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro j hj
    apply List.nodup_range.map
    intro a b hab
    exact congrArg Mode.slot hab
  · apply List.nodup_range.pairwise_of_forall_ne
    intro i hi j hj hne
    apply List.disjoint_left.mpr
    intro mode hmi hmj
    obtain ⟨x,hx,hix⟩ := List.mem_map.mp hmi
    obtain ⟨y,hy,hjy⟩ := List.mem_map.mp hmj
    have he := congrArg Mode.order (hix.trans hjy.symm)
    exact hne he

/-- The actual acquired catalogue weights, in execution order. -/
def weights (slots K : ℕ) : List ℕ :=
  (catalog slots K).map fun mode => mode.order+1

/-- Exact dimensions of the literal finite acquisition. -/
theorem catalog_length (slots K : ℕ) : (catalog slots K).length=K*slots := by
  simp [catalog,List.length_flatMap]

/-- The cache contains exactly slots variables at each represented positive weight. -/
theorem weights_eq (slots K : ℕ) : weights slots K=
    (List.range K).flatMap fun j => List.replicate slots (j+1) := by
  simp [weights,catalog,List.map_flatMap,List.map_map,Function.comp_def,List.map_const',List.length_range]

/-- There are no zero-weight modes, including the empty catalogue cases. -/
theorem weights_positive (slots K : ℕ) : ∀w∈weights slots K,0<w := by
  intro w hw
  obtain ⟨mode,hm,rfl⟩ := List.mem_map.mp hw
  omega

/-- Every mode weight is at most the explicitly acquired cutoff K. -/
theorem weights_le (slots K : ℕ) : ∀w∈weights slots K,w≤K := by
  intro w hw
  obtain ⟨mode,hm,rfl⟩ := List.mem_map.mp hw
  obtain ⟨j,hj,hmode⟩ := List.mem_flatMap.mp hm
  obtain ⟨slot,hslot,rfl⟩ := List.mem_map.mp hmode
  have := List.mem_range.mp hj
  change j+1≤K
  omega

/-- Literal multiplicity, not a supplied per-weight cardinality answer. -/
theorem weights_count (slots K j : ℕ) :
    (weights slots K).count j=if 0<j ∧ j≤K then slots else 0 := by
  rw [weights_eq]
  induction K with
  | zero => simp;omega
  | succ K ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.count_append,ih,List.count_replicate]
    split_ifs <;> simp_all <;> omega

/-- Cached literal catalogue with per-row list and native field-copy accounting. -/
structure CatalogReport where
  /-- Actual acquired finite mode labels. -/
  value : List Mode
  /-- Retained catalogue construction report. -/
  work : ℕ
  deriving Repr

/-- Acquire every actual order/slot label once; no supplied mode descriptor list. -/
def acquireCatalog (slots K : ℕ) : CatalogReport :=
  let rows := (List.range K).map fun j =>
    let values := (List.range slots).map fun slot => (⟨slot,j⟩ : Mode)
    (values,10*slots+10)
  ⟨rows.flatMap Prod.fst,10*K+10+(rows.map Prod.snd).sum⟩

/-- The retained catalogue is precisely the literal ordered label family. -/
theorem acquireCatalog_value (slots K : ℕ) : (acquireCatalog slots K).value=catalog slots K := by
  simp [acquireCatalog,catalog,List.flatMap_map]

/-- Catalogue construction is polynomial in its original finite dimensions. -/
theorem acquireCatalog_work (slots K : ℕ) :
    (acquireCatalog slots K).work=10*K+10+K*(10*slots+10) := by
  simp [acquireCatalog,List.map_map,Function.comp_def]

/-- Acquire the actual padded labels and run the budget recursion on their weights.
For D.14 the caller passes P=precision-1 and K=P; positive precision is required. -/
def acquireModes (packets tiles P : ℕ) : Report :=
  let labels := acquireCatalog (packets*tiles) P
  let ws := labels.value.map fun mode => mode.order+1
  let result := acquire ws P
  ⟨result.values,result.nodes,result.work+labels.work+10*labels.value.length+10⟩

/-- Literal output of the mode catalogue and its cached tuple traversal. -/
theorem acquireModes_values (packets tiles P : ℕ) :
    (acquireModes packets tiles P).values=tuples (weights (packets*tiles) P) P := by
  simp only [acquireModes,acquireCatalog_value,acquire_values,weights]

/-- Catalogue generation, weight reads and tuple traversal are all retained. -/
theorem acquireModes_work (packets tiles P : ℕ) :
    (acquireModes packets tiles P).work=
      (acquire (weights (packets*tiles) P) P).work+
        (10*P+10+P*(10*(packets*tiles)+10))+10*(P*(packets*tiles))+10 := by
  simp only [acquireModes,acquireCatalog_value,acquireCatalog_work,catalog_length,weights]

/-- Exact acquired original-mode tuple condition, with fixed implicit zero tail. -/
theorem acquireModes_correct (packets tiles P : ℕ) (es : List ℕ) :
    (es∈(acquireModes packets tiles P).values ↔
      Admissible (weights (packets*tiles) P) es P) ∧
      (acquireModes packets tiles P).values.Nodup :=
by
  unfold acquireModes
  simp only [acquireCatalog_value]
  exact acquire_correct (weights_positive _ _)

/-- The actual D1 packet estimate gives floor multiplicity, with no added one.
For slots=packets*2^(i+1), D=2^(a-i), the packet constructor must prove hslots. -/
theorem original_multiplicity (packets tiles D M P j : ℕ)
    (hD : 0<D) (hslots : packets*tiles*D≤6*M) :
    (weights (packets*tiles) P).count j≤6*M/D := by
  rw [weights_count]
  split_ifs
  · exact (Nat.le_div_iff_mul_le hD).mpr hslots
  · exact Nat.zero_le _

/-- All acquired native tuple/list work is polynomial per actual output.
No primitive bit/tape lowering is inferred from this scalar/control report. -/
theorem acquireModes_work_le (packets tiles P : ℕ) :
    (acquireModes packets tiles P).work≤
      20*(P+10)*(P*(packets*tiles)+1)^2*(acquireModes packets tiles P).values.length+
        (10*P+10+P*(10*(packets*tiles)+10))+10*(P*(packets*tiles))+10 := by
  have hw := acquire_work_le P (weights_positive (packets*tiles) P)
  have hv := visits_le (weights (packets*tiles) P) P
  have hn : (weights (packets*tiles) P).length=P*(packets*tiles) := by
    simp only [weights,List.length_map,catalog_length]
  have h := hw.trans (Nat.mul_le_mul_left
    (20*(P+10)*((weights (packets*tiles) P).length+1)) hv)
  rw [hn] at h
  rw [acquireModes_work,acquireModes_values]
  have he : 20*(P+10)*(P*(packets*tiles)+1)*
      ((P*(packets*tiles)+1)*(tuples (weights (packets*tiles) P) P).length)=
        20*(P+10)*(P*(packets*tiles)+1)^2*(tuples (weights (packets*tiles) P) P).length := by ring
  rw [he] at h
  omega

/-- Literal D1 dyadic tile arithmetic at split i≤a, without rounding loss. -/
theorem dyadic_tiles (a i : ℕ) (hi : i≤a) :
    2^(i+1)*2^(a-i)=2*2^a := by
  rw [← pow_add]
  have he : i+1+(a-i)=a+1 := by omega
  rw [he,pow_succ]
  omega

/-- The actual packet bound yields the exact floor multiplicity for every mode.
The packet-construction theorem itself is still a required upstream input. -/
theorem packet_multiplicity (packets a i M P j : ℕ) (hi : i≤a)
    (hpackets : packets*2^a≤3*M) :
    (weights (packets*2^(i+1)) P).count j≤6*M/2^(a-i) := by
  apply original_multiplicity packets (2^(i+1)) (2^(a-i)) M P j (by positivity)
  calc
    packets*2^(i+1)*2^(a-i)=packets*(2*2^a) := by rw [Nat.mul_assoc,dyadic_tiles a i hi]
    _ ≤ 6*M := by nlinarith

end RiemannGaussian.SemiprimeD1ModeCatalog
