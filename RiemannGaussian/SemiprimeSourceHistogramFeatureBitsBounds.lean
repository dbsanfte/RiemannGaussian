/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramFeatureBits
import RiemannGaussian.SemiprimeSourceHistogramTrieBounds
import RiemannGaussian.SemiprimeSourceHistogramSquaresBounds

/-! # Original-cap widths and paid filtered-feature acquisition
Lookup/report bounds follow actual compact prefix payloads and original variable
codes; no intermediate width or dictionary-clock answer is supplied. Cached port
acquisition is paid once by its outer caller, separate from these query passes.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeSourceHistogramFeatureBitsBounds
open SemiprimeSourceHistogramFeatureBits
open SemiprimeSourceHistogramPortKeys (PortRecord)
open SemiprimeSourceHistogramTrie (Trie CompactCounters)
open SemiprimeSourceHistogramTrieBounds (CountCap)
open SemiprimeSourceIncidenceHistogram (Feature)

/-- One common original-dimensional variable/word-ID component width. -/
def width (N L : ℕ) : ℕ := max (SemiprimeSourceHistogramPortKeys.keyWidth N) (Nat.clog 2 (L+1))

/-- Compact represented variable keys fit their original finite code universe. -/
theorem keyRep_length (N code : ℕ) (key : List Bool) (h : KeyRep N code key) :
    key.length ≤ SemiprimeSourceHistogramPortKeys.keyWidth N := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ h.1
  rw [h.2.1]
  have hc := h.2.2
  have hp:=Nat.le_pow_clog (by decide : 1<(2:ℕ)) (N+1)
  unfold SemiprimeSourceHistogramPortKeys.keyWidth
  omega

/-- Every acquired feature component has a width derived from original caps. -/
theorem component_length (dict : Trie) (f : Feature) (key : List Bool) (N L : ℕ)
    (hk : key.length ≤ SemiprimeSourceHistogramPortKeys.keyWidth N)
    (hc : CompactCounters dict) (hv : CountCap dict L) :
    (component dict f key).bits.length ≤ width N L := by
  have hl:=SemiprimeSourceHistogramTrieBounds.lookup_length dict key L hc (hv key)
  by_cases h1 : f=1
  · simp only [component,h1,ite_true,SemiprimeSourceCompactBits.copy_bits]
    exact hk.trans (le_max_left _ _)
  · by_cases h2 : f=2
    · simpa [component,h2,width] using hl.trans (le_max_right (SemiprimeSourceHistogramPortKeys.keyWidth N) (Nat.clog 2 (L+1)))
    · simp [component,h1,h2]

/-- One copied variable key or acquired/copied fixed label and finite control. -/
def componentBudget (B : ℕ) : ℕ := 11*B+12

/-- Actual prefix-trie lookup and component copying are charged at derived width. -/
theorem component_clock (dict : Trie) (f : Feature) (key : List Bool) (N L : ℕ)
    (hk : key.length ≤ SemiprimeSourceHistogramPortKeys.keyWidth N)
    (hc : CompactCounters dict) (hv : CountCap dict L) :
    (component dict f key).clock ≤ componentBudget (width N L) := by
  have hkey : key.length ≤ width N L := hk.trans (le_max_left _ _)
  have hl := SemiprimeSourceHistogramTrieBounds.stored_length dict key L hc (hv key)
  have hs : (SemiprimeSourceHistogramTrie.stored dict key).length ≤ width N L :=
    hl.trans (le_max_right _ _)
  have lookup := SemiprimeSourceHistogramTrieBounds.lookup_clock dict key (width N L) hs
  have copied := SemiprimeSourceCompactBits.copy_clock key
  by_cases h1 : f=1
  · simp only [component,h1,ite_true,componentBudget]
    omega
  · by_cases h2 : f=2
    · have hlk : (SemiprimeSourceHistogramTrie.lookup dict key).clock ≤ componentBudget (width N L) := by
        unfold componentBudget
        omega
      simpa [component,h2] using hlk
    · simp [component,h1,h2,componentBudget]

/-- Physical feature-key framing plus both components and native mask stage. -/
def oneBudget (B : ℕ) : ℕ := 28*B+47

/-- One actual original cached row pays both component reports and framing. -/
theorem one_clock (dict : Trie) (k s : ℕ) (f g : Feature) (row : PortRecord) (N L : ℕ)
    (hr : RecordRep N row) (hc : CompactCounters dict) (hv : CountCap dict L) :
    (one dict k s f g row).work ≤ oneBudget (width N L) := by
  have hown:=keyRep_length N _ row.ownerKey hr.1
  have hfac:=keyRep_length N _ row.factorKey hr.2
  have ha:=component_clock dict f row.ownerKey N L hown hc hv
  have hb:=component_clock dict g row.factorKey N L hfac hc hv
  have hal:=component_length dict f row.ownerKey N L hown hc hv
  have frame:=SemiprimeSourceHistogramKeyBits.pair_clock
    (component dict f row.ownerKey).bits (component dict g row.factorKey).bits
  by_cases hm : (eligible k s f row.ownerCode && eligible k s g row.factorCode)=true
  · simp only [one,hm,ite_true]
    unfold oneBudget componentBudget at *
    omega
  · simp [one,hm,oneBudget]

/-- The exact produced key count is at most the original cache size. -/
theorem produce_length (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord) :
    (produce dict k s f g rows).value.length ≤ rows.length := by
  rw [produce_value,List.length_map]
  exact List.length_filter_le _ _

/-- All actually produced framed key widths follow original variable/label caps. -/
theorem produce_key_length (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord)
    (N L : ℕ) (hr : ∀ row∈rows,RecordRep N row)
    (hc : CompactCounters dict) (hv : CountCap dict L) :
    ∀ key∈(produce dict k s f g rows).value,key.length ≤ 3*width N L+1 := by
  intro key hkey
  rw [produce_value] at hkey
  rcases List.mem_map.mp hkey with ⟨row,hrow,rfl⟩
  have hg:=hr row (List.mem_filter.mp hrow).1
  have ha:=component_length dict f row.ownerKey N L (keyRep_length N _ _ hg.1) hc hv
  have hb:=component_length dict g row.factorKey N L (keyRep_length N _ _ hg.2) hc hv
  rw [component_bits] at ha hb
  unfold jointBytes
  rw [SemiprimeSourceHistogramKeyBits.frame_length]
  omega

/-- Every row is tested once and every eligible physical lookup/copy is paid. -/
theorem produce_clock (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord)
    (N L : ℕ) (hr : ∀ row∈rows,RecordRep N row)
    (hc : CompactCounters dict) (hv : CountCap dict L) :
    (produce dict k s f g rows).work ≤ rows.length*(oneBudget (width N L)+4)+1 := by
  induction rows with
  | nil => simp [produce]
  | cons row rows ih =>
    have ha:=one_clock dict k s f g row N L (hr row List.mem_cons_self) hc hv
    have ht:=ih (fun row hrow => hr row (List.mem_cons_of_mem _ hrow))
    simp only [produce,List.length_cons,Nat.add_mul,Nat.one_mul]
    cases h : (one dict k s f g row).value <;> simp only <;> omega

/-- Actual query acquisition budget; no setup or histogram answer is an input. -/
def budget (N L M : ℕ) : ℕ :=
  M*(oneBudget (width N L)+4)+1+
    SemiprimeSourceHistogramSquaresBounds.budget (3*width N L+1) M+3

/-- Actual produced key list and actual square-count fold are both retained. -/
theorem acquire_clock (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord)
    (N L : ℕ) (hr : ∀ row∈rows,RecordRep N row)
    (hc : CompactCounters dict) (hv : CountCap dict L) :
    (acquire dict k s f g rows).clock ≤ budget N L rows.length := by
  let keys:=(produce dict k s f g rows).value
  have hp:=produce_clock dict k s f g rows N L hr hc hv
  have hl:=produce_length dict k s f g rows
  have hk:=produce_key_length dict k s f g rows N L hr hc hv
  have hs:=SemiprimeSourceHistogramSquaresBounds.fold_clock keys []
    SemiprimeSourceHistogramSquares.initial (3*width N L+1) rows.length
    SemiprimeSourceHistogramSquares.initial_good (by simpa using hl) hk
  have hm : keys.length*(SemiprimeSourceHistogramSquaresBounds.stepBudget (3*width N L+1) rows.length+3) ≤
      rows.length*(SemiprimeSourceHistogramSquaresBounds.stepBudget (3*width N L+1) rows.length+3) :=
    Nat.mul_le_mul_right _ hl
  change (SemiprimeSourceHistogramSquares.acquire keys).clock ≤
    1+keys.length*(SemiprimeSourceHistogramSquaresBounds.stepBudget (3*width N L+1) rows.length+3)+1 at hs
  dsimp only [keys] at hs hm
  unfold acquire budget SemiprimeSourceHistogramSquaresBounds.budget
  dsimp only
  omega

/-- Original acquired cached ports discharge all variable-key shape/width premises. -/
theorem acquirePorts_clock {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (ports : List ((e : Fin F)×Fin (arity e)))
    (dict : Trie) (k s : ℕ) (f g : Feature) (L : ℕ)
    (hc : CompactCounters dict) (hv : CountCap dict L) :
    (acquire dict k s f g
      (SemiprimeSourceHistogramPortKeys.acquirePorts owner ports).value).clock ≤ budget (n+F) L ports.length := by
  have h:=acquire_clock dict k s f g _ (n+F) L (acquirePorts_rep owner ports) hc hv
  simpa only [SemiprimeSourceHistogramPortKeys.acquirePorts_value,List.length_map] using h


/-- The actual accumulated collision word is always compact. -/
theorem acquire_compact (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord) :
    SemiprimeSourceCompactBits.Compact (acquire dict k s f g rows).bits :=
  (SemiprimeSourceHistogramSquares.acquire_good (produce dict k s f g rows).value).2.2.2

/-- No derived feature histogram can exceed the original ordered port-pair count. -/
theorem acquire_value_le (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord) :
    SemiprimeBitArithmetic.bitValue (acquire dict k s f g rows).bits ≤ rows.length^2 := by
  change SemiprimeBitArithmetic.bitValue
    (SemiprimeSourceHistogramSquares.acquire (produce dict k s f g rows).value).bits ≤ _
  rw [SemiprimeSourceHistogramSquares.acquire_value]
  exact (SemiprimeSourceHistogramSquaresBounds.collisions_le _).trans
    (Nat.pow_le_pow_left (produce_length dict k s f g rows) 2)

/-- Original cache size derives the actual final output-word width internally. -/
theorem acquire_length (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord) :
    (acquire dict k s f g rows).bits.length ≤ Nat.clog 2 (rows.length^2+1) := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (acquire_compact dict k s f g rows)
  have h:=acquire_value_le dict k s f g rows
  have hp:=Nat.le_pow_clog (by decide : 1<(2:ℕ)) (rows.length^2+1)
  omega

/-- This acquired persistent histogram-trie node count is charged per produced key;
it is not asserted to be a complete auxiliary-heap bound. -/
theorem acquire_nodes (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord)
    (N L : ℕ) (hr : ∀ row∈rows,RecordRep N row)
    (hc : CompactCounters dict) (hv : CountCap dict L) :
    SemiprimeSourceHistogramTrie.nodes (acquire dict k s f g rows).trie ≤
      rows.length*(3*width N L+2) := by
  have h:=SemiprimeSourceHistogramSquaresBounds.acquire_nodes (produce dict k s f g rows).value
    (3*width N L+1) (produce_key_length dict k s f g rows N L hr hc hv)
  have hl:=produce_length dict k s f g rows
  change SemiprimeSourceHistogramTrie.nodes
    (SemiprimeSourceHistogramSquares.acquire (produce dict k s f g rows).value).trie ≤ _
  apply h.trans
  simpa only [Nat.add_assoc] using Nat.mul_le_mul_right (3*width N L+1+1) hl

end RiemannGaussian.SemiprimeSourceHistogramFeatureBitsBounds
