/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsPrimitives
/-! # Clean physical factor/port boundaries and exact actual fibre-bank projection -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsView
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives
/-- Clean actual boundary: all14allocated fibre words and every unlisted private work word are EMPTY. -/
def view (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences:List Bool) :Stack→List Bool :=
  Sum.elim index (Sum.elim (fun _=>[]) (fun k=>match k with
    | .reader=>reader | .ports=>ports | .rowHistory=>rowHistory | .history=>history
    | .factors=>factors | .occurrences=>occurrences | _=>[]))
/-- Update ONLYthe actual reader boundary word; all original index/cache/fibre/shadow words retain their view. -/
theorem view_reader (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences xs:List Bool) :
    Function.update (view index reader ports rowHistory history factors occurrences) (aux .reader) xs=
      view index xs ports rowHistory history factors occurrences :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> simp [view,aux,Function.update]
/-- Update ONLYthe actual ports boundary word; all original index/cache/fibre/shadow words retain their view. -/
theorem view_ports (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences xs:List Bool) :
    Function.update (view index reader ports rowHistory history factors occurrences) (aux .ports) xs=
      view index reader xs rowHistory history factors occurrences :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> simp [view,aux,Function.update]
/-- Update ONLYthe actual rowHistory boundary word; all original index/cache/fibre/shadow words retain their view. -/
theorem view_rowHistory (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences xs:List Bool) :
    Function.update (view index reader ports rowHistory history factors occurrences) (aux .rowHistory) xs=
      view index reader ports xs history factors occurrences :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> simp [view,aux,Function.update]
/-- Update ONLYthe actual history boundary word; all original index/cache/fibre/shadow words retain their view. -/
theorem view_history (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences xs:List Bool) :
    Function.update (view index reader ports rowHistory history factors occurrences) (aux .history) xs=
      view index reader ports rowHistory xs factors occurrences :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> simp [view,aux,Function.update]
/-- Update ONLYthe actual factors boundary word; all original index/cache/fibre/shadow words retain their view. -/
theorem view_factors (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences xs:List Bool) :
    Function.update (view index reader ports rowHistory history factors occurrences) (aux .factors) xs=
      view index reader ports rowHistory history xs occurrences :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> simp [view,aux,Function.update]
/-- Update ONLYthe actual occurrences boundary word; all original index/cache/fibre/shadow words retain their view. -/
theorem view_occurrences (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences xs:List Bool) :
    Function.update (view index reader ports rowHistory history factors occurrences) (aux .occurrences) xs=
      view index reader ports rowHistory history factors xs :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> simp [view,aux,Function.update]
/-- Actual key field has been parsed; it is DIRECTLYthe real fibre query word. -/
def keyed (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key:List Bool) :Stack→List Bool :=
  Function.update (view index reader ports rowHistory history factors occurrences) (aux .key) key
/-- Actual preserving dictionary copy has reached the real fibre reader, not a semantic getter. -/
def copied (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key dictionary:List Bool) :Stack→List Bool :=
  Function.update (keyed index reader ports rowHistory history factors occurrences key) (fibreStack (.inr .reader)) dictionary
/-- Physically returned singleton vector is the only changed private fibre word. -/
def returned (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key owner:List Bool) :Stack→List Bool :=
  Function.update (keyed index reader ports rowHistory history factors occurrences key) (fibreStack (.inr .output))
    (SemiprimeD1TensorTapeCodec.vectorBits [owner])
/-- Before the REALfibre call, all14 actual operand projections equal its literal original source state. -/
theorem fibre_initial (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key dictionary:List Bool) (k:F.Stack) :
    copied index reader ports rowHistory history factors occurrences key dictionary (fibreStack k)=
      (SemiprimeD1StackOwnerFibre.initial key dictionary).data k :=by
  rcases k with k|k
  · cases k <;> simp [copied,keyed,view,fibreStack,aux,SemiprimeD1StackOwnerFibre.initial,
      SemiprimeD1StackOwnerFibre.data,SemiprimeD1StackAdder.store,Function.update]
  · cases k <;> simp [copied,keyed,view,fibreStack,aux,SemiprimeD1StackOwnerFibre.initial,
      SemiprimeD1StackOwnerFibre.data,Function.update]
/-- Exact source-derived singleton semantics collapses the ACTUALfibre result into its clean physical view. -/
theorem fibre_singleton (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key owner:List Bool)
    (rows:List (List Bool×List Bool)) (hs:SemiprimeD1StackOwnerFibre.values key rows=[owner]) :
    withFibre (copied index reader ports rowHistory history factors occurrences key (SemiprimeD1StackOwnerFibre.records rows []))
      (SemiprimeD1StackOwnerFibre.done key rows []).data=
        returned index reader ports rowHistory history factors occurrences key owner :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp [withFibre,keyed,returned,view,fibreStack,aux,SemiprimeD1StackOwnerFibre.done,
          SemiprimeD1StackOwnerFibre.data,SemiprimeD1StackAdder.store,Function.update,hs]
      · cases k <;> simp [withFibre,copied,keyed,returned,view,fibreStack,aux,SemiprimeD1StackOwnerFibre.done,
          SemiprimeD1StackOwnerFibre.data,Function.update,hs]
    · cases k <;> simp [withFibre,copied,keyed,returned,view,fibreStack,aux,SemiprimeD1StackOwnerFibre.done,
        SemiprimeD1StackOwnerFibre.data,Function.update,hs]
/-- Every original index/cache word remains a literal physical tape projection at every clean boundary. -/
theorem index_retained (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences:List Bool) (k:I.Stack) :
    view index reader ports rowHistory history factors occurrences (indexStack k)=index k :=rfl
/-- The one unused query shadow is counted in the allocation and remains physically EMPTY. -/
theorem query_shadow (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences:List Bool) :
    view index reader ports rowHistory history factors occurrences (.inr (.inl (.inr .query)))=[] :=rfl
end RiemannGaussian.SemiprimeD1StackNetworkRowsView
