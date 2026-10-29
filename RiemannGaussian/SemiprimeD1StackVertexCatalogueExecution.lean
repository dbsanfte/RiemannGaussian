/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCatalogueTags
import RiemannGaussian.SemiprimePublicAcquiredExecution

/-! # Complete original binary-input vertex-catalogue acquisition
The whole producer executes metadata/digits once, actual cached-record count,
all derived source-word/tag setup, and all eighteen physical Cartesian blocks.
Empty binary input has an explicit early branch; the original graph equality
is stated for positive canonical input, as required by the public arithmetic
configuration. No graph/cache/parameter/limit/count/truth answer is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCatalogueExecution
open SemiprimeD1StackVertexCatalogue SemiprimeD1StackVertexCatalogueComponents SemiprimeD1StackVertexCatalogueView
open SemiprimeD1StackVertexCataloguePrepare SemiprimeD1StackVertexCatalogueModes SemiprimeD1StackVertexCatalogueCaches
open SemiprimeD1StackVertexCatalogueTags
open SemiprimeD1StackProcedureFragments (At Runs one_base)
open SemiprimeMacroParameters SemiprimeBitArithmetic

/-- Exact constructed final positive-width source store, with all original data retained. -/
def result (bits:List Bool) : Stack→List Bool :=
  view (base bits) (preparedLimits (base bits) .input) []
    (SemiprimeD1VertexCatalogueEncoding.catalogue (firstAxis bits.length) (secondAxis bits.length)
      (digitCountValue bits) [])
/-- Actual stopped positive-width configuration. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Whole producer transition envelope before original-input polynomial substitution. -/
def budget (bits:List Bool) : ℕ :=
  1+(SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+1)+
    (SemiprimeD1StackDigitCountExecution.totalTime (SemiprimeD1StackDigitCountBounds.originalWords bits)+1)+
    (5*transformLength bits.length+5*digitCountValue bits+16)+18+
    18*blockBudget (64*bits.length+3)+1

/-- The real nonempty-input guard preserves the original N, regardless of its low bit. -/
theorem input_guard (bits:List Bool) (hb:bits≠[]) :
    Runs program 1 (.inl .main) (input bits) (.inl .acquireRoot) (input bits) := by
  apply one_base program _ _ (.peek originalInput (.inl .halt) (.inl .acquireRoot) (.inl .acquireRoot)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (Sum.inl Control.halt : Label) (.inl .acquireRoot) (.inl .acquireRoot) bits.head?)=
      some (.inl .acquireRoot)
    cases bits with
    | nil => exact False.elim (hb rfl)
    | cons bit bits => cases bit <;> rfl
  · rfl

/-- Reusable actual stage after the shared original parameter/digit acquisition.
It executes the physical count, derived limits, static tags and complete catalogue,
retaining that same acquired source store. -/
theorem ready (bits:List Bool) (hb:bits≠[]) :
    ∃m≤(SemiprimeD1StackDigitCountExecution.totalTime (SemiprimeD1StackDigitCountBounds.originalWords bits)+1)+
      (5*transformLength bits.length+5*digitCountValue bits+16)+18+18*blockBudget (64*bits.length+3),
      Runs program m (.inl .acquireCount) (afterRoot bits) (.inl .halt) (result bits) := by
  have h2:=count_call bits
  have h3:=caches_run bits
  rw [←base_view bits] at h3
  have h4:=init_run 17 0 rfl (base bits) (fun _=>[]) []
  obtain ⟨t,ht,h5⟩:=catalogue_run bits hb
  refine ⟨_,?_,h2.trans (h3.trans (h4.trans h5))⟩
  omega

/-- The WHOLE actual original-input producer trace; no supplier/control oracle remains. -/
theorem source_run (bits:List Bool) (hb:bits≠[]) :
    ∃m≤budget bits,C.run program m (initial bits)=some (done bits) := by
  have h0:=input_guard bits hb
  obtain ⟨r,hr,h1⟩:=root_call bits hb
  have h2:=count_call bits
  have h3:=caches_run bits
  rw [←base_view bits] at h3
  have h4:=init_run 17 0 rfl (base bits) (fun _=>[]) []
  obtain ⟨t,ht,h5⟩:=catalogue_run bits hb
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  refine ⟨1+(r+((SemiprimeD1StackDigitCountExecution.totalTime (SemiprimeD1StackDigitCountBounds.originalWords bits)+1)+
    ((5*transformLength bits.length+5*digitCountValue bits+16)+(18+t))))+1,?_,?_⟩
  · unfold budget
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    rcases hout with ⟨hpc,hdata,hframes⟩
    change C.step program finish=some (done bits)
    simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done,result]

/-- The actual zero-width early branch does not claim a legacy positive arithmetic graph. -/
theorem empty_run : C.run program 2 (initial [])=some (⟨none,none,none,input [],[]⟩:C.State Stack Label) := rfl

/-- The machine genuinely starts from binary N only, with every new data role empty. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:initial bits=SemiprimeD1StackCalls.initial originalInput (.inl .main) bits:=by
    unfold initial input SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with k|k|k|k|k
    · rcases k with k|k|k
      · rcases k with k|k|k
        · cases k <;> rfl
        · rcases k with k|k <;> rfl
        · rfl
      · rfl
      · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct originalInput (kernelStack (Kernel.aux 2)) (.inl .main) program bits).symm

/-- Every shared original metadata/cache role survives the complete catalogue stage. -/
theorem retained_root (bits:List Bool) (k:Root.Stack) :
    result bits (rootStack k)=SemiprimeD1BinaryPublicAcquisitionComponents.result bits k := by
  simp [result,view,base,twoReady,oneReady,predReady,radiusReady,
    afterCount,afterRoot,rootStack,cacheStack,countStack,Function.update]

/-- Exact complete ORIGINAL graph enumeration, including arithmetic and equality vertices,
with every order/multiplicity retained. The only public input is canonical binary N. -/
theorem original_vertices (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) :
    result bits (kernelStack (Kernel.aux 2))=
      (SemiprimePublicAcquiredExecution.vertexEnumeration (bitValue bits)).values.foldr
        SemiprimeD1VertexCatalogueEncoding.vertex [] := by
  have hw:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  have hb:bits≠[]:=by intro h;subst bits;simp [bitValue] at hN
  change SemiprimeD1VertexCatalogueEncoding.catalogue (firstAxis bits.length) (secondAxis bits.length)
    (digitCountValue bits) []=_
  rw [digitCount_raw bits hb,hw,SemiprimeD1VertexCatalogueEncoding.original_vertices]
  rfl
end RiemannGaussian.SemiprimeD1StackVertexCatalogueExecution
