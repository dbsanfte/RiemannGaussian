import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueExecution
set_option Elab.async false
set_option maxRecDepth 200000
set_option synthInstance.maxSize 1000000
namespace FullFactorCatalogueControl
open RiemannGaussian
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueView
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt)
end Bank
/-- Actual prepared pair bytes for three unary factor keys; key2 has VALUE3. -/
def pairs:List (List Bool×List Bool):=
  [([],Bank.idAt 6 0),([true],Bank.idAt 6 1),([true],Bank.idAt 6 2),([true],Bank.idAt 6 3),
    ([true,true],Bank.idAt 6 4),([true,true],Bank.idAt 6 5),([false,true],Bank.idAt 6 0)]
def raw (tag:Nat) :Fin 5→List Bool:=![List.replicate tag true,[],[],[],[]]
def descriptor (fields:Fin 5→List Bool) (tail:List Bool):List Bool:=
  SemiprimeSourceHistogramKeyBits.frame (fields 0)
    (SemiprimeSourceHistogramKeyBits.frame (fields 1)
      (SemiprimeSourceHistogramKeyBits.frame (fields 2)
        (SemiprimeSourceHistogramKeyBits.frame (fields 3)
          (SemiprimeSourceHistogramKeyBits.frame (fields 4) tail))))
def descriptors:List Bool:=descriptor (raw 9) (descriptor (raw 8) (descriptor (raw 17) []))
def source:F.Stack→List Bool:=fun k=>
  if k=F.originalInput then [true] else if k=SemiprimeD1StackFactorScopeFibre.pairsOutput
    then SemiprimeD1StackOwnerFibre.records pairs [] else if k=F.output
    then SemiprimeD1TensorTapeCodec.vectorBits [Bank.idAt 6 0] else []
def catalogue:V.Stack→List Bool:=fun k=>if k=catalogueOutput then descriptors else []
def initial:C.State Stack Label:=⟨some (.local .seed),none,none,data source catalogue (fun _=>[]) [] [],[]⟩
def drive:Nat→C.State Stack Label→Option (C.State Stack Label)
  | 0,_=>none
  | n+1,s=>if s.pc.isNone then some s else (C.step program s).bind (drive n)
def expected:List Bool:=
  SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackVertexReadExecution.portTape [0])
    (SemiprimeD1BooleanRootTables.bytes .inputCheck)++
  SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackVertexReadExecution.portTape [1,2,3])
    (SemiprimeD1BooleanRootTables.bytes .orGate)++
  SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackVertexReadExecution.portTape [4,5])
    (SemiprimeD1BooleanRootTables.bytes .equality)++[false]
def check:Bool:=match drive 100000 initial with
  | none=>false
  | some s=>decide (s.data output=expected) && decide (s.frames=[]) &&
    decide (s.data counter=[true,true,true]) && decide (s.data scope=[]) &&
    decide (s.data descriptorReader=[]) && decide (s.data valid=[]) &&
    decide (s.data originalInput=[true]) &&
    decide (s.data (sourceStack SemiprimeD1StackFactorScopeFibre.pairsOutput)=SemiprimeD1StackOwnerFibre.records pairs []) &&
    decide (∀k:D.Stack,k≠D.output→s.data (.inr (.inr (.inl k)))=[])
#eval check
end FullFactorCatalogueControl
