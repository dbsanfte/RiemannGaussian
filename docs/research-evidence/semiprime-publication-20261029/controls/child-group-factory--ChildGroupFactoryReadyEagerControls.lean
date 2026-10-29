import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyResources
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace ChildGroupFactoryReadyEagerControls
open RiemannGaussian
namespace R
export SemiprimeD1StackChildGroupFactoryReady
  (Stack Header initial sourceInputs program factory allocation)
end R
namespace C
export SemiprimeD1StackCalls (State step)
end C
namespace W
export SemiprimeD1StackChildGroupFactoryWiring (Label entry)
end W
def keys:List R.Stack:=[
  .inl (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left))))),
  .inl (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right))))),
  .inl (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch))))),
  .inl (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output))))),
  .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query))))),
  .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader))))),
  .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch))))),
  .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid))))),
  .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch))))),
  .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard))))),
  .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output))))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.dictionary)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.nextKey)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.chosenID)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.markedValue)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.copyWork)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.copyScratch)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.trimScratch)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.frameScratch)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.incNext)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.incScratch)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.found)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.prefix)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.reader)))),
  .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.reversedPrefix)))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.source))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.outerReader))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.innerReader))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.ownerLeft))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.factorLeft))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.ownerRight))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.factorRight))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.square))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.cube))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.fourth))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.copyScratch))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.fieldScratch))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.valid))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.eqLeft))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.eqRight))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.eqScratch))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.eqOutput))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.savedQuery))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.sumLeft))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.term))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.sumScratch))),
  .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.total))),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.catalogue)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.owners)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.factors)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.todo)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.reader)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.discard)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.parserScratch)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.valid)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.copyScratch)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.savedKey)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.bestID)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.bestScore)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.compareLeft)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.compareRight)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.compareScratch)),
  .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.compareOutput)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.rows)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.number)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.reader)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.row)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.word)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.todo)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.counter)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.next)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.incrementScratch)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.ownerKey)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.factorKey)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.fieldScratch)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.valid)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.copyScratch)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.normScratch)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.frameBuffer)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.frameScratch)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.history)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.output)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.factors)),
  .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.occurrences)),
  .inr (.inr (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left)))))),
  .inr (.inr (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right)))))),
  .inr (.inr (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch)))))),
  .inr (.inr (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output)))))),
  .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query)))))),
  .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader)))))),
  .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch)))))),
  .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid)))))),
  .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch)))))),
  .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard)))))),
  .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output)))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.source))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.reader))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.raw))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.dictionary))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.count))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.maximum))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.incScratch))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.incNext))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.trimScratch))))),
  .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.frameScratch))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard))))))),
  .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output))))))),
  .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.key)))))),
  .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.catalogue)))))),
  .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.keyReader)))))),
  .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftBytes)))))),
  .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftHistory)))))),
  .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.rightHistory)))))),
  .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftOutput)))))),
  .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.rightOutput)))))),
  .inr (.inr (.inl (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left))))))),
  .inr (.inr (.inl (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right))))))),
  .inr (.inr (.inl (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch))))))),
  .inr (.inr (.inl (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output))))))),
  .inr (.inr (.inl (.inr (.inr (.inl (.inr (PUnit.unit))))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.leftInput)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.rightInput)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.indexInput)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.leftReader)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.rightReader)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.indexCursor)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.leftColour)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.rightColour)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.copyScratch)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.keyHistory)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.slotHistory)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.keyOutput)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.slotOutput)))))),
  .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.highOutput)))))),
  .inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left))))),
  .inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right))))),
  .inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch))))),
  .inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output))))),
  .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query))))),
  .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader))))),
  .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch))))),
  .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid))))),
  .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch))))),
  .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard))))),
  .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard))))))),
  .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output))))))),
  .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.key)))))),
  .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.catalogue)))))),
  .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.keyReader)))))),
  .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftBytes)))))),
  .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftHistory)))))),
  .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.rightHistory)))))),
  .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftOutput)))))),
  .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.rightOutput)))))),
  .inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left)))))),
  .inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right)))))),
  .inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch)))))),
  .inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output)))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1TensorTapeFieldMachine.Stack.input)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1TensorTapeFieldMachine.Stack.scratch)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1TensorTapeFieldMachine.Stack.output)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (.inr (PUnit.unit)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.bank)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.reader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.word)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.fieldScratch)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.valid)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.copyScratch)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.digits)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.unaryScratch)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.unary)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.logScratch)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.history)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.output)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.environment)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.catalogue)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.owners)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.factors)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.occurrences)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.placements)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.packets)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.colourIndex)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.group)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldAxes)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldPrecision)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.jetAxis)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.newPrecision)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.activation)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.activationMap)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.endpoints)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldEndpoints)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.buckets)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.leftPorts)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.orders)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.output)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.vertexTodo)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.vertexKey)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.selectedID)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.jointKey)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.pairReader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.placementReader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.packetReader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.endpointReader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldReader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.childReader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.outerReader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.ownerKey)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.factorKey)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.sourceKey)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.paddingKey)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.packetKey)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.slotWord)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.edgeWord)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.sideWord)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.validWord)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.colourReader)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.colourCursor)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.colourWord)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.activationHistory)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.endpointHistory)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldHistory)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.bucketHistory)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.factorHistory)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.portHistory)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.orderHistory)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.vertexHistory)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.tagWord)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.candidateTag)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.localPosition)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.globalPosition)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.answerPosition)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.frameBuffer)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.rowBuffer)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.copyScratch)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.sentinelScratch)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.flagScratch)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.success)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.orderBank)))))))),
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.portBank))))))))
]
def index:R.Stack→Nat
  | .inl (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left)))))=>0
  | .inl (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right)))))=>1
  | .inl (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch)))))=>2
  | .inl (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output)))))=>3
  | .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query)))))=>4
  | .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader)))))=>5
  | .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch)))))=>6
  | .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid)))))=>7
  | .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch)))))=>8
  | .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard)))))=>9
  | .inl (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output)))))=>10
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.dictionary))))=>11
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.nextKey))))=>12
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.chosenID))))=>13
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.markedValue))))=>14
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.copyWork))))=>15
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.copyScratch))))=>16
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.trimScratch))))=>17
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.frameScratch))))=>18
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.incNext))))=>19
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.incScratch))))=>20
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.found))))=>21
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.prefix))))=>22
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.reader))))=>23
  | .inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceEnvironment.Aux.reversedPrefix))))=>24
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.source)))=>25
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.outerReader)))=>26
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.innerReader)))=>27
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.ownerLeft)))=>28
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.factorLeft)))=>29
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.ownerRight)))=>30
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.factorRight)))=>31
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.square)))=>32
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.cube)))=>33
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.fourth)))=>34
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.copyScratch)))=>35
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.fieldScratch)))=>36
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.valid)))=>37
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.eqLeft)))=>38
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.eqRight)))=>39
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.eqScratch)))=>40
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.eqOutput)))=>41
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.savedQuery)))=>42
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.sumLeft)))=>43
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.term)))=>44
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.sumScratch)))=>45
  | .inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidence.Aux.total)))=>46
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.catalogue))=>47
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.owners))=>48
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.factors))=>49
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.todo))=>50
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.reader))=>51
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.discard))=>52
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.parserScratch))=>53
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.valid))=>54
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.copyScratch))=>55
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.savedKey))=>56
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.bestID))=>57
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.bestScore))=>58
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.compareLeft))=>59
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.compareRight))=>60
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.compareScratch))=>61
  | .inl (.inr (RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect.Aux.compareOutput))=>62
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.rows))=>63
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.number))=>64
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.reader))=>65
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.row))=>66
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.word))=>67
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.todo))=>68
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.counter))=>69
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.next))=>70
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.incrementScratch))=>71
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.ownerKey))=>72
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.factorKey))=>73
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.fieldScratch))=>74
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.valid))=>75
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.copyScratch))=>76
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.normScratch))=>77
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.frameBuffer))=>78
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.frameScratch))=>79
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.history))=>80
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.output))=>81
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.factors))=>82
  | .inr (.inl (RiemannGaussian.SemiprimeD1StackSourceOccurrences.Stack.occurrences))=>83
  | .inr (.inr (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left))))))=>84
  | .inr (.inr (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right))))))=>85
  | .inr (.inr (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch))))))=>86
  | .inr (.inr (.inl (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output))))))=>87
  | .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query))))))=>88
  | .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader))))))=>89
  | .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch))))))=>90
  | .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid))))))=>91
  | .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch))))))=>92
  | .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard))))))=>93
  | .inr (.inr (.inl (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output))))))=>94
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.source)))))=>95
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.reader)))))=>96
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.raw)))))=>97
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.dictionary)))))=>98
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.count)))))=>99
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.maximum)))))=>100
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.incScratch)))))=>101
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.incNext)))))=>102
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.trimScratch)))))=>103
  | .inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackSourceKeyFrequency.Aux.frameScratch)))))=>104
  | .inr (.inr (.inl (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left)))))))=>105
  | .inr (.inr (.inl (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right)))))))=>106
  | .inr (.inr (.inl (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch)))))))=>107
  | .inr (.inr (.inl (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output)))))))=>108
  | .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query)))))))=>109
  | .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader)))))))=>110
  | .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch)))))))=>111
  | .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid)))))))=>112
  | .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch)))))))=>113
  | .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard)))))))=>114
  | .inr (.inr (.inl (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output)))))))=>115
  | .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.key))))))=>116
  | .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.catalogue))))))=>117
  | .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.keyReader))))))=>118
  | .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftBytes))))))=>119
  | .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftHistory))))))=>120
  | .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.rightHistory))))))=>121
  | .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftOutput))))))=>122
  | .inr (.inr (.inl (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.rightOutput))))))=>123
  | .inr (.inr (.inl (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left)))))))=>124
  | .inr (.inr (.inl (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right)))))))=>125
  | .inr (.inr (.inl (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch)))))))=>126
  | .inr (.inr (.inl (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output)))))))=>127
  | .inr (.inr (.inl (.inr (.inr (.inl (.inr (PUnit.unit)))))))=>128
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.leftInput))))))=>129
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.rightInput))))))=>130
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.indexInput))))))=>131
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.leftReader))))))=>132
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.rightReader))))))=>133
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.indexCursor))))))=>134
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.leftColour))))))=>135
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.rightColour))))))=>136
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.copyScratch))))))=>137
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.keyHistory))))))=>138
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.slotHistory))))))=>139
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.keyOutput))))))=>140
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.slotOutput))))))=>141
  | .inr (.inr (.inl (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackPacketOrientation.Aux.highOutput))))))=>142
  | .inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left)))))=>143
  | .inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right)))))=>144
  | .inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch)))))=>145
  | .inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output)))))=>146
  | .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query)))))=>147
  | .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader)))))=>148
  | .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch)))))=>149
  | .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid)))))=>150
  | .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch)))))=>151
  | .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard)))))=>152
  | .inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output)))))=>153
  | .inr (.inr (.inr (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left)))))))=>154
  | .inr (.inr (.inr (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right)))))))=>155
  | .inr (.inr (.inr (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch)))))))=>156
  | .inr (.inr (.inr (.inr (.inl (.inl (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output)))))))=>157
  | .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.query)))))))=>158
  | .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.reader)))))))=>159
  | .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.fieldScratch)))))))=>160
  | .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.valid)))))))=>161
  | .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.copyScratch)))))))=>162
  | .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.discard)))))))=>163
  | .inr (.inr (.inr (.inr (.inl (.inl (.inr (RiemannGaussian.SemiprimeD1StackOwnerLookup.Aux.output)))))))=>164
  | .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.key))))))=>165
  | .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.catalogue))))))=>166
  | .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.keyReader))))))=>167
  | .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftBytes))))))=>168
  | .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftHistory))))))=>169
  | .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.rightHistory))))))=>170
  | .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.leftOutput))))))=>171
  | .inr (.inr (.inr (.inr (.inl (.inr (RiemannGaussian.SemiprimeD1StackPacketRows.Aux.rightOutput))))))=>172
  | .inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.left))))))=>173
  | .inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.right))))))=>174
  | .inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.scratch))))))=>175
  | .inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackAdder.Stack.output))))))=>176
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1TensorTapeFieldMachine.Stack.input))))))))=>177
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1TensorTapeFieldMachine.Stack.scratch))))))))=>178
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (.inl (RiemannGaussian.SemiprimeD1TensorTapeFieldMachine.Stack.output))))))))=>179
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (.inr (PUnit.unit))))))))=>180
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.bank))))))))=>181
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.reader))))))))=>182
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.word))))))))=>183
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.fieldScratch))))))))=>184
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.valid))))))))=>185
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.copyScratch))))))))=>186
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.digits))))))))=>187
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.unaryScratch))))))))=>188
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.unary))))))))=>189
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.logScratch))))))))=>190
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.history))))))))=>191
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (RiemannGaussian.SemiprimeD1StackPortOrdinalStream.Stack.output))))))))=>192
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.environment))))))))=>193
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.catalogue))))))))=>194
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.owners))))))))=>195
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.factors))))))))=>196
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.occurrences))))))))=>197
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.placements))))))))=>198
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.packets))))))))=>199
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.colourIndex))))))))=>200
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.group))))))))=>201
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldAxes))))))))=>202
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldPrecision))))))))=>203
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.jetAxis))))))))=>204
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.newPrecision))))))))=>205
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.activation))))))))=>206
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.activationMap))))))))=>207
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.endpoints))))))))=>208
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldEndpoints))))))))=>209
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.buckets))))))))=>210
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.leftPorts))))))))=>211
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.orders))))))))=>212
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.output))))))))=>213
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.vertexTodo))))))))=>214
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.vertexKey))))))))=>215
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.selectedID))))))))=>216
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.jointKey))))))))=>217
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.pairReader))))))))=>218
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.placementReader))))))))=>219
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.packetReader))))))))=>220
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.endpointReader))))))))=>221
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldReader))))))))=>222
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.childReader))))))))=>223
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.outerReader))))))))=>224
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.ownerKey))))))))=>225
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.factorKey))))))))=>226
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.sourceKey))))))))=>227
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.paddingKey))))))))=>228
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.packetKey))))))))=>229
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.slotWord))))))))=>230
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.edgeWord))))))))=>231
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.sideWord))))))))=>232
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.validWord))))))))=>233
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.colourReader))))))))=>234
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.colourCursor))))))))=>235
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.colourWord))))))))=>236
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.activationHistory))))))))=>237
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.endpointHistory))))))))=>238
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.oldHistory))))))))=>239
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.bucketHistory))))))))=>240
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.factorHistory))))))))=>241
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.portHistory))))))))=>242
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.orderHistory))))))))=>243
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.vertexHistory))))))))=>244
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.tagWord))))))))=>245
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.candidateTag))))))))=>246
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.localPosition))))))))=>247
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.globalPosition))))))))=>248
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.answerPosition))))))))=>249
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.frameBuffer))))))))=>250
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.rowBuffer))))))))=>251
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.copyScratch))))))))=>252
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.sentinelScratch))))))))=>253
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.flagScratch))))))))=>254
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.success))))))))=>255
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.orderBank))))))))=>256
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles.Aux.portBank))))))))=>257
theorem index_keys (k:R.Stack):keys[index k]?=some k:=by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> rfl
          · cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k
            · rcases k with k|k
              · cases k <;> rfl
              · cases k <;> rfl
            · cases k <;> rfl
          · rcases k with k|k
            · rcases k with k|k
              · cases k <;> rfl
              · cases k;rfl
            · cases k <;> rfl
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k
            · rcases k with k|k
              · cases k <;> rfl
              · cases k <;> rfl
            · cases k <;> rfl
          · rcases k with k|k
            · cases k <;> rfl
            · rcases k with k|k
              · rcases k with k|k
                · cases k <;> rfl
                · cases k;rfl
              · rcases k with k|k
                · cases k <;> rfl
                · cases k <;> rfl
def snapshot (d:R.Stack→List Bool):R.Stack→List Bool:=
  let values:=(keys.map d).toArray
  fun k=>(values[index k]?).getD []
theorem snapshot_eq (d:R.Stack→List Bool):snapshot d=d:=by
  funext k
  simp only [snapshot,List.getElem?_toArray,List.getElem?_map,index_keys,Option.map_some,Option.getD_some]
theorem eager_state_snapshot_eq (q:C.State R.Stack W.Label):
    (let values:=(keys.map q.data).toArray
     let fresh:R.Stack→List Bool:=fun k=>(values[index k]?).getD []
     {q with data:=fresh})=q:=by
  change {q with data:=snapshot q.data}=q
  rw [snapshot_eq]
def drive:Nat→C.State R.Stack W.Label→Nat→Option (C.State R.Stack W.Label×Nat)
  | 0,_,_=>none
  | fuel+1,s,n=>match s.pc with
    | none=>some (s,n)
    | some _=>match C.step R.program s with
      | none=>none
      | some q=>
        let values:=(keys.map q.data).toArray
        let fresh:R.Stack→List Bool:=fun k=>(values[index k]?).getD []
        drive fuel {q with data:=fresh} (n+1)
def selector:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool:=fun k=>
  if k=SemiprimeD1StackChildGroupFactoryReady.S.environmentStack (SemiprimeD1StackSourceEnvironment.aux .dictionary) then [false]
  else if k=SemiprimeD1StackChildGroupFactoryReady.S.aux .catalogue then
    SemiprimeD1StackOwnerLookup.records [([],SemiprimeSourceHistogramKeyBits.frame [] [])] []
  else if k=SemiprimeD1StackChildGroupFactoryReady.S.aux .owners ∨ k=SemiprimeD1StackChildGroupFactoryReady.S.aux .factors then []
  else [true,false,true]
def occurrence:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool:=fun k=>if k=.output then [false] else [false,true]
def inventory:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool:=fun k=>
  if k=SemiprimeD1StackChildGroupFactoryReady.I.output ∨ k=SemiprimeD1StackChildGroupFactoryReady.I.packets then [false]
  else [true,true,false]
def header:R.Header:=⟨[],[],SemiprimeD1TensorTapeCodec.vectorBits [[true,true]],[false,true],[true,true,true],[true,false,true]⟩
def input:=R.sourceInputs selector occurrence inventory header
def expected:R.Stack→List Bool
  | .inl k=>selector k
  | .inr (.inl k)=>occurrence k
  | .inr (.inr (.inl k))=>inventory k
  | .inr (.inr (.inr k))=>if R.factory k=R.allocation k then
      SemiprimeD1StackChildGroupFactoryExecution.result input 0 0 [] [] [] k else []
def run:IO Unit:=do
  unless keys.length=258 do throw (IO.userError "ready inventory count")
  let some (out,steps):=drive 10000 (R.initial selector occurrence inventory header) 0
    | throw (IO.userError "ready actual source did not halt")
  let mismatches:=keys.filter (fun k=>out.data k != expected k)
  unless mismatches.isEmpty && out.pc.isNone && out.flag.isNone && out.returned.isNone && out.frames.isEmpty do
    throw (IO.userError s!"ready mismatch count={mismatches.length} steps={steps}")
  IO.println s!"CHILD_GROUP_FACTORY_READY cases=1 actual_steps={steps} all258=true all143_producers_retained=true unrelated_stale_producers=true seven_unused_shadows_empty=true prepared_empty=true generic_old_new_headers=true actual_final_return_eof=true"
#eval run
end ChildGroupFactoryReadyEagerControls
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut checked:Nat:=0
  for (name,_) in env.constants.toList do
    unless (`ChildGroupFactoryReadyEagerControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "observer axiom {name}: {ax}"
    checked:=checked+1
  logInfo m!"CHILD_GROUP_FACTORY_READY_OBSERVER_STD3 {checked}"
