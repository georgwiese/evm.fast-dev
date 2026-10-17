import InitECandidate.Solver.MutableTable.WitnessDictionaryCall
import InitECandidate.Solver.MutableTable.WitnessDictionaryFields
import InitECandidate.Solver.MutableTable.WitnessRunAttempt

namespace InitECandidate.Solver.MutableTable.WitnessRunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessBuild
open Flapjack.Basis.Pure.MlString QueryBranch

def withTable (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (table : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 table))) source

/-- Both actual initialization calls resume the real runtime suffix, with the
correct nested lexical restorations. The two constructor contracts supply real
ABI execution rather than assuming a run of the whole initialization suffix. -/
theorem initialization_execute (source firstTarget secondTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodeTable codeTable : Nat)
    (firstCall : ConstructorReturn source firstTarget (arguments 40) nodeTable)
    (secondCall : ConstructorReturn (withTable firstTarget "nodedb" nodeTable) secondTarget (arguments 56) codeTable) :
    evaluateHOLFiniteState source initialization=
      (let output:=evaluateHOLFiniteState (withTable secondTarget "codedb" codeTable) runtime;
        (output.1,restore source "nodedb" (restore (withTable firstTarget "nodedb" nodeTable) "codedb" output.2))) := by
  have nextRun:=secondCall.resume "codedb" runtime
  simp only [withTable] at nextRun ⊢
  rw [initialization_shape,firstCall.resume "nodedb" _,nextRun]

/-- Conditional whole initialization connection: both actual constructor calls
leave BOTH original/radix dictionary pairs represented at the real runtime
entry. Earlier dictionaries survive the second call by concrete own-memory
frames and allocation ordering. Startup/decoder/header reachability and the
constructor entry obligations remain outside this composition theorem. -/
theorem paired_initialization (source right leftFirst rightFirst leftSecond rightSecond : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodeRecords nodeTable nodeCount codeRecords codeTable codeCount maximumNode maximumCode : Nat)
    (nodeObservation : DictionaryObservation nodeRecords nodeTable nodeCount)
    (codeObservation : DictionaryObservation codeRecords codeTable codeCount)
    (nodeSlices codeSlices : BitVec 64 → Graph.Slice) (stp pad scratch : BitVec 64)
    (region firstSafe : BitVec 64 → Prop)
    (firstCall : ConstructorPairResult source right leftFirst rightFirst (arguments 40) (arguments 40)
      nodeObservation nodeSlices scratch maximumNode region firstSafe)
    (secondCall : ConstructorPairResult (withTable leftFirst "nodedb" nodeTable) (withTable rightFirst "nodedb" nodeTable)
      leftSecond rightSecond (arguments 56) (arguments 56) codeObservation codeSlices scratch maximumCode region
      (fun query=>query.toNat<codeTable ∧ Keccak256.Protected stp pad scratch query))
    (before : nodeObservation.heapEnd≤codeTable)
    (stateArena : AllocatedBytes.Arena stp 200) (paddingArena : AllocatedBytes.Arena pad 136) (outputArena : AllocatedBytes.Arena scratch 32)
    (buffersBefore : stp.toNat+200≤nodeRecords ∧ pad.toNat+136≤nodeRecords ∧ scratch.toNat+32≤nodeRecords)
    (locals : source.locals=right.locals) :
    let leftReady:=withTable leftSecond "codedb" codeTable
    let rightReady:=withTable rightSecond "codedb" codeTable
    DictionaryPair leftReady rightReady nodeObservation nodeSlices scratch ∧
      DictionaryPair leftReady rightReady codeObservation codeSlices scratch ∧
      leftReady.locals=rightReady.locals ∧ leftReady.globals=rightReady.globals ∧ leftReady.ffi=rightReady.ffi ∧
      MemoryRegion.Agree region leftReady.memory rightReady.memory ∧
      evaluateHOLFiniteState source initialization=
        (let output:=evaluateHOLFiniteState leftReady runtime;
          (output.1,restore source "nodedb" (restore (withTable leftFirst "nodedb" nodeTable) "codedb" output.2))) ∧
      evaluateHOLFiniteState right initialization=
        (let output:=evaluateHOLFiniteState rightReady runtime;
          (output.1,restore right "nodedb" (restore (withTable rightFirst "nodedb" nodeTable) "codedb" output.2))) := by
  let leftEntry:=withTable leftFirst "nodedb" nodeTable
  let rightEntry:=withTable rightFirst "nodedb" nodeTable
  let leftReady:=withTable leftSecond "codedb" codeTable
  let rightReady:=withTable rightSecond "codedb" codeTable
  have enteredPair:=DictionaryPair.of_fields leftFirst rightFirst leftEntry rightEntry nodeObservation nodeSlices scratch
    rfl rfl rfl rfl rfl rfl firstCall.dictionary
  have leftFields:=ConstructorReturn.fields leftEntry leftSecond (arguments 56) codeTable secondCall.leftCall
  have rightFields:=ConstructorReturn.fields rightEntry rightSecond (arguments 56) codeTable secondCall.rightCall
  have savedPair:=DictionaryPair.preserved_by_later leftEntry rightEntry leftSecond rightSecond nodeObservation nodeSlices scratch enteredPair
    codeTable before stp pad scratch stateArena paddingArena outputArena buffersBefore
    leftFields.1.symm rightFields.1.symm leftFields.2.1.symm rightFields.2.1.symm secondCall.leftFrame secondCall.rightFrame
  have nodePair:=DictionaryPair.of_fields leftSecond rightSecond leftReady rightReady nodeObservation nodeSlices scratch
    rfl rfl rfl rfl rfl rfl savedPair
  have codePair:=DictionaryPair.of_fields leftSecond rightSecond leftReady rightReady codeObservation codeSlices scratch
    rfl rfl rfl rfl rfl rfl secondCall.dictionary
  refine ⟨nodePair,codePair,?_,secondCall.globals,secondCall.ffi,secondCall.memory,
    initialization_execute source leftFirst leftSecond nodeTable codeTable firstCall.leftCall secondCall.leftCall,
    initialization_execute right rightFirst rightSecond nodeTable codeTable firstCall.rightCall secondCall.rightCall⟩
  change leftSecond.locals.update _=rightSecond.locals.update _
  rw [secondCall.leftCall.locals,secondCall.rightCall.locals]
  change (leftFirst.locals.update _).update _=(rightFirst.locals.update _).update _
  rw [firstCall.leftCall.locals,firstCall.rightCall.locals,locals]

end InitECandidate.Solver.MutableTable.WitnessRunAttempt

#print axioms InitECandidate.Solver.MutableTable.WitnessRunAttempt.initialization_execute
#print axioms InitECandidate.Solver.MutableTable.WitnessRunAttempt.paired_initialization
