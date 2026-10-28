import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Program
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LoopState
import InitECandidate.Solver.Headers.ValidateRows

namespace InitECandidate.Solver.Input.CurrentTable.NodeLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem present_read (data : NodeBuild.Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper)
    (inside : index<data.total) (domain : source.memaddrs=InitE.ordinaryDomain)
    (rCell : source.locals.lookup (ofString "r")=some (Get.presentValue (byteAddress data.array (16*index)))) :
    eval source (.rstruct [.const 1#64,.load .one recordPointer,.load .one (.op .add [recordPointer,.const 8#64])])=
      some (presentValue (data.pointers index) (data.lengths index)) := by
  have pointerRead : eval source recordPointer=some (.val (.word (byteAddress data.array (16*index)))) := by
    simp [recordPointer,eval,evalHOLExact,toExact,localVar,rCell,Get.presentValue]
  have firstMapped := AllocatedBytes.word_mapped source (byteAddress data.array (16*index)) 16 0 domain
    (rows.rowArena index inside) (by decide) (rows.rowAligned index inside) (by decide)
  have secondMapped := AllocatedBytes.word_mapped source (byteAddress data.array (16*index)) 16 8 domain
    (rows.rowArena index inside) (by decide) (rows.rowAligned index inside) (by decide)
  have firstRead := Witness.load_word_read source recordPointer (byteAddress data.array (16*index)) (data.pointers index)
    pointerRead (by simpa [byteAddress] using firstMapped) (rows.cells index inside).1
  have lengthAddress := Scalar.plus_read source recordPointer (byteAddress data.array (16*index)) 8 pointerRead
  have secondRead := Witness.load_word_read source (.op .add [recordPointer,.const 8#64]) (byteAddress data.array (16*index)+8#64) (data.lengths index)
    lengthAddress secondMapped (rows.cells index inside).2
  simp only [eval] at firstRead secondRead ⊢
  rw [evalHOLExact]
  simp only [evalListHOLExact,firstRead,secondRead]
  rfl

end InitECandidate.Solver.Input.CurrentTable.NodeLookup

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.present_read
