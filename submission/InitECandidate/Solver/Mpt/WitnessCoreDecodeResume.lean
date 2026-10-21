import InitECandidate.Solver.Mpt.WitnessCorePush
import InitECandidate.Solver.Mpt.WitnessCoreTerminal

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_decode_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag value : BitVec 64)
    (decodedCell : source.locals.lookup (ofString "d")=some (.rStruct [.val (.word tag),.val (.word value)])) :
    evaluateHOLFiniteState source afterDecode=
      if tag=0#64 then evaluateHOLFiniteState source decodeTerminal else evaluateHOLFiniteState source decodePush := by
  rw [after_decode_shape]
  by_cases zero : tag=0#64
  · simp [evaluateHOLFiniteState_ite,decodeField,evalHOLExact,localVar,toExact,decodedCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp [evaluateHOLFiniteState_ite,decodeField,evalHOLExact,localVar,toExact,decodedCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- The actual checked record return takes the original push branch and
executes its real mapped link/stage/local updates. -/
theorem after_decode_push (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db previous oldSlot oldMode : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data)
    (decodedCell : source.locals.lookup (ofString "d")=some (.rStruct [.val (.word 1#64),.val (.word record)]))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word previous)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    evaluateHOLFiniteState source afterDecode=(none,pushed source record previous data.payload) := by
  rw [after_decode_choice source 1#64 record decodedCell,if_neg (by decide)]
  exact push_execute source record db previous oldSlot oldMode data view decodedCell topCell slotCell modeCell

/-- The real checked terminal return takes the original result/mode branch
without mutating any record, witness database or other memory. -/
theorem after_decode_terminal (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node oldResult oldMode : BitVec 64)
    (decodedCell : source.locals.lookup (ofString "d")=some (.rStruct [.val (.word 0#64),.val (.word node)]))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    evaluateHOLFiniteState source afterDecode=(none,delivered source node) := by
  rw [after_decode_choice source 0#64 node decodedCell,if_pos rfl]
  exact terminal_execute source node oldResult oldMode decodedCell resultCell modeCell

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_decode_choice
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_decode_push
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_decode_terminal
