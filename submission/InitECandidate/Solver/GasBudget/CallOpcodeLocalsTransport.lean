import InitECandidate.Solver.GasBudget.CallOpcodeLocals

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack PanSemStateFiniteExact Input.RlpWrite

theorem ChargedLocals.of_locals {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame message current warm : BitVec 64} {value inStart inSize outStart outSize : U256Value.Words}
    (cells : ChargedLocals source frame message current value inStart inSize outStart outSize warm)
    (same : target.locals = source.locals) :
    ChargedLocals target frame message current value inStart inSize outStart outSize warm := by
  exact ⟨by rw [same]; exact cells.valueCell,
    by rw [same]; exact cells.inStartCell, by rw [same]; exact cells.inSizeCell,
    by rw [same]; exact cells.outStartCell, by rw [same]; exact cells.outSizeCell,
    by rw [same]; exact cells.xCell, by rw [same]; exact cells.vzCell,
    by rw [same]; exact cells.toCell, by rw [same]; exact cells.msgCell,
    by rw [same]; exact cells.warmCell, by rw [same]; exact cells.gasCell,
    by rw [same]; exact cells.toValueCell⟩

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.ChargedLocals.of_locals
