import InitECandidate.Solver.GasBudget.CallOpcodeCostProgram

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

/-- Bindings at the actual first charged CALL suffix. In particular, the
value and cost pair are the operands used in that charge. -/
structure ChargedLocals (ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message current : BitVec 64) (value inStart inSize outStart outSize : U256Value.Words)
    (warm : BitVec 64) : Prop where
  valueCell : ready.locals.lookup (ofString "value") = some (U256Value.tuple value)
  inStartCell : ready.locals.lookup (ofString "in_start") = some (U256Value.tuple inStart)
  inSizeCell : ready.locals.lookup (ofString "in_size") = some (U256Value.tuple inSize)
  outStartCell : ready.locals.lookup (ofString "out_start") = some (U256Value.tuple outStart)
  outSizeCell : ready.locals.lookup (ofString "out_size") = some (U256Value.tuple outSize)
  xCell : ready.locals.lookup (ofString "x") = some (MemoryExpansionCost.pairValue
    (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current))
  vzCell : ready.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord value)))
  toCell : ready.locals.lookup (ofString "to") = some (.val (.word (frame + 240#64)))
  msgCell : ready.locals.lookup (ofString "msg") = some (.val (.word message))
  warmCell : ready.locals.lookup (ofString "warm") = some (.val (.word warm))
  gasCell : ∃ gas, ready.locals.lookup (ofString "gasv") = some (U256Value.tuple gas)
  toValueCell : ∃ address, ready.locals.lookup (ofString "tov") = some (U256Value.tuple address)

theorem charged_locals_of_preservation
    (entry costReady ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message current : BitVec 64) (value inStart inSize outStart outSize : U256Value.Words)
    (warm : BitVec 64)
    (valueCell : entry.locals.lookup (ofString "value") = some (U256Value.tuple value))
    (inStartCell : entry.locals.lookup (ofString "in_start") = some (U256Value.tuple inStart))
    (inSizeCell : entry.locals.lookup (ofString "in_size") = some (U256Value.tuple inSize))
    (outStartCell : entry.locals.lookup (ofString "out_start") = some (U256Value.tuple outStart))
    (outSizeCell : entry.locals.lookup (ofString "out_size") = some (U256Value.tuple outSize))
    (gasCell : ∃ gas, entry.locals.lookup (ofString "gasv") = some (U256Value.tuple gas))
    (toValueCell : ∃ address, entry.locals.lookup (ofString "tov") = some (U256Value.tuple address))
    (costX : costReady.locals.lookup (ofString "x") = some (MemoryExpansionCost.pairValue
      (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current)))
    (costVZ : costReady.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord value))))
    (costTo : costReady.locals.lookup (ofString "to") = some (.val (.word (frame + 240#64))))
    (costMsg : costReady.locals.lookup (ofString "msg") = some (.val (.word message)))
    (costOther : ∀ key : String, ofString "x" ≠ ofString key → ofString "vz" ≠ ofString key → ofString "msg" ≠ ofString key →
      costReady.locals.lookup (ofString key) = entry.locals.lookup (ofString key))
    (warmCell : ready.locals.lookup (ofString "warm") = some (.val (.word warm)))
    (feeOther : ∀ key : String, ofString "need" ≠ ofString key → ofString "transfer_cost" ≠ ofString key →
      ofString "access_cost" ≠ ofString key → ofString "warm" ≠ ofString key →
      ready.locals.lookup (ofString key) = costReady.locals.lookup (ofString key)) :
    ChargedLocals ready frame message current value inStart inSize outStart outSize warm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, warmCell, ?_, ?_⟩
  · exact (feeOther "value" (by decide) (by decide) (by decide) (by decide)).trans
      ((costOther "value" (by decide) (by decide) (by decide)).trans valueCell)
  · exact (feeOther "in_start" (by decide) (by decide) (by decide) (by decide)).trans
      ((costOther "in_start" (by decide) (by decide) (by decide)).trans inStartCell)
  · exact (feeOther "in_size" (by decide) (by decide) (by decide) (by decide)).trans
      ((costOther "in_size" (by decide) (by decide) (by decide)).trans inSizeCell)
  · exact (feeOther "out_start" (by decide) (by decide) (by decide) (by decide)).trans
      ((costOther "out_start" (by decide) (by decide) (by decide)).trans outStartCell)
  · exact (feeOther "out_size" (by decide) (by decide) (by decide) (by decide)).trans
      ((costOther "out_size" (by decide) (by decide) (by decide)).trans outSizeCell)
  · exact (feeOther "x" (by decide) (by decide) (by decide) (by decide)).trans costX
  · exact (feeOther "vz" (by decide) (by decide) (by decide) (by decide)).trans costVZ
  · exact (feeOther "to" (by decide) (by decide) (by decide) (by decide)).trans costTo
  · exact (feeOther "msg" (by decide) (by decide) (by decide) (by decide)).trans costMsg
  · obtain ⟨gas, cell⟩ := gasCell
    exact ⟨gas, (feeOther "gasv" (by decide) (by decide) (by decide) (by decide)).trans
      ((costOther "gasv" (by decide) (by decide) (by decide)).trans cell)⟩
  · obtain ⟨address, cell⟩ := toValueCell
    exact ⟨address, (feeOther "tov" (by decide) (by decide) (by decide) (by decide)).trans
      ((costOther "tov" (by decide) (by decide) (by decide)).trans cell)⟩

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.charged_locals_of_preservation
