import InitECandidate.Solver.Mpt.WitnessCoreStackBranchScope

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Close an enclosing lexical scope without losing the actual
physical branch transition or any of its four control/result bindings. -/
theorem BranchStep.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit child slot : BitVec 64) (entry : Entry) (rest : List Entry)
    (step : BranchStep source db heap cursor limit child slot entry rest)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs)
    (topCell : target.locals.lookup (ofString "top")=source.locals.lookup (ofString "top"))
    (slotCell : target.locals.lookup (ofString "slot")=source.locals.lookup (ofString "slot"))
    (modeCell : target.locals.lookup (ofString "mode")=source.locals.lookup (ofString "mode"))
    (resultCell : target.locals.lookup (ofString "result")=source.locals.lookup (ofString "result")) :
    BranchStep target db heap cursor limit child slot entry rest := by
  rcases step with ⟨next,sameRecord,sameMark,samePending,sameArray,samePayload,view,top,slotValue,mode,result,rank⟩|⟨view,node,owned,top,result,mode,slotValue,rank⟩
  · exact Or.inl ⟨next,sameRecord,sameMark,samePending,sameArray,samePayload,
      view.of_fields source target db cursor.toNat heap.toNat (next::rest) memory domain,
      topCell.trans top,slotCell.trans slotValue,modeCell.trans mode,resultCell.trans result,rank⟩
  · exact Or.inr ⟨view.of_fields source target db cursor.toNat heap.toNat rest memory domain,node,
      owned.of_fields source target node (max (resultLower rest) entry.data.payload.startAddress) heap.toNat memory,
      topCell.trans top,resultCell.trans result,modeCell.trans mode,slotCell.trans slotValue,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.BranchStep.of_fields
