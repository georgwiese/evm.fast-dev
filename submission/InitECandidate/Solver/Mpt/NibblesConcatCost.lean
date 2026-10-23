import InitECandidate.Solver.Mpt.NibblesConcatAllocation
import InitECandidate.Solver.Mpt.NibblesConcatCopiesCost
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every original concatenation outcome, including allocator failure and
timeouts. Physical destination room is derived only if allocation returns;
the byte lengths are charged by the real memcpy loop counts. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap a al b bl : BitVec 64)
    (sourceA : AllocatedBytes.Arena a al.toNat) (sourceB : AllocatedBytes.Arena b bl.toNat)
    (aCell : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (alCell : source.locals.lookup (ofString "al")=some (.val (.word al)))
    (bCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (blCell : source.locals.lookup (ofString "bl")=some (.val (.word bl)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤al.toNat/8+bl.toNat/8+18 := by
  have amount : (al+bl).toNat=al.toNat+bl.toNat:=BitVec.toNat_add_of_lt (by have left:=sourceA.upper; have right:=sourceB.upper; omega)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=some (PersistentAlloc.values (al+bl)):=by
    simp [allocationArguments,amountExpression,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,alCell,blCell,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup (al+bl) (PersistentAlloc.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have calleePrice:=PersistentAlloc.body_price source.code installed entry rfl
  rw [body_shapes.1]
  have priced:=Input.ClockCost.scoped_reached_current source "out" .one (ofString "alloc") allocationArguments (PersistentAlloc.values (al+bl))
    PersistentAlloc.body afterAllocation callee .one 1 (al.toNat/8+bl.toNat/8+16) args called calleePrice (by
      intro target returned normal checked
      obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal entry target heap (al+bl) amountCell heapCell
        (by have upper:=frontier.upper; omega) (Input.Trap.original_code source.code installed) returned normal
      have destination : AllocatedBytes.Arena heap (al.toNat+bl.toNat):=⟨frontier.lower,by rw [amount] at room; exact room⟩
      let ready:=Input.CallNormal.continuationEntry source target "out" returned
      have fields:=Input.evaluation_fields entry target PersistentAlloc.body (some (.returned returned)) normal
      have currentDomain : ready.memaddrs=InitE.ordinaryDomain:=fields.1.trans domain
      have currentCode : ready.code=source.code:=fields.2.2.2
      have currentInstalled : Input.OriginalCode.Installed ready.code:=by rw [currentCode]; exact installed
      have aReady : ready.locals.lookup (ofString "a")=some (.val (.word a)):=by
        simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "out"≠ofString "a" from by decide,aCell]
      have alReady : ready.locals.lookup (ofString "al")=some (.val (.word al)):=by
        simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "out"≠ofString "al" from by decide,alCell]
      have bReady : ready.locals.lookup (ofString "b")=some (.val (.word b)):=by
        simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "out"≠ofString "b" from by decide,bCell]
      have blReady : ready.locals.lookup (ofString "bl")=some (.val (.word bl)):=by
        simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "out"≠ofString "bl" from by decide,blCell]
      have outReady : ready.locals.lookup (ofString "out")=some (.val (.word heap)):=by
        simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
      exact copies_cost ready heap a al b bl sourceA sourceB destination aReady alReady bReady blReady outReady currentDomain currentInstalled)
  omega

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.body_cost
