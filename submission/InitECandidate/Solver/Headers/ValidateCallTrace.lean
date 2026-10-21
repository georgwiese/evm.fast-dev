import InitECandidate.Solver.Headers.ValidateReturned
import InitECandidate.Solver.Headers.ValidateCallCost
import InitECandidate.Solver.Input.ScopedCallSuccess

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current physical call context, with one shared actual row-byte budget.
It contains no future successful allocation, comparison or return premise. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat) : Prop where
  installed : Input.OriginalCode.Installed source.code
  shape : source.eshapes.lookup (ofString "HdrErr")=some .one
  arena : Rlp.Validation.Arena source cursor limit
  environment : Keccak256.Environment source stp pad
  rows : Rows source array pointers lengths count.toNat lower upper
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapLower : 2701131776≤heap.toNat
  heapBound : heap.toNat≤33806089496
  heapAligned : heap.toNat%8=0
  before : upper≤heap.toNat
  stateArena : AllocatedBytes.Arena stp 200
  stateAligned : stp.toNat%8=0
  padArena : AllocatedBytes.Arena pad 136
  padAligned : pad.toNat%8=0
  stateBefore : stp.toNat+200≤lower
  padBefore : pad.toNat+136≤lower
  aligned : lower%8=0
  inputLower : 2701131776≤lower
  scratchBefore : cursor.toNat≤lower
  byteBudget : Input.VarList.sumPrefix (fun index=>(lengths index).toNat) count.toNat≤budget

def bodyPrice (count : BitVec 64) (budget : Nat) := 251*budget+1578*count.toNat+20*(budget/136)+130*(count.toNat-1)+4

theorem Context.callee (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (context : Context source array heap count cursor limit stp pad pointers lengths lower upper budget)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) : Context (callEntryStateHOLFinite source callee) array heap count cursor limit stp pad pointers lengths lower upper budget := by
  exact ⟨context.installed,context.shape,
    Rlp.Validation.Arena.of_fields source _ cursor limit context.arena rfl rfl,
    Keccak256.Environment.of_fields source _ stp pad context.environment rfl rfl rfl (by intro key other; rfl),
    context.rows.of_frame source _ array pointers lengths count.toNat lower upper ⟨by intro query low high; rfl⟩,
    context.heapCell,context.heapLower,context.heapBound,context.heapAligned,context.before,context.stateArena,context.stateAligned,
    context.padArena,context.padAligned,context.stateBefore,context.padBefore,context.aligned,context.inputLower,context.scratchBefore,context.byteBudget⟩

theorem Context.price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (context : Context source array heap count cursor limit stp pad pointers lengths lower upper budget)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyPrice count budget :=
  body_cost source array heap count cursor limit stp pad pointers lengths lower upper budget context.installed context.shape context.arena context.environment context.rows
    arrayCell countCell context.heapCell context.heapLower context.heapBound context.heapAligned context.before context.stateArena context.stateAligned context.padArena context.padAligned
    context.stateBefore context.padBefore context.aligned context.inputLower context.scratchBefore context.byteBudget

structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    extends Output source target array heap count cursor limit stp pad pointers lengths lower upper where
  code : target.code=source.code
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  exceptions : target.eshapes=source.eshapes
  oracle : target.ffi.oracle=source.ffi.oracle
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤bodyPrice count budget+1

/-- A true body return at the real call entry derives the complete caller
frame and cost, with the actual original pair of output pointers. -/
theorem callee_returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (context : Context source array heap count cursor limit stp pad pointers lengths lower upper budget)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : callee.lookup (ofString "n")=some (.val (.word count)))
    (value : ValueHOL 64) (funded : 1≤source.clock)
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target)) :
    value=result heap (hashesPointer heap count) ∧ Returned source target array heap count cursor limit stp pad pointers lengths lower upper budget := by
  let entry:=callEntryStateHOLFinite source callee
  have ready:=context.callee source array heap count cursor limit stp pad pointers lengths lower upper budget callee
  have price:=ready.price entry array heap count cursor limit stp pad pointers lengths lower upper budget arrayCell countCell
  have clock:=evaluateHOLFiniteState_clock_le entry body
  rw [normal] at price clock
  change source.clock-1-target.clock≤bodyPrice count budget at price
  change target.clock≤source.clock-1 at clock
  obtain ⟨valueEq,output⟩ := body_returned entry target array heap count cursor limit stp pad pointers lengths lower upper ready.installed ready.shape ready.arena ready.environment ready.rows
    arrayCell countCell ready.heapCell ready.heapLower ready.heapBound ready.heapAligned ready.before ready.stateArena ready.stateAligned ready.padArena ready.padAligned
    ready.stateBefore ready.padBefore ready.aligned ready.inputLower ready.scratchBefore value normal
  have fields:=Input.evaluation_fields entry target body (some (.returned value)) normal
  have outputFrame : Output source target array heap count cursor limit stp pad pointers lengths lower upper :=
    ⟨output.smallCount,output.geometry,output.currentHeap,output.arena,output.environment,⟨output.memory.words⟩,output.rows,output.globals,output.heapBound⟩
  exact ⟨valueEq,outputFrame,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,Input.evaluation_oracle entry target body (some (.returned value)) normal,by omega,by omega⟩

/-- Every actual scoped call either stops within its own allowance or
reaches the genuine continuation with the derived output/context. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (context : Context source array heap count cursor limit stp pad pointers lengths lower upper budget)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word array),.val (.word count)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "validate_headers") expressions continuation)=(outcome,post)) :
    source.clock-post.clock≤bodyPrice count budget+1 ∨ ∃ target inner,Returned source target array heap count cursor limit stp pad pointers lengths lower upper budget ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (result heap (hashesPointer heap count))) continuation=(outcome,inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,arrayCell,countCell⟩ := Input.word_pair_environment source.code.lookup (ofString "validate_headers") (ofString "arr") (ofString "n") body resultShape array count (by decide) (original_code source.code context.installed)
  have ready:=context.callee source array heap count cursor limit stp pad pointers lengths lower upper budget callee
  have price:=ready.price (callEntryStateHOLFinite source callee) array heap count cursor limit stp pad pointers lengths lower upper budget arrayCell countCell
  rcases Input.CallNormal.scoped_trace source post name resultShape (ofString "validate_headers") expressions _ body continuation callee resultShape (bodyPrice count budget) args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨valueEq,output⟩ := callee_returned source target array heap count cursor limit stp pad pointers lengths lower upper budget context callee arrayCell countCell value funded bodyRun
    rw [valueEq] at continued
    exact Or.inr ⟨target,inner,output,continued,endpoint⟩

/-- Observed successful enclosing execution forces the original callee's
normal return; it cannot be discharged by the early-stopping cost branch. -/
theorem scoped_success (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (context : Context source array heap count cursor limit stp pad pointers lengths lower upper budget)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word array),.val (.word count)])
    (outcome : Option (PanSemResultExact 64)) (success : outcome=none ∨ ∃ value,outcome=some (.returned value))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "validate_headers") expressions continuation)=(outcome,post)) :
    ∃ target inner,Returned source target array heap count cursor limit stp pad pointers lengths lower upper budget ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (result heap (hashesPointer heap count))) continuation=(outcome,inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,arrayCell,countCell⟩ := Input.word_pair_environment source.code.lookup (ofString "validate_headers") (ofString "arr") (ofString "n") body resultShape array count (by decide) (original_code source.code context.installed)
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩ := Input.CallNormal.scoped_success source post name resultShape (ofString "validate_headers") expressions _ body continuation callee resultShape args called outcome success run
  obtain ⟨valueEq,output⟩ := callee_returned source target array heap count cursor limit stp pad pointers lengths lower upper budget context callee arrayCell countCell value funded bodyRun
  rw [valueEq] at continued
  exact ⟨target,inner,output,continued,endpoint⟩

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.Context.callee
#print axioms InitECandidate.Solver.Headers.Validate.Context.price
#print axioms InitECandidate.Solver.Headers.Validate.callee_returned
#print axioms InitECandidate.Solver.Headers.Validate.scoped_trace
#print axioms InitECandidate.Solver.Headers.Validate.scoped_success
