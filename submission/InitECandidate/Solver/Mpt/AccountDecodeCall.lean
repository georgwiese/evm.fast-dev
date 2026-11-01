import InitECandidate.Solver.Mpt.AccountDecodeCost

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def values (pointer length out : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word pointer),.val (.word length),.val (.word out)]
def rawLocals (pointer length out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "acct_out" then some (.val (.word out)) else
  if name=ofString "n" then some (.val (.word length)) else
  if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (pointer length out : BitVec 64) (known : table (ofString "decode_account_from_leaf")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "decode_account_from_leaf") (values pointer length out)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "n")=some (.val (.word length)) ∧
      callee.lookup (ofString "acct_out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer length out).length ∧
      ((formals.zip (values pointer length out)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "decode_account_from_leaf") (values pointer length out)=some (body,rawLocals pointer length out,.one) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals
    rw [locals]
    simp [rawLocals,show ofString "p"≠ofString "acct_out" from by decide,
      show ofString "p"≠ofString "n" from by decide,show ofString "n"≠ofString "acct_out" from by decide]

/-- Ordinary original caller, including failed/exceptional outcomes and
the actual call tick. Entry geometry is current, not a callee-run premise. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out : BitVec 64) (cutoff : Nat)
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length out)) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "decode_account_from_leaf") arguments)).2.clock≤191*length.toNat+293 := by
  obtain ⟨callee,called,p,n,a⟩ := environment source.code.lookup pointer length out (original_code source.code installed)
  have cost := body_cost (callEntryStateHOLFinite source callee) pointer length heap cursor limit out cutoff p n a
    (Rlp.Validation.Arena.of_fields source _ cursor limit arena rfl rfl) heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove output installed
  exact Input.ClockCost.call_current source destination (ofString "decode_account_from_leaf") arguments _ body callee .one _ args called cost

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.environment
#print axioms InitECandidate.Solver.Mpt.AccountDecode.call_cost

namespace InitECandidate.Solver.Mpt.AccountDecode.Current
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual current account decoder caller, retaining all malformed,
exceptional and timeout outcomes. Zero length needs no payload order. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap out : BitVec 64) (arena : Rlp.LiveArena source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : length≠0#64→pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64) (output : Output out) (installed : Input.OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values pointer length out)) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "decode_account_from_leaf") arguments)).2.clock≤191*length.toNat+262 := by
  obtain ⟨callee,called,p,n,a⟩:=environment source.code.lookup pointer length out (original_code source.code installed)
  have priced:=body_cost (callEntryStateHOLFinite source callee) pointer length heap out p n a (arena.of_frame rfl)
    heapGlobal heapBound before sizeBound output installed
  exact Input.ClockCost.call_current source destination (ofString "decode_account_from_leaf") arguments _ body callee .one _ args called priced

end InitECandidate.Solver.Mpt.AccountDecode.Current

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Current.call_cost
