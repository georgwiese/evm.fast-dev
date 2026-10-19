import InitECandidate.Solver.Mpt.WsAccountLeafCursors

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Normal allocation derives its temporary32-byte room before any hash,
trie or mapped-buffer model is required. -/
theorem after_mark_room (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤33806089496) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterMark=(some (.returned returned),post)) : pointer.toNat+32≤33806089496 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,positive,inner,tailRun,restored⟩ := PersistentAlloc.call_normal source post "h" [.const 32#64] afterAlloc pointer 32#64 args
    (alloc_original_code source.code installed) (Input.Trap.original_code source.code installed) heap bounded returned normal
  exact room

/-- The real original account-leaf call derives temporary allocation room
using only its current heap and actual normal execution, with no future
hash-data or value model in the premises. -/
theorem body_room (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤33806089496) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : pointer.toNat+32≤33806089496 := by
  rw [body_shape] at normal
  have positive := Input.CallNormal.normal_clock source post (ofString "mark") .one (ofString "heap_mark") [] afterMark returned normal
  let ready := bind {source with clock:=source.clock-1} "mark" pointer
  let inner := (evaluateHOLFiniteState ready afterMark).2
  have actual := Input.HeapScope.mark_call_execute source pointer "mark" afterMark heap (Input.HeapScope.mark_original_code source.code installed) positive
  have joined := actual.symm.trans normal
  have resultEq := congrArg Prod.fst joined
  change (evaluateHOLFiniteState ready afterMark).1=some (.returned returned) at resultEq
  have innerRun : evaluateHOLFiniteState ready afterMark=(some (.returned returned),inner) := Prod.ext resultEq rfl
  have postEq := (congrArg Prod.snd joined).symm
  change post=restore source "mark" inner at postEq
  exact after_mark_room ready inner pointer heap bounded installed returned innerRun

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_mark_room
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.body_room
