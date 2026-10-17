import InitECandidate.Solver.Input.RlpWrite.U256PutProgram

namespace InitECandidate.Solver.Input.RlpWrite.U256Put
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def marked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind {source with clock:=source.clock-1} "mark" cursor
def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind (WitnessRadix.PersistentAlloc.post {marked source cursor with clock:=(marked source cursor).clock-1} cursor 32#64) "tmp" cursor

theorem prepare_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) (codes : Codes source)
    (fits : cursor.toNat+32≤33806089496) (enough : 2≤source.clock) :
    evaluateHOLFiniteState source body=
      (let output:=evaluateHOLFiniteState (prepared source cursor) afterTemporary
      (output.1,restore source "mark" (restore (marked source cursor) "tmp" output.2))) := by
  classical
  have markRun:=HeapScope.mark_call_execute source cursor "mark" afterMark heap codes.markCode (by omega)
  have args : evalListHOLFinite (marked source cursor) (h:=fun address=>Classical.propDecidable ((marked source cursor).memaddrs address)) [.const 32#64]=
      some (WitnessRadix.PersistentAlloc.values 32#64):=rfl
  have allocRun:=WitnessRadix.PersistentAlloc.call_execute (marked source cursor) "tmp" [.const 32#64] afterTemporary cursor 32#64 args codes.allocCode heap
    (by simpa using fits) (by change 1≤source.clock-1; omega)
  rw [body_shape,markRun]
  change (let output:=evaluateHOLFiniteState (marked source cursor) afterMark; (output.1,restore source "mark" output.2))=_
  rw [afterMark,allocRun]
  rfl

theorem prepared_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :
    prepared source cursor={source with
      locals:=(prepared source cursor).locals
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 32#64)))
      clock:=source.clock-1-1}:=rfl

theorem prepared_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (name : String)
    (markNe : ofString "mark"≠ofString name) (tmpNe : ofString "tmp"≠ofString name) :
    (prepared source cursor).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "tmp" name _ tmpNe).trans (bind_lookup_other _ "mark" name _ markNe)

theorem prepared_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :
    (prepared source cursor).locals.lookup (ofString "tmp")=some (.val (.word cursor)) ∧
      (prepared source cursor).locals.lookup (ofString "mark")=some (.val (.word cursor)) :=
  ⟨bind_lookup_same _ _ _,(bind_lookup_other _ "tmp" "mark" _ (by decide)).trans (bind_lookup_same _ _ _)⟩

theorem prepared_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :
    (prepared source cursor).globals.lookup (ofString "heap_ptr")=some (.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 32#64))) := by
  change (source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 32#64)))).lookup (ofString "heap_ptr")=_
  simp [HolFiniteMapExact.update,FUPDATE]

end InitECandidate.Solver.Input.RlpWrite.U256Put

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.prepare_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.prepared_state
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.prepared_other
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.prepared_locals
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.prepared_heap
