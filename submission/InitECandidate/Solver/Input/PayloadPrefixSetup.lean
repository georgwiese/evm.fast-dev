import InitECandidate.Solver.Input.PayloadOffsetDeclarations

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor length : BitVec 64) :=
  declaredState (headerStored source pointer cursor length) input
def restorePrefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor length : BitVec 64)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "pl" (restoreDeclarations (headerStored source pointer cursor length) input target)

/-- Whole literal allocation/header/declaration prefix, with the real alloc
call clock, exact stores, input byte frame and all five lexical restorations. -/
theorem prefix_setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (enough : 1≤source.clock) :
    Executes source prefixActions (prepared source input pointer cursor length) (restorePrefix source input pointer cursor length) ∧
      Blob.HeapInput (prepared source input pointer cursor length) input pointer := by
  obtain ⟨s0,s1,headerHeap,cell0,cell8⟩:=header_stores source input pointer cursor length heap p n domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
  have headerP : (headerStored source pointer cursor length).locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} cursor 136#64) "pl" "p" cursor (by decide)).trans p
  obtain ⟨decls,finalHeap⟩:=offset_declarations (headerStored source pointer cursor length) input pointer headerHeap inside headerP
  have first:=Request.command_single (allocated source cursor) (pointerStored source pointer cursor) pointerStore s0 (Nat.le_refl (source.clock-1))
  have second:=Request.command_single (pointerStored source pointer cursor) (headerStored source pointer cursor length) lengthStore s1 (Nat.le_refl (source.clock-1))
  have headers:=executes_append first second
  have allCommands:=executes_append headers decls
  refine ⟨?_,finalHeap⟩
  exact Executes.allocate (restoreRest:=restoreDeclarations (headerStored source pointer cursor length) input)
    cursor 136#64 rfl allocCode heapGlobal (by change cursor.toNat+136≤33806089496; exact cursorRoom) enough allCommands

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.prefix_setup
