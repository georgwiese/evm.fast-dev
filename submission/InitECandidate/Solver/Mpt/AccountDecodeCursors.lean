import InitECandidate.Solver.Mpt.AccountDecodeFieldsNormal
import InitECandidate.Solver.Mpt.AccountDecodeTailGlobals

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Complete actual normal original account decoding restores its incoming
scratch/frame arena and allocates exactly the rounded64-byte record array.
All array room and the final heap bound follow from actual execution. -/
theorem body_cursors (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    Rlp.Validation.Arena post cursor limit ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      heap.toNat+64≤33806089496 ∧ (PersistentAlloc.rounded heap 64#64).toNat≤33806089496 := by
  obtain ⟨header,payload,a,b,c,d,ready,inner,extent,room,results,view,heapEntry,domain,endian,codeEq,memory,tailRun,frame⟩ :=
    body_fields source post pointer length heap cursor limit out cutoff pointerCell lengthCell outputCell arena heapGlobal heapBound before sizeBound
      aligned scratchBelow inputAbove output installed returned normal
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [codeEq]; exact installed
  have finalGlobals := congrArg PanSemStateFiniteExact.globals frame
  change post.globals=inner.globals at finalGlobals
  have globals (key : MlS) : post.globals.lookup key=ready.globals.lookup key := by
    have preserved := after_fields_globals key ready.code readyInstalled ready rfl
    rw [tailRun] at preserved
    rw [finalGlobals]
    exact congrArg Prod.snd preserved
  have finalDomain := (Input.evaluation_fields source post body (some (.returned returned)) normal).1
  have finalArena : Rlp.Validation.Arena post cursor limit :=
    ⟨finalDomain.trans arena.domain,(globals (ofString "scratch_ptr")).trans view.arena.cursorGlobal,
      (globals (ofString "frame_mem_ptr")).trans view.arena.limitGlobal,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
  have guards := PersistentAlloc.guards heap 64#64 room
  exact ⟨finalArena,(globals (ofString "heap_ptr")).trans heapEntry,room,guards.2.2.2.1⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.body_cursors
