import InitECandidate.Solver.Mpt.AccountDecodeNormalPrefix
import InitECandidate.Solver.Mpt.AccountAfterDecodeNormal
import InitECandidate.Solver.Mpt.AccountFieldsNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- A real normal complete original account body reaches afterFields with
its actual four decoded values. Both validation passes, record allocation,
count guard and every item call are included in the derived state/frame. -/
theorem body_fields (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    ∃ (header payload : BitVec 64) (a b c d : Rlp.ListItem) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      header.toNat+payload.toNat=length.toNat ∧ heap.toNat+64≤33806089496 ∧ Nonempty (FieldResults ready (pointer+header) a b c d) ∧
      FieldsView ready heap (pointer+header) payload cursor limit out cutoff [a,b,c,d] ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat → ready.memory query=source.memory query) ∧
      evaluateHOLFiniteState ready afterFields=(some (.returned returned),inner) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite inner := by
  have fits : pointer.toNat+length.toNat<2^64 := by omega
  obtain ⟨answer,decoded,decodedPost,complete,decodedArena,decodedAbove,decodedDomain,decodedEndian,decodedCode,decodedHeap,itemCell,decodedOutput,decodedRun,decodedFrame⟩ :=
    body_decode_prefix source post pointer length cursor limit out pointerCell lengthCell outputCell arena fits installed returned normal
  have decodedInstalled : Input.OriginalCode.Installed decoded.code := by rw [decodedCode]; exact installed
  obtain ⟨header,payload,items,fieldsEntry,fieldsPost,extent,itemEq,lengthFour,recordRoom,fieldsView,fieldsHeap,fieldsDomain,fieldsEndian,fieldsCode,fieldsMemory,fieldsRun,fieldsFrame⟩ :=
    after_decode_fields decoded decodedPost pointer length heap cursor limit out cutoff answer itemCell complete decodedOutput decodedArena
      (decodedHeap.trans heapGlobal) heapBound before sizeBound aligned scratchBelow inputAbove output decodedInstalled returned decodedRun
  obtain ⟨a,b,c,d,itemsEq⟩ := List.length_eq_four.mp lengthFour
  subst items
  have fieldsInstalled : Input.OriginalCode.Installed fieldsEntry.code := by rw [fieldsCode]; exact decodedInstalled
  obtain ⟨ready,inner,results,view,above,domain,endian,codeEq,heapEq,tailRun,tailFrame⟩ :=
    fields_normal fieldsEntry fieldsPost heap (pointer+header) payload cursor limit out cutoff a b c d fieldsView fieldsInstalled returned fieldsRun
  refine ⟨header,payload,a,b,c,d,ready,inner,extent,recordRoom,results,view,heapEq.trans fieldsHeap,
    domain.trans (fieldsDomain.trans decodedDomain),endian.trans (fieldsEndian.trans decodedEndian),codeEq.trans (fieldsCode.trans decodedCode),?_,tailRun,
    decodedFrame.trans (fieldsFrame.trans tailFrame)⟩
  intro query beyond outside
  exact (above query beyond).trans ((fieldsMemory query beyond outside).trans (decodedAbove query beyond))

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.body_fields
