import InitECandidate.Solver.MutableTable.HashUnaligned32
import InitECandidate.Solver.MutableTable.HashWordBytes

namespace InitECandidate.Solver.MutableTable.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def keyBytes (key : WitnessRadix.ByteKeys.Key) : Fin 32→UInt8:=fun i=>WitnessRadix.Memeq32.toUInt8 (key i)
def keyHash (key : WitnessRadix.ByteKeys.Key) : BitVec 64:=resultWord (packedWords (keyBytes key))

theorem packed_roundtrip (words : Fin 4→BitVec 64) : packedWords (keyBytes (WitnessRadix.WordKeys.key words))=words := by
  funext block
  rcases block with ⟨i,inside⟩
  have positions : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
  rcases positions with rfl|rfl|rfl|rfl
  all_goals simp only [packedWords,chunkByte,keyBytes,WitnessRadix.Memeq32.widened_byte,WitnessRadix.WordKeys.key]
  all_goals exact rebuild_word _

theorem unaligned32_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : Fin 32→UInt8)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (unaligned : pointer &&& 7#64≠0#64)
    (loaded : ∀ index : Fin 32,@panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be
      (pointer+BitVec.ofNat 64 index.val)=some (bytes index)) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word (resultWord (packedWords bytes))))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  let hs:=bind source "h" 14695981039346656037#64
  let ws:=bind hs "w" 0#64
  have pW : ws.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (bind_lookup_other _ "w" "p" _ (by decide)).trans ((bind_lookup_other _ "h" "p" _ (by decide)).trans p)
  have lengthW : ws.locals.lookup (ofString "key_len")=some (.val (.word 32#64)):=
    (bind_lookup_other _ "w" "key_len" _ (by decide)).trans ((bind_lookup_other _ "h" "key_len" _ (by decide)).trans length)
  have hW : ws.locals.lookup (ofString "h")=some (.val (.word 14695981039346656037#64)):=
    (bind_lookup_other _ "w" "h" _ (by decide)).trans (bind_lookup_same _ _ _)
  have run:=unaligned32_core ws pointer bytes pW lengthW hW (bind_lookup_same _ _ _) unaligned loaded
  have wScope:=Input.ScalarScope.declare_execute hs _ "w" (.const 0#64) 0#64 afterLocals _ rfl run
  let target:=restore source "h" (restore hs "w" (emptyLocalsHOLFinite ws))
  refine ⟨target,?_,rfl⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "h" (.const 14695981039346656037#64) 14695981039346656037#64 _ _ rfl wScope

/-- Uniform actual32-byte hash, both alignment paths, from the byte-level key.
The pure result depends only on those bytes; no hash-distribution assumption. -/
theorem memory_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (key : WitnessRadix.ByteKeys.Key)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (view : WitnessRadix.MemoryBytes.ByteView source pointer key) (fits : pointer.toNat+32<2^64) (little : source.be=false) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word (keyHash key)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  by_cases aligned : pointer &&& 7#64=0#64
  · have alignNumber : pointer.toNat%8=0 := by rw [← WitnessRadix.WordBits.mask7 pointer,aligned];rfl
    let words:=WitnessRadix.MemoryBytes.wordsOf source pointer
    have cells:=WitnessRadix.MemoryBytes.byteView_words source pointer key alignNumber fits view
    have represented:=WitnessRadix.MemoryBytes.wordView_bytes source pointer words alignNumber fits little cells
    have keyEq:=WitnessRadix.MemoryBytes.byteView_unique source pointer (WitnessRadix.WordKeys.key words) key represented view
    obtain ⟨target,run,frame⟩:=aligned32_execute source pointer words p length aligned cells.mapped cells.stored
    have resultEq : keyHash key=resultWord words := by rw [keyHash,← keyEq,packed_roundtrip]
    exact ⟨target,by rw [resultEq];exact run,frame⟩
  · exact unaligned32_execute source pointer (keyBytes key) p length aligned view

/-- Real hash caller for every alignment, with one call clock and canonical
caller locals. The return value is the byte-level keyHash. -/
theorem memory_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (key : WitnessRadix.ByteKeys.Key)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word pointer),.val (.word 32#64)])
    (code : source.code.lookup (ofString "htab_hash")=some (formals,body,.one))
    (view : WitnessRadix.MemoryBytes.ByteView source pointer key) (fits : pointer.toNat+32<2^64) (little : source.be=false)
    (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_hash") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (keyHash key)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,p,len⟩:=environment source.code.lookup pointer code
  let entry:=callEntryStateHOLFinite source callee
  have entryView:=WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ view
  obtain ⟨target,run,frame⟩:=memory_execute entry pointer key p len entryView fits little
  have actual:=Input.CallNormal.pure_return_execute source target name (ofString "htab_hash") expressions _ body continuation callee (keyHash key) 0 args called enough run frame
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.MutableTable.Hash

#print axioms InitECandidate.Solver.MutableTable.Hash.packed_roundtrip
#print axioms InitECandidate.Solver.MutableTable.Hash.unaligned32_execute
#print axioms InitECandidate.Solver.MutableTable.Hash.memory_execute

#print axioms InitECandidate.Solver.MutableTable.Hash.memory_call
