import InitECandidate.Solver.Input.Witness.PrefixNormal

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def prefixActions : List Action := [.declare "wp" witnessPointer,.declare "wlen" witnessLength]
def restorePrefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) := restore source "wp" (restore (pointerPrepared source pointer offset) "wlen" target)

theorem prefix_shape : prefixBody = program prefixActions (.seq shortGuard offsetBody) := by
  rw [offset_shapes.1]
  rfl

/-- Both real witness declarations, before any length/offset/list guard.
No clock or future helper outcome is required. -/
theorem prefix_setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (offset : Nat) (heap : Blob.HeapInput source input pointer)
    (extent : 2 ≤ input.length % 2^64) (offsetUpper : offset ≤ input.length % 2^64 - 2)
    (p : source.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64))))
    (n : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))))
    (o : source.locals.lookup (ofString "o_wit") = some (.val (.word (BitVec.ofNat 64 offset)))) :
    Executes source prefixActions (prefixPrepared source input pointer offset) (restorePrefix source pointer offset) ∧
      Blob.HeapInput (prefixPrepared source input pointer offset) input pointer ∧
      (prefixPrepared source input pointer offset).locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 (2+offset)))) ∧
      (prefixPrepared source input pointer offset).locals.lookup (ofString "wlen") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2 - offset)))) := by
  classical
  have bytesSmall : input.length%2^64<2^64:=Nat.mod_lt _ (by decide)
  have pointerRead : eval source witnessPointer=some (.val (.word (pointer+BitVec.ofNat 64 (2+offset)))) := by
    simp [eval,witnessPointer,localVar,evalHOLExact,evalListHOLExact,toExact,p,o,valueIsWord,valueWord,
      wordOpHOL,wordOp,BitVec.add_assoc,BitVec.ofNat_add]
  have n' : (pointerPrepared source pointer offset).locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64-2)))):=
    (bind_lookup_other source "wp" "len" _ (by decide)).trans n
  have o' : (pointerPrepared source pointer offset).locals.lookup (ofString "o_wit")=some (.val (.word (BitVec.ofNat 64 offset))):=
    (bind_lookup_other source "wp" "o_wit" _ (by decide)).trans o
  have difference : BitVec.ofNat 64 (input.length%2^64-2)-BitVec.ofNat 64 offset=
      BitVec.ofNat 64 (input.length%2^64-2-offset):=BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) offsetUpper
  have lengthRead : eval (pointerPrepared source pointer offset) witnessLength=
      some (.val (.word (BitVec.ofNat 64 (input.length%2^64-2-offset)))) := by
    simp [eval,witnessLength,localVar,evalHOLExact,evalListHOLExact,toExact,n',o',valueIsWord,valueWord,wordOpHOL,wordOp]
    exact difference
  have setup : Executes source [.declare "wp" witnessPointer,.declare "wlen" witnessLength]
      (prefixPrepared source input pointer offset) (fun target=>restore source "wp" (restore (pointerPrepared source pointer offset) "wlen" target)) := by
    refine Executes.declare (restoreRest:=fun target=>restore (pointerPrepared source pointer offset) "wlen" target) _ pointerRead ?_
    exact Executes.declare (restoreRest:=id) _ lengthRead (Executes.done _)
  exact ⟨setup,Blob.HeapInput.of_fields source (prefixPrepared source input pointer offset) input pointer rfl rfl rfl heap,
    (bind_lookup_other (pointerPrepared source pointer offset) "wlen" "wp" _ (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _⟩

theorem prefix_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64) (offset : Nat) :
    emptyLocalsHOLFinite (prefixPrepared source input pointer offset) = emptyLocalsHOLFinite source := rfl

theorem restore_prefix_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) :
    emptyLocalsHOLFinite (restorePrefix source pointer offset target) = emptyLocalsHOLFinite target := rfl

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.prefix_shape
#print axioms InitECandidate.Solver.Input.Witness.prefix_setup
#print axioms InitECandidate.Solver.Input.Witness.prefix_frame
#print axioms InitECandidate.Solver.Input.Witness.restore_prefix_frame
