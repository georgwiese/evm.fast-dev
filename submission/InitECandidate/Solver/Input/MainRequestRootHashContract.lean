import InitECandidate.Solver.Input.MainRequestRootHashPrepared

namespace InitECandidate.Solver.Input.Main.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Main's literal unchanged request-root call at its actual prepared
startup/copy/decoded state, with every observed non-timeout failure retained. -/
theorem call_cost (input : Guest.InputBlob) (current post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (actual : RequestRootHashData.Prepared input current root counts)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (entered current root) call=(result,post)) (notTimeout : result≠some .timeOut) :
    (entered current root).clock-post.clock≤RequestRootHash.bodyPrice (RequestRootHashData.description input counts)+1 :=
  RequestRootHash.call_cost (RequestRootHashData.description input counts) current (entered current root) post inputPointer.toNat root.toNat (input.length%2^64)
    root (PersistentAlloc.rounded root 32#64) 2713714688#64 2713714880#64 2713715312#64 2713715408#64 actual.image actual.layout actual.workspace actual.frame actual.heap actual.geometry actual.output
    RequestRootHashData.separation (by decide) actual.before (some none) arguments actual.arguments result run notTimeout

/-- Actual normal main hashing restores the post-root-allocation heap and
retains all copied/decoded words below root for the constructor continuation. -/
theorem call_normal (input : Guest.InputBlob) (current post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (actual : RequestRootHashData.Prepared input current root counts)
    (run : evaluateHOLFiniteState (entered current root) call=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded root 32#64))) ∧ HashInput.Frame current post inputPointer.toNat root.toNat :=
  RequestRootHash.call_normal (RequestRootHashData.description input counts) current (entered current root) post inputPointer.toNat root.toNat (input.length%2^64)
    root (PersistentAlloc.rounded root 32#64) 2713714688#64 2713714880#64 2713715312#64 2713715408#64 actual.image actual.layout actual.workspace actual.frame actual.heap actual.geometry actual.output
    RequestRootHashData.separation (by decide) actual.before arguments actual.arguments run

theorem call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code call :=
  GlobalEffects.call_body key code (some none) (ofString "htr_new_payload_request") arguments RequestRootHash.formals RequestRootHash.body .one
    (RequestRootHash.original_code code installed) (RequestRootHash.globals key code installed different)

end InitECandidate.Solver.Input.Main.RequestHash
#print axioms InitECandidate.Solver.Input.Main.RequestHash.call_cost
#print axioms InitECandidate.Solver.Input.Main.RequestHash.call_normal
#print axioms InitECandidate.Solver.Input.Main.RequestHash.call_globals
