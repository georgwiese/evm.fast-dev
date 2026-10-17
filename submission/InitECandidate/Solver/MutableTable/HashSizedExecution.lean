import InitECandidate.Solver.MutableTable.HashSized

namespace InitECandidate.Solver.MutableTable.HashSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def initialized (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "h" 14695981039346656037#64) "w" 0#64
def closed (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "h" (restore (WitnessRadix.QueryBranch.bind source "h" 14695981039346656037#64) "w" (emptyLocalsHOLFinite (initialized source)))

theorem initialized_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notH : ofString "h" ≠ ofString name) (notW : ofString "w" ≠ ofString name) :
    (initialized source).locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "w" name _ notW).trans (bind_lookup_other _ "h" name _ notH)

theorem initialized_h (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (initialized source).locals.lookup (ofString "h") = some (.val (.word 14695981039346656037#64)) :=
  (bind_lookup_other _ "w" "h" _ (by decide)).trans (bind_lookup_same _ _ _)

theorem initialized_w (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (initialized source).locals.lookup (ofString "w") = some (.val (.word 0#64)) := bind_lookup_same _ _ _

/-- Scalar scope composition, instantiated below with actual checked cores. -/
theorem close_core (source : PanSemStateFiniteExact 64 Guest.HostMemory) (digest : BitVec 64)
    (core : evaluateHOLFiniteState (initialized source) Hash.afterLocals =
      (some (.returned (.val (.word digest))), emptyLocalsHOLFinite (initialized source))) :
    evaluateHOLFiniteState source Hash.body = (some (.returned (.val (.word digest))), closed source) := by
  let hs := WitnessRadix.QueryBranch.bind source "h" 14695981039346656037#64
  have wScope := Input.ScalarScope.declare_execute hs _ "w" (.const 0#64) 0#64 Hash.afterLocals _ rfl core
  rw [Hash.body_shape]
  exact Input.ScalarScope.declare_execute source _ "h" (.const 14695981039346656037#64) 14695981039346656037#64 _ _ rfl wScope

theorem canonical (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    emptyLocalsHOLFinite (closed source) = emptyLocalsHOLFinite source := rfl

/-- Complete actual aligned20/52-byte hash body, including both declarations
and lexical scopes. No body clocks, memory writes or FFI effects occur. -/
theorem aligned_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (words : Fin 6 → BitVec 64) (bytes : Fin 4 → UInt8)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))))
    (aligned : pointer &&& 7#64 = 0#64)
    (mapped : ∀ i : Fin 6, i.val < wordCount kind → source.memaddrs (pointer + BitVec.ofNat 64 (8 * i.val)))
    (stored : ∀ i : Fin 6, i.val < wordCount kind → source.memory (pointer + BitVec.ofNat 64 (8 * i.val)) = .word (words i))
    (loaded : ∀ i : Fin 4, @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer + BitVec.ofNat 64 (8 * wordCount kind + i.val)) = some (bytes i)) :
    evaluateHOLFiniteState source Hash.body =
      (some (.returned (.val (.word (resultWord kind words bytes)))), closed source) := by
  apply close_core
  exact aligned_core (initialized source) kind pointer words bytes
    ((initialized_other source "p" (by decide) (by decide)).trans p)
    ((initialized_other source "key_len" (by decide) (by decide)).trans length)
    (initialized_h source) (initialized_w source) aligned mapped stored loaded

/-- Complete actual unaligned20/52-byte hash body from its input bytes. -/
theorem unaligned_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (bytes : Fin 52 → UInt8)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))))
    (unaligned : pointer &&& 7#64 ≠ 0#64)
    (loaded : ∀ i : Fin 52, i.val < keySize kind → @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer + BitVec.ofNat 64 i.val) = some (bytes i)) :
    evaluateHOLFiniteState source Hash.body =
      (some (.returned (.val (.word (resultWord kind (packedWords bytes) (tailBytes kind bytes))))), closed source) := by
  apply close_core
  exact unaligned_core (initialized source) kind pointer bytes
    ((initialized_other source "p" (by decide) (by decide)).trans p)
    ((initialized_other source "key_len" (by decide) (by decide)).trans length)
    (initialized_h source) (initialized_w source) unaligned loaded

end InitECandidate.Solver.MutableTable.HashSized

#print axioms InitECandidate.Solver.MutableTable.HashSized.initialized_other
#print axioms InitECandidate.Solver.MutableTable.HashSized.initialized_h
#print axioms InitECandidate.Solver.MutableTable.HashSized.initialized_w
#print axioms InitECandidate.Solver.MutableTable.HashSized.close_core
#print axioms InitECandidate.Solver.MutableTable.HashSized.canonical
#print axioms InitECandidate.Solver.MutableTable.HashSized.aligned_execute
#print axioms InitECandidate.Solver.MutableTable.HashSized.unaligned_execute
