import InitECandidate.Solver.Input.Requests.CountLocals
import InitECandidate.Solver.Input.WorkspaceWord
import InitECandidate.Solver.PanDeclarations

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

def offsetBindings : List (String × ExpHOL 64) :=
  [("o0", loadOffset 0), ("o1", loadOffset 1), ("o2", loadOffset 2), ("o3", loadOffset 3), ("o4", loadOffset 4)]
def loadedOffsets (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (start : Nat) :=
  bind (bind (bind (bind (bind source "o0" (offsetWord input start 0)) "o1" (offsetWord input start 1))
    "o2" (offsetWord input start 2)) "o3" (offsetWord input start 3)) "o4" (offsetWord input start 4)

/-- The five real readonly workspace declarations, after allocation has
already occurred. No allocator, clock or future-return premise is required. -/
theorem offset_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (array : BitVec 64) (start : Nat)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (cells : ∀ position < 5, source.memory (byteAddress array (8 * position)) = .word (offsetWord input start position))
    (domain : source.memaddrs = InitE.ordinaryDomain) (aligned : array.toNat % 8 = 0) (arena : Arena array 40) :
    ∃ restoreStack, BuildEntry.Initializes source offsetBindings (loadedOffsets source input start) restoreStack := by
  have read (current : PanSemStateFiniteExact 64 Guest.HostMemory) (position : Nat) (small : position < 5)
      (global : current.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
      (memory : current.memory = source.memory) (addresses : current.memaddrs = source.memaddrs) :
      eval current (loadOffset position) = some (.val (.word (offsetWord input start position))) := by
    have mapped := word_mapped current array 40 (8 * position) (addresses.trans domain) arena (by omega) aligned (by omega)
    have cell : current.memory (array + BitVec.ofNat 64 (8 * position)) = .word (offsetWord input start position) := by
      rw [memory]
      exact cells position small
    by_cases zero : position = 0
    · subst position
      have mappedZero : current.memaddrs array := by simpa [byteAddress] using mapped
      have cellZero : current.memory array = .word (offsetWord input start 0) := by simpa using cell
      simp [loadOffset, eval, Header.offsets, evalHOLExact, toExact, global, isWfShapeExactHOL, memLoadHOLExact, mappedZero, cellZero]
    · rw [loadOffset, if_neg zero]
      exact Request.word_read current array (offsetWord input start position) (8 * position) global mapped cell
  let first := bind source "o0" (offsetWord input start 0)
  let second := bind first "o1" (offsetWord input start 1)
  let third := bind second "o2" (offsetWord input start 2)
  let fourth := bind third "o3" (offsetWord input start 3)
  have r0 := read source 0 (by decide) offsets rfl rfl
  have r1 := read first 1 (by decide) offsets rfl rfl
  have r2 := read second 2 (by decide) offsets rfl rfl
  have r3 := read third 3 (by decide) offsets rfl rfl
  have r4 := read fourth 4 (by decide) offsets rfl rfl
  refine ⟨fun output => restore source "o0" (restore first "o1" (restore second "o2" (restore third "o3" (restore fourth "o4" output)))), ?_⟩
  exact .step _ r0 (.step _ r1 (.step _ r2 (.step _ r3 (.step _ r4 (.done _)))))

/-- The real declarations install all five validated offsets and keep the
callee pointer/length and allocated record binding needed by each count call. -/
theorem loaded_offsets_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor total : BitVec 64) (start : Nat)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "len") = some (.val (.word total)))
    (rq : source.locals.lookup (ofString "rq") = some (.val (.word cursor))) :
    CountLocals (loadedOffsets source input start) (offsetWord input start) total pointer cursor := by
  have kept (name : String) (a : ofString "o0" ≠ ofString name) (b : ofString "o1" ≠ ofString name)
      (c : ofString "o2" ≠ ofString name) (d : ofString "o3" ≠ ofString name) (e : ofString "o4" ≠ ofString name) :
      (loadedOffsets source input start).locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    simp [loadedOffsets, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, a, b, c, d, e]
  refine ⟨?_, (kept "len" (by decide) (by decide) (by decide) (by decide) (by decide)).trans n,
    (kept "p" (by decide) (by decide) (by decide) (by decide) (by decide)).trans p,
    (kept "rq" (by decide) (by decide) (by decide) (by decide) (by decide)).trans rq⟩
  intro index small
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;>
    simp [loadedOffsets, offsetName, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.offset_locals
#print axioms InitECandidate.Solver.Input.Requests.loaded_offsets_model
