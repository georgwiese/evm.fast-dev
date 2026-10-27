import InitECandidate.Solver.Input.CopyObservedBytes
import InitECandidate.Solver.Input.BlobCurrentCost
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Invert the actual i/w lexical scopes, copy loop and tuple return. Every
access and returned byte view is derived from this real returning suffix. -/
theorem copy_tail_reached (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64) (length : Nat) (returned : ValueHOL 64)
    (bounded : length ≤ Guest.maxInputBytes) (fits : pointer.toNat + length + 8 < 2^64)
    (aligned : pointer.toNat % 8 = 0) (little : source.be = false)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (normal : evaluateHOLFiniteState source copyTail = (some (.returned returned), post)) :
    returned = .rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 length))] ∧
    InputBytes post input pointer length ∧ post.clock = source.clock - copyRounds length ∧
    post.globals = source.globals ∧ post.code = source.code ∧
    post.memaddrs = source.memaddrs ∧ post.shMemaddrs = source.shMemaddrs ∧
    post.ffi.ffiState = source.ffi.ffiState ∧ post.ffi.oracle = source.ffi.oracle ∧
    ∀ query, (∀ slot < copyRounds length, query ≠ pointer + BitVec.ofNat 64 (8 * slot)) →
      post.memory query = source.memory query := by
  let withI := bind source "i" 0#64
  let ready := bind withI "w" 0#64
  let finish : ProgHOL 64 := .return (.rstruct [localVar "p", localVar "len"])
  rw [copyTail] at normal
  obtain ⟨innerI, runI, postI⟩ := declaration_return_word source post "i" (.const 0#64) 0#64
    (.dec (ofString "w") .one (.const 0#64) (.seq copyLoop finish)) returned rfl normal
  obtain ⟨innerW, runW, postW⟩ := declaration_return_word withI innerI "w" (.const 0#64) 0#64
    (.seq copyLoop finish) returned rfl runI
  have summary := while_local_summary (ofString "len") copyCondition copyBody copy_body_local ready
  obtain ⟨copied, copyRun, returnRun⟩ := sequence_returned ready innerW copyLoop finish returned summary.2.1 runW
  have readyP : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) :=
    (bind_lookup_other withI "w" "p" 0#64 (by decide)).trans
      ((bind_lookup_other source "i" "p" 0#64 (by decide)).trans pointerLocal)
  have readyI : ready.locals.lookup (ofString "i") = some (.val (.word 0#64)) :=
    (bind_lookup_other withI "w" "i" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
  have readyL : ready.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other withI "w" "len" 0#64 (by decide)).trans
      ((bind_lookup_other source "i" "len" 0#64 (by decide)).trans lengthLocal)
  have facts := copy_bytes_reached ready copied input pointer 0#64 length bounded fits aligned little
    readyP readyI readyL (bind_lookup_same _ _ _) oracleEq host copyRun
  have fit := copyRounds_fit length bounded
  obtain ⟨same, observed⟩ := copy_loop_reached ready copied pointer 0#64 0 length (copyRounds length)
    (by omega) (by omega) (by omega) readyP readyI readyL (bind_lookup_same _ _ _) oracleEq copyRun
  have copiedP : copied.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    rw [same, walk_other ready pointer 0 (copyRounds length) _ (by decide) (by decide)]
    exact readyP
  have copiedL : copied.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) := by
    rw [same, walk_other ready pointer 0 (copyRounds length) _ (by decide) (by decide)]
    exact readyL
  have returning := return_normal copied innerW _ returned returnRun
  have read : eval copied (.rstruct [localVar "p", localVar "len"]) =
      some (.rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 length))]) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, copiedP, copiedL]
  have valueEq := Option.some.inj (returning.1.symm.trans read)
  have postEq : post = restore source "i" (restore withI "w" (emptyLocalsHOLFinite copied)) := by
    rw [postI, postW, returning.2]
  rw [postEq]
  exact ⟨valueEq, facts⟩

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_tail_reached
