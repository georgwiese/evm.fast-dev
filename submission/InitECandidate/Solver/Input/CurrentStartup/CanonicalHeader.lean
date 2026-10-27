import InitECandidate.Solver.Input.CurrentStartup.SeparatedInput
import InitECandidate.Solver.Input.HeaderEntryNormal
import InitECandidate.Solver.Input.HeaderAfterTrace
import InitECandidate.Solver.Input.HeaderPassingEntry
import InitECandidate.Solver.Input.OffsetsTrace
import InitECandidate.Solver.Input.HeaderAfterNormal
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.CurrentStartup.CanonicalHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem offset_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ssz_check_offsets") = some (Offsets.formals, Offsets.body, .one) := by
  simpa only [Code.name, Code.body, Code.formals, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_ssz_check_offsets, Offsets.formals, Offsets.body,
    shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
    using Code.installed code installed .ssz_check_offsets

theorem fail_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one) := by
  simpa only [Code.name, Code.body, Code.formals, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_ssz_fail, SszFail.formals, SszFail.body,
    shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
    using Code.installed code installed .ssz_fail

/-- The actual returning decoder establishes the schema and first canonical
container offset. Four clock units are added using the proved non-timeout
clock-shift theorem; funding is derived, not an extra caller premise. The two
real workspace stores preserve copied input using the actual geometry. -/
theorem first_offset (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (initial : HostState input source)
    (bytes : Blob.InputBytes source input pointer (input.length % 2^64))
    (pCell : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lenCell : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64)))))
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (lower : 2701134640 ≤ pointer.toNat) (aligned : pointer.toNat % 8 = 0)
    (room : pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016)
    (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (Code.body .decode_stateless_input) = (some (.returned value), post)) :
    18 ≤ input.length % 2^64 ∧ Guest.GasLimit.byte input 0 = 21 ∧ Guest.GasLimit.byte input 1 = 1 ∧
      Guest.GasLimit.le32 input 2 = 16 ∧ 16 ≤ Guest.GasLimit.le32 input 6 ∧
      Guest.GasLimit.le32 input 6 ≤ input.length % 2^64 - 2 := by
  let funded : PanSemStateFiniteExact 64 Guest.HostMemory := {source with clock := source.clock + 4}
  have run := panPropsEvaluateAddClockEq (Code.body .decode_stateless_input) source (some (.returned value)) post 4 ⟨actual, by simp⟩
  have entryRun : evaluateHOLFiniteState funded Header.body = (some (.returned value), {post with clock := post.clock + 4}) := run
  have image : Blob.HeapInput funded input pointer := bytes
  have failed := fail_code source.code initial.arena.code
  have shape : source.eshapes.lookup (ofString "SszErr") = some .one := initial.shapes .SszErr
  obtain ⟨extent, tag, version, after⟩ := Header.normal_entry funded _ input pointer image pCell lenCell failed shape (by dsimp [funded]; omega) value entryRun
  let entered := Header.shifted funded pointer (input.length % 2^64)
  have enteredImage : Blob.HeapInput entered input pointer := image
  have enteredP : entered.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64))) :=
    (bind_lookup_other _ "len" "p" _ (by decide)).trans (bind_lookup_same _ _ _)
  have enteredLen : entered.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) := bind_lookup_same _ _ _
  obtain ⟨first, secondLower, secondUpper, next, paid, bound, nextEq, retained, remaining⟩ :=
    Header.after_normal entered _ input pointer 2701132528#64 (BitVec.ofNat 64 (input.length % 2^64 - 2)) enteredImage
      (by omega) enteredP offsets enteredLen initial.arena.domain aligned (by decide) (by omega)
      (by decide) (by change 2701132528 + 16 ≤ pointer.toNat; omega)
      (offset_code source.code initial.arena.code) failed shape (by dsimp [entered, Header.shifted, WitnessRadix.QueryBranch.bind, setVarHOLFinite, funded]; omega) value after
  have small : input.length % 2^64 - 2 < 2^64 := by have := Nat.mod_lt input.length (show 0 < 2^64 by decide); omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at secondUpper
  exact ⟨extent, tag, version, first, secondLower, secondUpper⟩

/-- The real unpadded decoder run reaches the first validated-container
continuation with its copied bytes intact and its actual prefix cost funded. -/
theorem outer_reached (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (initial : HostState input source)
    (bytes : Blob.InputBytes source input pointer (input.length % 2^64))
    (pCell : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lenCell : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64)))))
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (lower : 2701134640 ≤ pointer.toNat) (aligned : pointer.toNat % 8 = 0)
    (room : pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016)
    (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (Code.body .decode_stateless_input) = (some (.returned value), post)) :
    ∃ next paid, paid ≤ 4 ∧ paid ≤ source.clock ∧
      next = {Header.pairState (Header.shifted source pointer (input.length % 2^64)) input 2701132528#64 with clock := source.clock - paid} ∧
      Blob.HeapInput next input pointer ∧
      evaluateHOLFiniteState next Header.continuation = (some (.returned value), post) := by
  obtain ⟨extent, tag, version, first, secondLower, secondUpper⟩ :=
    first_offset input source post pointer initial bytes pCell lenCell offsets lower aligned room value actual
  have image : Blob.HeapInput source input pointer := bytes
  let entered := Header.shifted source pointer (input.length % 2^64)
  have passing := Header.passing_entry source input pointer image pCell lenCell extent tag version
  have after : evaluateHOLFiniteState entered Header.afterHeader = (some (.returned value), post) := passing.symm.trans actual
  have enteredP : entered.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64))) :=
    (bind_lookup_other _ "len" "p" _ (by decide)).trans (bind_lookup_same _ _ _)
  have enteredLen : entered.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) := bind_lookup_same _ _ _
  exact Header.after_trace entered post input pointer 2701132528#64 (BitVec.ofNat 64 (input.length % 2^64 - 2))
    image (by omega) enteredP offsets enteredLen initial.arena.domain aligned (by decide) (by omega)
    (by decide) (by change 2701132528 + 16 ≤ pointer.toNat; omega)
    (offset_code source.code initial.arena.code) (fail_code source.code initial.arena.code) (initial.shapes .SszErr) value after

/-- Apply the canonical-header result to the actual whole-main input cut. -/
theorem separated_first (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word) :
    18 ≤ input.length % 2^64 ∧ Guest.GasLimit.byte input 0 = 21 ∧ Guest.GasLimit.byte input 1 = 1 ∧
      Guest.GasLimit.le32 input 2 = 16 ∧ 16 ≤ Guest.GasLimit.le32 input 6 ∧
      Guest.GasLimit.le32 input 6 ≤ input.length % 2^64 - 2 := by
  obtain ⟨source, target, pointer, lengthBound, initial, heap, bytes, pCell, lenCell, offsets, lower, aligned, room, separation, frontier, returned⟩ := actual
  exact first_offset input source target pointer initial bytes pCell lenCell offsets lower aligned room (.val (.word word)) returned

end InitECandidate.Solver.Input.CurrentStartup.CanonicalHeader

#print axioms InitECandidate.Solver.Input.CurrentStartup.CanonicalHeader.offset_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.CanonicalHeader.fail_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.CanonicalHeader.first_offset
#print axioms InitECandidate.Solver.Input.CurrentStartup.CanonicalHeader.separated_first

#print axioms InitECandidate.Solver.Input.CurrentStartup.CanonicalHeader.outer_reached
