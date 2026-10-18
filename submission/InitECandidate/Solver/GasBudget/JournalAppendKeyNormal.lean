import InitECandidate.Solver.GasBudget.JournalAppendKeyProgram
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) :=
  PersistentAlloc.nextState (bind source "klen" (BitVec.ofNat 64 (KeyHash.keySize kind))) "kc" cursor (cursor + stride kind)
def keyState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) (query : BitVec 64) :=
  CopyGeneral.callState (allocated source kind cursor) query (BitVec.ofNat 64 cursor) (KeyHash.keySize kind)
def keyPrice (kind : KeyHash.Kind) (cursor : Nat) (query : BitVec 64) : Nat :=
  CopyGeneral.cost query (BitVec.ofNat 64 cursor) (KeyHash.keySize kind) + 2
def restoreKeys (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (post : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "klen" (restore (bind source "klen" (BitVec.ofNat 64 (KeyHash.keySize kind))) "kc" post)

/-- Actual original append key prefix derives fresh allocation room and its
copy clock, exposing the canonical copied-key state and real continuation. -/
theorem key_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (keyProgram continuation) = (some (.returned returned), post)) :
    cursor + stride kind ≤ 33806089496 ∧ keyPrice kind cursor query ≤ source.clock ∧ keyPrice kind cursor query ≤ KeyHash.keySize kind + 2 ∧
      MemoryRegion.Valid ⟨cursor, stride kind⟩ ∧ ∃ finish,
        evaluateHOLFiniteState (keyState source kind cursor query) continuation = (some (.returned returned), finish) ∧
        post = restoreKeys source kind finish := by
  obtain ⟨declared, inner, read, shape, allocRun, outerFrame⟩ := Input.CallNormal.declaration_normal_entry source post "klen" .one lengthExpression _ returned normal
  have lengthRead := length_read source kind plan slots cursor floor table environment.domain tableLocal
  have same : declared = .val (.word (BitVec.ofNat 64 (KeyHash.keySize kind))) := Option.some.inj (read.symm.trans lengthRead)
  subst declared
  let withLength := bind source "klen" (BitVec.ofNat 64 (KeyHash.keySize kind))
  have round := key_rounding kind
  have nextAligned : (cursor + stride kind) % 8 = 0 := by
    rw [Nat.add_mod, table.aligned, round.2.2.1]
  have args : evalListHOLFinite withLength (h := fun address => Classical.propDecidable (withLength.memaddrs address)) [localVar "klen"] =
      some (PersistentAlloc.values (BitVec.ofNat 64 (KeyHash.keySize kind))) := by
    have binding : withLength.locals.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) := bind_lookup_same _ _ _
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, binding, PersistentAlloc.values]
  obtain ⟨requestRoom, nextBound, positive, finish, afterAlloc, innerFrame⟩ :=
    PersistentAlloc.call_normal_expected withLength inner "kc" [localVar "klen"] (.seq copyCall continuation) cursor (KeyHash.keySize kind) (cursor + stride kind)
      table.bounded (by have small := round.2.2.2; omega) (by omega) (by omega) nextAligned args environment.allocCode environment.trapCode table.heap returned allocRun
  have withLengthKey : withLength.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (bind_lookup_other _ "klen" "key" _ (by decide)).trans keyLocal
  let entry := allocated source kind cursor
  have entryKey : entry.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (bind_lookup_other _ "kc" "key" _ (by decide)).trans withLengthKey
  have entryLength : entry.locals.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) :=
    (bind_lookup_other _ "kc" "klen" _ (by decide)).trans (bind_lookup_same _ _ _)
  have copyArgs : evalListHOLFinite entry (h := fun address => Classical.propDecidable (entry.memaddrs address)) [localVar "kc", localVar "key", localVar "klen"] =
      some (CopyGeneral.values (BitVec.ofNat 64 cursor) query (KeyHash.keySize kind)) := by
    have keyCopy : entry.locals.lookup (ofString "kc") = some (.val (.word (BitVec.ofNat 64 cursor))) := bind_lookup_same _ _ _
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, keyCopy, entryKey, entryLength, CopyGeneral.values]
  have lower : 2701131776 ≤ cursor := by
    have poolLower := table.valid.lower .header
    have earlier := table.earlier .header
    omega
  have region : MemoryRegion.Valid ⟨cursor, stride kind⟩ := ⟨lower, nextBound, table.aligned⟩
  have destinationFits : (BitVec.ofNat 64 cursor).toNat + KeyHash.keySize kind < 2 ^ 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have bound := table.bounded; omega)]
    omega
  have copyMapped : CopyContext.Mapped entry query (BitVec.ofNat 64 cursor) (KeyHash.keySize kind) := by
    apply CopyMapped.of_regions entry query (BitVec.ofNat 64 cursor) (KeyHash.keySize kind) queryFits destinationFits queryMapped
    intro offset inside
    rw [show entry.memaddrs = InitE.ordinaryDomain from environment.domain]
    exact MemoryRegion.byte_mapped ⟨cursor, stride kind⟩ region offset (by change offset < stride kind; omega)
  have safe : Input.LocalPrefix (ofString "klen") copyCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨copied, copyRun, tailRun, saved⟩ := safe.normal_continue entry finish continuation returned afterAlloc
  obtain ⟨copyFunded, copyBound, copiedEq⟩ := CopyGeneral.call_normal entry copied _ query (BitVec.ofNat 64 cursor) (KeyHash.keySize kind) copyArgs environment.copyCode copyMapped round.2.2.2 copyRun
  change copied = keyState source kind cursor query at copiedEq
  rw [copiedEq] at tailRun
  change CopyGeneral.cost query (BitVec.ofNat 64 cursor) (KeyHash.keySize kind) + 1 ≤ source.clock - 1 at copyFunded
  refine ⟨nextBound, by dsimp only [keyPrice]; omega, by dsimp only [keyPrice]; omega, region, finish, tailRun, ?_⟩
  rw [outerFrame, innerFrame]
  rfl

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.key_normal
