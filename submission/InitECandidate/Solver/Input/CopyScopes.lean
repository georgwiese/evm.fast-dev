import InitECandidate.Solver.Input.CopyReturn

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def copySuffix : ProgHOL 64 := .dec (ofString "i") .one (.const 0#64)
  (.dec (ofString "w") .one (.const 0#64) (.seq copyLoop returnPair))
def copyEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "i" 0#64) "w" 0#64

/-- Actual local declarations and their restoration around the complete copy
and return; the stated resource cost includes every loop iteration. -/
theorem copy_scopes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (length : Nat) (bounded : length≤Guest.maxInputBytes)
    (lower : 2701131776≤pointer.toNat) (upper : pointer.toNat+length+8≤33806089496)
    (aligned : pointer.toNat%8=0)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (oracleEq : source.ffi.oracle=InitE.sourceOracle) (host : source.ffi.ffiState=Guest.guestHostMemory input)
    (ordinary : source.memaddrs=InitE.ordinaryDomain) (shared : source.shMemaddrs=InitE.sharedDomain)
    (enough : copyRounds length≤source.clock) :
    ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source copySuffix=(some (.returned (pair pointer length)),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite (walk (copyEntry source) pointer 0 (copyRounds length)) := by
  let entered:=copyEntry source
  have pointerEntered : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
    dsimp only [entered,copyEntry]
    rw [bind_lookup_other _ "w" "p" _ (by decide),bind_lookup_other _ "i" "p" _ (by decide)]
    exact pointerLocal
  have lengthEntered : entered.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) := by
    dsimp only [entered,copyEntry]
    rw [bind_lookup_other _ "w" "len" _ (by decide),bind_lookup_other _ "i" "len" _ (by decide)]
    exact lengthLocal
  have indexEntered : entered.locals.lookup (ofString "i")=some (.val (.word 0#64)) := by
    dsimp only [entered,copyEntry]
    rw [bind_lookup_other _ "w" "i" _ (by decide)]
    exact bind_lookup_same _ _ _
  have run:=copy_return entered input pointer 0#64 length bounded lower upper aligned pointerEntered indexEntered lengthEntered
    (bind_lookup_same _ _ _) oracleEq host ordinary shared enough
  have setup : WitnessRadix.BuildEntry.Initializes source [("i",.const 0#64),("w",.const 0#64)] entered
      (fun output=>restore source "i" (restore (WitnessRadix.QueryBranch.bind source "i" 0#64) "w" output)) :=
    .step 0#64 rfl (.step 0#64 rfl (.done _))
  have scopeRun:=WitnessRadix.BuildEntry.declarations_execute setup (.seq copyLoop returnPair)
  change evaluateHOLFiniteState source copySuffix=_ at scopeRun
  rw [run] at scopeRun
  exact ⟨_,scopeRun,rfl⟩

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_scopes
