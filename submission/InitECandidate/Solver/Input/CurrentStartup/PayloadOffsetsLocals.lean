import InitECandidate.Solver.Input.CurrentStartup.PayloadCut
import InitECandidate.Solver.Input.PayloadOffsetDeclarations

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadOffsetsLocals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual four read-only declarations are identified using the copied
image they retain. Their reads and p binding are taken from this same real
trace; no future offset load or validated offset values are assumed. -/
theorem declarations {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (input : Guest.InputBlob) (pointer : BitVec 64) (extent : 602 ≤ input.length % 2^64)
    (image : Blob.HeapInput target input pointer)
    (p : target.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))))
    (actual : CallPrefix.Execution source (PayloadCut.actions.drop 3) target) :
    target.locals.lookup (ofString "o_extra") = some (.val (.word (Payload.offsetWords input 0))) ∧
    target.locals.lookup (ofString "o_txs") = some (.val (.word (Payload.offsetWords input 1))) ∧
    target.locals.lookup (ofString "o_wd") = some (.val (.word (Payload.offsetWords input 2))) ∧
    target.locals.lookup (ofString "o_bal") = some (.val (.word (Payload.offsetWords input 3))) := by
  have n0 : ofString "o_extra" ≠ ofString "p" := by decide
  have n1 : ofString "o_txs" ≠ ofString "p" := by decide
  have n2 : ofString "o_wd" ≠ ofString "p" := by decide
  have n3 : ofString "o_bal" ≠ ofString "p" := by decide
  cases actual with
  | step extra rest =>
    cases rest with
    | step txs rest =>
      cases rest with
      | step wd rest =>
        cases rest with
        | step bal done =>
          cases done
          cases bal with
          | declare _ _ _ v3 r3 c3 =>
            cases wd with
            | declare _ _ _ v2 r2 c2 =>
              cases txs with
              | declare _ _ _ v1 r1 c1 =>
                cases extra with
                | declare _ _ _ v0 r0 c0 =>
                  have baseP : source.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))) := by
                    simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, n0, n1, n2, n3] using p
                  have baseImage : Blob.HeapInput source input pointer := image
                  have expected0 := Payload.payload_offset_read source input pointer [436] 498 baseImage (by omega) baseP rfl
                  have same0 := Option.some.inj (r0.symm.trans expected0)
                  subst v0
                  let first := setVarHOLFinite (ofString "o_extra") (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 498)))) source
                  have image1 : Blob.HeapInput first input pointer := baseImage
                  have p1 : first.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))) := by
                    simpa [first, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, n0] using baseP
                  have expected1 := Payload.payload_offset_read first input pointer [504] 566 image1 (by omega) p1 rfl
                  have same1 := Option.some.inj (r1.symm.trans expected1)
                  subst v1
                  let second := setVarHOLFinite (ofString "o_txs") (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)))) first
                  have image2 : Blob.HeapInput second input pointer := baseImage
                  have p2 : second.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))) := by
                    simpa [second, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, n1] using p1
                  have expected2 := Payload.payload_offset_read second input pointer [508] 570 image2 (by omega) p2 rfl
                  have same2 := Option.some.inj (r2.symm.trans expected2)
                  subst v2
                  let third := setVarHOLFinite (ofString "o_wd") (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 570)))) second
                  have image3 : Blob.HeapInput third input pointer := baseImage
                  have p3 : third.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))) := by
                    simpa [third, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, n2] using p2
                  have expected3 := Payload.payload_offset_read third input pointer [528] 590 image3 (by omega) p3 rfl
                  have same3 := Option.some.inj (r3.symm.trans expected3)
                  subst v3
                  simp [Payload.offsetWords, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                    show ofString "o_bal" ≠ ofString "o_extra" from by decide,
                    show ofString "o_wd" ≠ ofString "o_extra" from by decide,
                    show ofString "o_txs" ≠ ofString "o_extra" from by decide,
                    show ofString "o_bal" ≠ ofString "o_txs" from by decide,
                    show ofString "o_wd" ≠ ofString "o_txs" from by decide,
                    show ofString "o_bal" ≠ ofString "o_wd" from by decide]

theorem reached {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (input : Guest.InputBlob) (pointer : BitVec 64) (extent : 602 ≤ input.length % 2^64)
    (image : Blob.HeapInput target input pointer)
    (p : target.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))))
    (actual : CallPrefix.Execution source PayloadCut.actions target) :
    target.locals.lookup (ofString "o_extra") = some (.val (.word (Payload.offsetWords input 0))) ∧
    target.locals.lookup (ofString "o_txs") = some (.val (.word (Payload.offsetWords input 1))) ∧
    target.locals.lookup (ofString "o_wd") = some (.val (.word (Payload.offsetWords input 2))) ∧
    target.locals.lookup (ofString "o_bal") = some (.val (.word (Payload.offsetWords input 3))) := by
  obtain ⟨header, before, actual⟩ := actual.split (PayloadCut.actions.take 3) (PayloadCut.actions.drop 3)
  exact declarations input pointer extent image p actual

end InitECandidate.Solver.Input.CurrentStartup.PayloadOffsetsLocals

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadOffsetsLocals.declarations
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadOffsetsLocals.reached
