import InitECandidate.Solver.Input.CurrentStartup.WitnessLoaded
import InitECandidate.Solver.Input.Witness.OffsetValues

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessSlices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual validated witness words derive a contained first list slice and
its literal node-list ABI, before any successful list decode is assumed. -/
theorem node_arguments (input : Guest.InputBlob) (source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) (value : ValueHOL 64)
    (data : WitnessLoaded.Result input source current post pointer statelessRecord record gasWord requestRecord payloadLength value) :
    let start := 2 + Guest.GasLimit.le32 input 6
    let middle := Witness.offsetNat input start 1
    start + 12 + (middle - 12) ≤ input.length % 2^64 ∧
      evalListHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address))
        (Witness.listArguments "w0" "w1" 9223372036854775807 1024) =
      some (BytesList.values (pointer + BitVec.ofNat 64 (start + 12)) (BitVec.ofNat 64 (middle - 12))
        9223372036854775807#64 1024#64) := by
  let start := 2 + Guest.GasLimit.le32 input 6
  let total := input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6
  have values := Witness.offset_values input start (BitVec.ofNat 64 total) data.first data.valid
  have totalNat : (BitVec.ofNat 64 total).toNat = total := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.mod_lt input.length (show 0 < 2^64 by decide); dsimp [total]; omega)]
  rw [totalNat] at values
  have inside : start + Witness.offsetNat input start 1 ≤ input.length % 2^64 := by
    have upper := data.context.request.outer.upper
    dsimp only [start, total] at values ⊢
    omega
  have firstSmall : Witness.offsetNat input start 0 < 2^64 := by
    rw [values.1]
    decide
  have args := Witness.list_arguments current pointer start (Witness.offsetNat input start 0) (Witness.offsetNat input start 1)
    9223372036854775807 1024 "w0" "w1" (by omega) firstSmall data.wp data.w0 data.w1
  rw [values.1] at args
  dsimp only [start] at values inside args ⊢
  exact ⟨by omega, args⟩

/-- Adjacent validated witness subranges give the literal list-call ABI and
input containment. The rule also applies to the final w2/wlen header slice. -/
theorem arguments_between (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (left right limit maximum : Nat) (leftName rightName : String)
    (extent : 2 ≤ input.length % 2^64)
    (outer : Guest.GasLimit.le32 input 6 ≤ input.length % 2^64 - 2)
    (ordered : left ≤ right) (rightBound : right ≤ input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6)
    (wp : source.locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 (2 + Guest.GasLimit.le32 input 6)))))
    (leftCell : source.locals.lookup (ofString leftName) = some (.val (.word (BitVec.ofNat 64 left))))
    (rightCell : source.locals.lookup (ofString rightName) = some (.val (.word (BitVec.ofNat 64 right)))) :
    2 + Guest.GasLimit.le32 input 6 + left + (right - left) ≤ input.length % 2^64 ∧
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
        (Witness.listArguments leftName rightName limit maximum) =
      some (BytesList.values (pointer + BitVec.ofNat 64 (2 + Guest.GasLimit.le32 input 6 + left))
        (BitVec.ofNat 64 (right - left)) (BitVec.ofNat 64 limit) (BitVec.ofNat 64 maximum)) := by
  have small : left < 2^64 := by
    have := Nat.mod_lt input.length (show 0 < 2^64 by decide)
    omega
  exact ⟨by omega, Witness.list_arguments source pointer (2 + Guest.GasLimit.le32 input 6) left right limit maximum
    leftName rightName ordered small wp leftCell rightCell⟩

end InitECandidate.Solver.Input.CurrentStartup.WitnessSlices

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessSlices.node_arguments

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessSlices.arguments_between
