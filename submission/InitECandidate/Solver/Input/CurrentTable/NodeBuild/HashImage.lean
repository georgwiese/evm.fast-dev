import InitECandidate.Solver.Input.CurrentTable.ImageLowerFrame
import InitECandidate.Solver.CurrentKeccak.Call
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A genuine witness hash writes only its three earlier buffers. Every
physical cell and byte key of the later Patricia image is therefore retained. -/
theorem hash_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer out stp pad : BitVec 64) (length next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (CurrentKeccak.Hash.values pointer out length))
    (inputArena : AllocatedBytes.Arena pointer length) (outArena : AllocatedBytes.Arena out 32)
    (stateBefore : stp.toNat+200≤table.toNat) (padBefore : pad.toNat+136≤table.toNat) (outBefore : out.toNat+32≤table.toNat)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)=(none,post)) :
    Image post table cap root next count valid bits left right keys ValueOf := by
  have fields := evaluation_fields source post _ none run
  apply image.of_lower_frame fields.1 fields.2.1
  intro query afterTable
  exact (CurrentKeccak.Hash.call_frame source post stp pad pointer out query length environment arguments args inputArena outArena
    (CopyGeneral.Away.before stp query 200 table.toNat stateBefore table.isLt afterTable)
    (CopyGeneral.Away.before pad query 136 table.toNat padBefore table.isLt afterTable)
    (CopyGeneral.Away.before out query 32 table.toNat outBefore table.isLt afterTable) run).memory

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.hash_image
