import InitECandidate.Solver.Input.Requests.SetupFields
import InitECandidate.Solver.Input.Requests.CountLocals

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual allocator/load prefix supplies every fixed-list argument local. -/
theorem prepared_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor pointer total : BitVec 64) (start : Nat)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "len") = some (.val (.word total))) :
    CountLocals (prepared source input cursor start) (offsetWord input start) total pointer cursor := by
  have offsets := prepared_offsets source input cursor start
  have locals (index : Nat) (small : index < 5) : (prepared source input cursor start).locals.lookup (ofString (offsetName index)) = some (.val (.word (offsetWord input start index))) := by
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · exact offsets.1
    · exact offsets.2.1
    · exact offsets.2.2.1
    · exact offsets.2.2.2.1
    · exact offsets.2.2.2.2
  exact ⟨locals,(prepared_other source input cursor start (ofString "len") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans n,
    (prepared_other source input cursor start (ofString "p") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p,
    prepared_request source input cursor start⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.prepared_model
