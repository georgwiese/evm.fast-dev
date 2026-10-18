import InitECandidate.Solver.GasBudget.FrameOpenNormalCall

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual fresh-child opening inserts precisely the real message gas into
the physical live budget and no used credit. Current ownership protects the
existing live words; reaching that ownership/list in run_frames is separate. -/
theorem call_sums (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (rest : ProgHOL 64) (value : ValueHOL 64)
    (scratch lower message empty parent continuation kind : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64) (live : List (BitVec 64))
    (liveOutside : ∀ frame ∈ live, ∀ offset ∈ ([64, 184, 192] : List Nat), Arenas.Outside lower scratch (frame + BitVec.ofNat 64 offset))
    (entry : FrameNew.Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values message kind))
    (known : source.code.lookup (ofString "frame_open") = some (formals, body, .one))
    (newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "frame_open") arguments rest) = (some (.returned value), post)) :
    ∃ (memory : Memory) (spent : Nat) (inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      spent ≤ words.length.toNat ∧ WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent ≤ source.clock ∧
      GasSeed memory (FrameNew.framePointer scratch) words.gas ∧
      FrameSums.budget memory (FrameNew.framePointer scratch :: live) = words.gas.toNat + FrameSums.budget source.memory live ∧
      FrameSums.used memory (FrameNew.framePointer scratch :: live) = FrameSums.used source.memory live ∧
      evaluateHOLFiniteState (openedState source name scratch lower words.length memory spent) rest = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨memory, spent, inner, bound, fits, budget, seed, outside, run, scopes⟩ :=
    call_normal_full source post name arguments rest value scratch lower message empty parent continuation kind words
      addresses keys addressCount keyCount entry args known newCode evGlobal continuationGlobal room normal
  have liveWords : ∀ frame ∈ live, ∀ offset ∈ ([64, 184, 192] : List Nat),
      memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) := by
    intro frame member offset inside
    exact outside _ (liveOutside frame member offset inside)
  have liveBudget := FrameSums.budget_congr source.memory memory live liveWords
  have liveUsed := FrameSums.used_congr source.memory memory live (by intro frame member; exact liveWords frame member 184 (by simp))
  have inserted := seed.insert live
  rw [liveBudget] at inserted
  rw [liveUsed] at inserted
  exact ⟨memory, spent, inner, bound, fits, seed, inserted.1, inserted.2, run, scopes⟩

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.call_sums
