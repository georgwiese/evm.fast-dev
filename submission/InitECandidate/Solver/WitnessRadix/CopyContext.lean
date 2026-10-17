import InitECandidate.Solver.WitnessRadix.CopyByteState
import InitECandidate.Solver.WitnessRadix.CopyWordState

namespace InitECandidate.Solver.WitnessRadix.CopyContext
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

structure Args {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) : Prop where
  srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src))
  dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst))
  lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))

structure Mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) : Prop where
  sourceBytes : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress src offset))
  destinationBytes : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress dst offset))
  sourceWords : (dst ||| src) &&& 7#64 = 0#64 → ∀ offset < length, offset % 8 = 0 → source.memaddrs (byteAddress src offset)
  destinationWords : (dst ||| src) &&& 7#64 = 0#64 → ∀ offset < length, offset % 8 = 0 → source.memaddrs (byteAddress dst offset)

theorem Mapped.of_domain {F : Type} (source target : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (domain : target.memaddrs = source.memaddrs) (mapped : Mapped source src dst length) : Mapped target src dst length := by
  constructor
  · simpa only [domain] using mapped.sourceBytes
  · simpa only [domain] using mapped.destinationBytes
  · simpa only [domain] using mapped.sourceWords
  · simpa only [domain] using mapped.destinationWords

theorem Args.byte_walk {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length index step rounds : Nat) (offsets : List Nat)
    (args : Args source src dst length) : Args (CopyBytes.walk source src dst index step offsets rounds) src dst length := by
  constructor
  · rw [CopyBytes.walk_other _ _ _ _ _ _ _ _ (by decide)]; exact args.srcLocal
  · rw [CopyBytes.walk_other _ _ _ _ _ _ _ _ (by decide)]; exact args.dstLocal
  · rw [CopyBytes.walk_other _ _ _ _ _ _ _ _ (by decide)]; exact args.lengthLocal

theorem Args.word_walk {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length index step rounds : Nat) (offsets : List Nat)
    (args : Args source src dst length) : Args (CopyWords.walk source src dst index step offsets rounds) src dst length := by
  constructor
  · rw [CopyWords.walk_other _ _ _ _ _ _ _ _ (by decide)]; exact args.srcLocal
  · rw [CopyWords.walk_other _ _ _ _ _ _ _ _ (by decide)]; exact args.dstLocal
  · rw [CopyWords.walk_other _ _ _ _ _ _ _ _ (by decide)]; exact args.lengthLocal

theorem byte_walk_domain {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    (CopyBytes.walk source src dst index step offsets rounds).memaddrs = source.memaddrs := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memaddrs) (CopyBytes.walk_frame source src dst index step offsets rounds)
  exact h

theorem word_walk_domain {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    (CopyWords.walk source src dst index step offsets rounds).memaddrs = source.memaddrs := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memaddrs) (CopyWords.walk_frame source src dst index step offsets rounds)
  exact h

theorem byte_walk_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    (CopyBytes.walk source src dst index step offsets rounds).clock = source.clock - rounds := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) (CopyBytes.walk_frame source src dst index step offsets rounds)
  exact h

theorem word_walk_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    (CopyWords.walk source src dst index step offsets rounds).clock = source.clock - rounds := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) (CopyWords.walk_frame source src dst index step offsets rounds)
  exact h

end InitECandidate.Solver.WitnessRadix.CopyContext

#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.Mapped.of_domain
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.Args.byte_walk
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.Args.word_walk
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.byte_walk_domain
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.word_walk_domain
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.byte_walk_clock
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.word_walk_clock
