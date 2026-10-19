import InitECandidate.Solver.Mpt.KeyToNibblesExecution
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (lengthCell : source.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (inputMapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 8 := by
  by_cases enough : 8 ≤ source.clock
  · obtain ⟨post, run, view, clock, frame⟩ := execute_mapped source key out keyCell outCell lengthCell little fits inputMapped outputMapped separate enough
    rw [run]
    change source.clock - post.clock ≤ 8
    omega
  · omega

/-- A real original normal return derives its funding, exact source cost,
zero result and current physical nibble buffer/footprint. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (lengthCell : source.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (inputMapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right)
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    8 ≤ source.clock ∧ target.clock = source.clock - 8 ∧ returned = .val (.word 0#64) ∧
      TrieWalk.KeyView target.memory target.memaddrs target.be out 64 ∧ OutputFrame source target out := by
  let padded := {source with clock := source.clock + 8}
  obtain ⟨post, run, view, clock, frame⟩ := execute_mapped padded key out keyCell outCell lengthCell little fits inputMapped outputMapped separate (by change 8 ≤ source.clock + 8; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned returned)) target 8
    ⟨normal, by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans run)
  have postEq := congrArg Prod.snd (lifted.symm.trans run)
  change {target with clock := target.clock + 8} = post at postEq
  have postClock := congrArg PanSemStateFiniteExact.clock postEq
  change target.clock + 8 = post.clock at postClock
  change post.clock = source.clock + 8 - 8 at clock
  have answer : returned = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
  rw [← postEq] at view frame
  exact ⟨by omega, by omega, answer, view, ⟨frame.fields, frame.memory⟩⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.body_cost
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.body_normal
