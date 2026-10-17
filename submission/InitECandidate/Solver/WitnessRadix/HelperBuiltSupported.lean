import InitECandidate.Solver.WitnessRadix.HelperNonemptySupported
import InitECandidate.Solver.WitnessRadix.HelperEmptyPublic

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Entire literal candidate radix helper on every initialized ordinal array,
including the empty case. Its root represents last-record-wins construction;
its source-clock cost is at most 1028*N. -/
theorem helper_built_supported {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice) (input : List (BitVec 64))
    (length : input.length = layout.count) (ordinals : ∀ ordinal ∈ input, ordinal.toNat < layout.count)
    (mapped : Mapped source layout) (immutable : Immutable source layout keyFor sliceFor)
    (rows : BuildCopy.Rows source.memory source.memaddrs layout.primary 0#64 0 input)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word layout.table)))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 layout.count))))
    (header : BuildEntry.Header source layout.table layout.keys layout.vals layout.primary layout.backup)
    (enough : 1028 * layout.count ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F, ∃ root : BitVec 64,
      evaluateHOLFiniteState source BuildProgram.body = (some (.returned (.val (.word 0#64))), target) ∧
      target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24) = .word root ∧
      QueryMemory.Represents target layout.table layout.keys layout.vals root (initialTree keyFor sliceFor input) ∧
      control target = control source ∧ source.clock - 1028 * layout.count ≤ target.clock ∧ target.clock ≤ source.clock ∧
      (∀ query,PublicWord layout query→target.memory query=source.memory query) ∧
      (∀ query,QueryMemory.reads target layout.table layout.keys layout.vals root (initialTree keyFor sliceFor input) query →
        Protected layout layout.count query) := by
  by_cases empty : input = []
  · subst input
    have zero : layout.count = 0 := length.symm
    have countZero : source.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by simpa only [zero] using countLocal
    have rootMapped := mapped .header 24 (by decide) (by change 24 + 8 ≤ 72; decide)
    obtain ⟨target, run, mappedRoot, word, represented, fields, clock,publicFrame⟩ :=
      helper_empty_public source layout keyFor sliceFor tableLocal countZero header rootMapped
    refine ⟨target, 0#64, run, mappedRoot, word, represented, fields, ?_, ?_,publicFrame,?support⟩
    case support =>
      intro query read
      change False at read
      exact read.elim
    · rw [clock, zero]; simp
    · rw [clock]
      exact Nat.le_refl _
  · exact helper_nonempty_supported source layout valid keyFor sliceFor input length empty ordinals mapped immutable rows tableLocal countLocal header enough

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.helper_built_supported
