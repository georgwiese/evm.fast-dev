import InitECandidate.Solver.WitnessRadix.HelperCore

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem initial_price (layout : Layout) (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64))
    (length : input.length = layout.count) :
    4 * agendaWeight (agenda (initialContext layout keyFor input) []) = 1028 * layout.count := by
  simp only [agenda, agendaWeight, activeAgendaTask, initialContext, taskWeight, List.length_map,
    List.map_nil, Nat.sub_zero, Nat.add_zero, length, ← Nat.mul_assoc]

/-- Complete actual nonempty radix helper, including thirteen real prefix
loads/declarations, the initial zero test, the entire loop and lexical restores.
The caller supplies concrete initialized arrays; no execution is a premise. -/
theorem helper_nonempty {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice) (input : List (BitVec 64))
    (length : input.length = layout.count) (present : input ≠ [])
    (ordinals : ∀ ordinal ∈ input, ordinal.toNat < layout.count)
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
      control target = control source ∧ source.clock - 1028 * layout.count ≤ target.clock ∧ target.clock ≤ source.clock := by
  let initial := initialState source layout
  let context := initialContext layout keyFor input
  let graph := initialGraph layout keyFor sliceFor input
  have inv := invariant_initial source layout valid keyFor sliceFor input length present ordinals mapped immutable rows
  have price := initial_price layout keyFor input length
  have loop := loop_terminates initial layout valid sliceFor (initialTree keyFor sliceFor input) 0 0 0 context (.header, 24) [] graph inv
    (by rw [price]; exact enough)
  have positive : 0 < layout.count := by have := List.length_pos_iff.mpr present; omega
  have small : layout.count < 2 ^ 64 := by have := count_small layout valid; omega
  have nonzero : BitVec.ofNat 64 layout.count ≠ 0#64 := by
    intro zero
    have numeric := congrArg BitVec.toNat zero
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at numeric
    change layout.count = 0 at numeric
    omega
  have initialCount : initial.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 layout.count))) := by
    dsimp only [initial, initialState]
    rw [BuildEntry.entered_count]
    exact countLocal
  obtain ⟨loopTarget, root, coreRun, rootMapped, rootWord, represented, controls, lower, upper⟩ :=
    core_nonempty initial layout _ _ _ nonzero initialCount loop
  obtain ⟨restoreStack, restoreFrame, prefixRun⟩ := BuildEntry.prefix_execute source layout.table (BitVec.ofNat 64 layout.count)
    layout.keys layout.vals layout.primary layout.backup tableLocal countLocal header
  change evaluateHOLFiniteState source BuildProgram.body =
    (let output := evaluateHOLFiniteState initial BuildEntry.core; (output.1, restoreStack output.2)) at prefixRun
  rw [coreRun] at prefixRun
  let target := restoreStack loopTarget
  have frame := restoreFrame loopTarget
  have memoryEq : loopTarget.memory = target.memory := (congrArg (fun state => state.memory) frame).symm
  have domainEq : loopTarget.memaddrs = target.memaddrs := (congrArg (fun state => state.memaddrs) frame).symm
  have endianEq : loopTarget.be = target.be := (congrArg (fun state => state.be) frame).symm
  have clockEq : target.clock = loopTarget.clock := congrArg (fun state => state.clock) frame
  refine ⟨target, root, prefixRun, ?_, ?_,
    QueryMemory.represents_of_fields loopTarget target memoryEq domainEq endianEq _ _ _ _ _ represented,
    (control_of_frame target loopTarget frame).trans (controls.trans rfl), ?_, ?_⟩
  · rw [← domainEq]; exact rootMapped
  · rw [← memoryEq]; exact rootWord
  · rw [clockEq]
    rw [price] at lower
    exact lower
  · rw [clockEq]
    exact upper

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.helper_nonempty
