import InitECandidate.Solver.WitnessRadix.LoopResult

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

/-- The actual construction loop terminates from the complete invariant.
Its final root represents the expected tree, and source-clock consumption is
at most four times the remaining record/bit-depth agenda weight. -/
theorem loop_terminates {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree)
    (inv : Invariant source layout sliceFor expectedTree allocated completed depth context destination tasks graph)
    (enough : 4 * agendaWeight (agenda context tasks) ≤ source.clock) :
    LoopResult source layout expectedTree (agendaWeight (agenda context tasks)) := by
  have general : ∀ (weight : Nat) (source : PanSemStateFiniteExact 64 F) (allocated completed depth : Nat)
      (context : SplitContext) (destination : Address) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree),
      agendaWeight (agenda context tasks) = weight →
      Invariant source layout sliceFor expectedTree allocated completed depth context destination tasks graph →
      4 * weight ≤ source.clock → LoopResult source layout expectedTree weight := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
        intro source allocated completed depth context destination tasks graph weightEq inv enough
        subst weight
        have present : 0 < context.input.length := List.length_pos_iff.mpr inv.present
        have lengthBound := weight_ge_length context tasks
        have positive : source.clock ≠ 0 := by omega
        let entry := decClockHOLFinite source
        have entryInv : Invariant entry layout sliceFor expectedTree allocated completed depth context destination tasks graph :=
          invariant_clock source layout valid sliceFor expectedTree allocated completed depth context destination tasks graph inv (source.clock - 1)
        have enoughBody : 3 * context.input.length ≤ entry.clock := by change 3 * context.input.length ≤ source.clock - 1; omega
        by_cases stop : context.input.length = 1 ∨ context.position = 256
        · obtain ⟨ordinal, last⟩ := last_exists context.input inv.present
          cases tasks with
          | nil =>
              obtain ⟨target, root, body, frame, mapped, word, represented⟩ :=
                invariant_terminal_finish entry layout valid sliceFor expectedTree allocated completed depth context destination graph entryInv stop ordinal last
              have clockEq : target.clock = source.clock - 1 := congrArg (fun state => state.clock) frame
              have run := loop_return source target (.val (.word 0#64)) positive body (by rw [clockEq]; exact Nat.le_refl _)
              refine ⟨target, root, run, mapped, word, represented, ?_, ?_, ?_⟩
              · exact (control_of_frame target (OpenGraph.leafPost entry context.dest ordinal.toNat) frame).trans rfl
              · rw [clockEq]; omega
              · rw [clockEq]; omega
          | cons task rest =>
              obtain ⟨nextGraph, parent, body, nextInv⟩ :=
                invariant_terminal_continue entry layout valid sliceFor expectedTree allocated completed depth context destination task rest graph entryInv stop ordinal last
              let next := resumePost entry context task ordinal.toNat
              let nextWeight := agendaWeight (agenda (resumeContext context task rest.length) rest)
              have smaller : nextWeight < agendaWeight (agenda context (task :: rest)) := by
                rw [terminal_weight]
                have product : 0 < (256 - context.position + 1) * context.input.length := Nat.mul_pos (by omega) present
                change nextWeight < (256 - context.position + 1) * context.input.length + nextWeight
                omega
              have price : 1 + 4 * nextWeight ≤ 4 * agendaWeight (agenda context (task :: rest)) := terminal_price context task rest present
              have clockEq : next.clock = source.clock - 1 := rfl
              have nextEnough : 4 * nextWeight ≤ next.clock := by rw [clockEq]; omega
              have remaining := ih nextWeight smaller next allocated (completed + 1) rest.length
                (resumeContext context task rest.length) (resumeDestination layout parent) rest nextGraph rfl nextInv nextEnough
              have run := loop_next source next (some .continue) (Or.inr rfl) positive body (Nat.le_refl _)
              exact result_next source next layout expectedTree _ nextWeight 1 run
                ((resume_control entry context task ordinal.toNat).trans rfl) clockEq price remaining
        · have notSingle : context.input.length ≠ 1 := fun single => stop (Or.inl single)
          have notLast : context.position ≠ 256 := fun lastBit => stop (Or.inr lastBit)
          have inside : context.position < 256 := by have := inv.position; omega
          have many : 1 < context.input.length := by omega
          by_cases uniform : zeroCount context = 0 ∨ zeroCount context = context.input.length
          · obtain ⟨body, nextInv⟩ := invariant_unary entry layout valid sliceFor expectedTree allocated completed depth context destination tasks graph entryInv
              inside many uniform (by omega)
            let next := unaryPost entry context
            let nextWeight := agendaWeight (agenda (unaryContext context) tasks)
            have smaller : nextWeight < agendaWeight (agenda context tasks) := by
              rw [unary_weight context tasks inside]
              change nextWeight < nextWeight + context.input.length
              omega
            have price : context.input.length + 1 + 4 * nextWeight ≤ 4 * agendaWeight (agenda context tasks) := unary_price context tasks inside present
            have clockEq : next.clock = source.clock - (context.input.length + 1) := by
              change source.clock - 1 - context.input.length = _
              omega
            have nextEnough : 4 * nextWeight ≤ next.clock := by rw [clockEq]; omega
            have remaining := ih nextWeight smaller next allocated completed depth (unaryContext context) destination tasks graph rfl nextInv nextEnough
            have run := loop_next source next (some .continue) (Or.inr rfl) positive body (by
              change source.clock - 1 - context.input.length ≤ source.clock - 1
              omega)
            exact result_next source next layout expectedTree _ nextWeight (context.input.length + 1) run
              ((unary_control entry context).trans rfl) clockEq price remaining
          · have zeroLe : zeroCount context ≤ context.input.length := List.length_filter_le _ _
            have notZero : zeroCount context ≠ 0 := fun empty => uniform (Or.inl empty)
            have notAll : zeroCount context ≠ context.input.length := fun full => uniform (Or.inr full)
            have splitZero : 0 < zeroCount context := by omega
            have splitOne : zeroCount context < context.input.length := by omega
            obtain ⟨nextGraph, body, nextInv⟩ := invariant_split entry layout valid sliceFor expectedTree allocated completed depth context destination tasks graph entryInv
              inside splitZero splitOne enoughBody
            let next := SplitCount.post entry context
            let nextWeight := agendaWeight (agenda (SplitCount.leftContext context) (PendingStack.rightTask context :: tasks))
            have smaller : nextWeight < agendaWeight (agenda context tasks) := by
              rw [split_weight context tasks inside]
              change nextWeight < nextWeight + context.input.length
              omega
            have price : 3 * context.input.length + 1 + 4 * nextWeight ≤ 4 * agendaWeight (agenda context tasks) := split_price context tasks inside present
            have clockEq : next.clock = source.clock - (3 * context.input.length + 1) := by
              rw [show next.clock = entry.clock - 3 * context.input.length from SplitCount.post_clock entry context]
              change source.clock - 1 - 3 * context.input.length = _
              omega
            have nextEnough : 4 * nextWeight ≤ next.clock := by rw [clockEq]; omega
            have remaining := ih nextWeight smaller next (allocated + 1) completed (depth + 1) (SplitCount.leftContext context)
              (leftDestination layout allocated) (PendingStack.rightTask context :: tasks) nextGraph rfl nextInv nextEnough
            have run := loop_next source next none (Or.inl rfl) positive body (by
              rw [show next.clock = entry.clock - 3 * context.input.length from SplitCount.post_clock entry context]
              exact Nat.sub_le _ _)
            exact result_next source next layout expectedTree _ nextWeight (3 * context.input.length + 1) run
              ((split_control entry context).trans rfl) clockEq price remaining
  exact general _ source allocated completed depth context destination tasks graph rfl inv enough

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.loop_terminates
