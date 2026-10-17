import InitECandidate.Solver.WitnessRadix.SplitScopeExecution
import InitECandidate.Solver.WitnessRadix.UnaryBody

namespace InitECandidate.Solver.WitnessRadix.SplitCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch SplitScope

/-- Live construction fields before the temporary counters are introduced. -/
structure TaskLocals {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : Prop where
  srcLocal : source.locals.lookup (ofString "src") = some (.val (.word context.src))
  dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word context.dst))
  keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word context.keys))
  nextLocal : source.locals.lookup (ofString "node_next") = some (.val (.word context.node))
  depthLocal : source.locals.lookup (ofString "depth") = some (.val (.word context.depth))
  startLocal : source.locals.lookup (ofString "start") = some (.val (.word (BitVec.ofNat 64 context.start)))
  countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 context.input.length)))
  bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 context.position)))
  destLocal : source.locals.lookup (ofString "dest") = some (.val (.word context.dest))
  pendingStartLocal : source.locals.lookup (ofString "pending_start") = some (.val (.word context.pendingStart))
  pendingCountLocal : source.locals.lookup (ofString "pending_count") = some (.val (.word context.pendingCount))
  pendingNodeLocal : source.locals.lookup (ofString "pending_node") = some (.val (.word context.pendingNode))

structure Inputs {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : Prop where
  inside : context.position < 256
  small : context.input.length < 2 ^ 64
  fits : context.start + context.input.length ≤ context.limit
  allocation : context.dst.toNat + 8 * context.limit < 2 ^ 64
  enough : 3 * context.input.length ≤ source.clock
  splitZero : 0 < zeroCount context
  splitOne : zeroCount context < context.input.length
  locals : TaskLocals source context
  mapped : SplitProgram.Mapped source context.node context.depth context.dest context.pendingStart context.pendingCount context.pendingNode
  ready : ScatterProgram.Ready source context.src context.dst (BitVec.ofNat 64 context.start) context.keys
    context.keyFor context.input 0 context.limit

theorem task_locals_of_lookup {F : Type} (source target : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (outside : ∀ name : MlS, ofString "i" ≠ name → ofString "zeros" ≠ name →
      target.locals.lookup name = source.locals.lookup name)
    (locals : TaskLocals source context) : TaskLocals target context := by
  exact ⟨(outside _ (by decide) (by decide)).trans locals.srcLocal,
    (outside _ (by decide) (by decide)).trans locals.dstLocal,
    (outside _ (by decide) (by decide)).trans locals.keysLocal,
    (outside _ (by decide) (by decide)).trans locals.nextLocal,
    (outside _ (by decide) (by decide)).trans locals.depthLocal,
    (outside _ (by decide) (by decide)).trans locals.startLocal,
    (outside _ (by decide) (by decide)).trans locals.countLocal,
    (outside _ (by decide) (by decide)).trans locals.bitLocal,
    (outside _ (by decide) (by decide)).trans locals.destLocal,
    (outside _ (by decide) (by decide)).trans locals.pendingStartLocal,
    (outside _ (by decide) (by decide)).trans locals.pendingCountLocal,
    (outside _ (by decide) (by decide)).trans locals.pendingNodeLocal⟩

theorem entry_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (locals : TaskLocals source context)
    (zerosLocal : source.locals.lookup (ofString "zeros") = some (.val (.word (BitVec.ofNat 64 (zeroCount context))))) :
    SplitProgram.EntryLocals source context.node context.depth (BitVec.ofNat 64 context.start)
      (BitVec.ofNat 64 context.input.length) (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position)
      context.dest context.pendingStart context.pendingCount context.pendingNode :=
  ⟨locals.nextLocal, locals.depthLocal, locals.startLocal, locals.countLocal, zerosLocal,
    locals.bitLocal, locals.destLocal, locals.pendingStartLocal, locals.pendingCountLocal, locals.pendingNodeLocal⟩

theorem after_count_split {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : SplitScope.Inputs source context)
    (small : context.input.length < 2 ^ 64) (splitZero : 0 < zeroCount context)
    (splitOne : zeroCount context < context.input.length) :
    evaluateHOLFiniteState source UnaryProgram.afterCount = (none, SplitScope.post source context) := by
  classical
  have zeroSmall : zeroCount context < 2 ^ 64 := Nat.lt_trans splitOne small
  have zeroNe : BitVec.ofNat 64 (zeroCount context) ≠ 0#64 := by
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt zeroSmall] at numeric
    change zeroCount context = 0 at numeric
    omega
  have countNe : BitVec.ofNat 64 (zeroCount context) ≠ BitVec.ofNat 64 context.input.length := by
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt zeroSmall,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at numeric
    omega
  have test := UnaryProgram.test_read source _ _ premises.locals.zerosLocal premises.locals.countLocal
  simp only [eval, zeroNe, countNe, or_self, ↓reduceIte] at test
  have skipped : evaluateHOLFiniteState source
      (.ite UnaryProgram.unaryTest UnaryProgram.unaryBody .skip) = (none, source) := by
    rw [evaluateHOLFiniteState_ite, test]
    simp
  rw [UnaryProgram.after_count_shape,
    StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)]
  exact SplitScope.execute source context premises

end InitECandidate.Solver.WitnessRadix.SplitCount

#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.after_count_split
