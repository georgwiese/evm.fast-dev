import InitECandidate.Solver.WitnessRadix.SortExecution
import InitECandidate.Solver.WitnessRadix.AllocationPost

namespace InitECandidate.Solver.WitnessRadix.SplitScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

structure SplitContext where
  src : BitVec 64
  dst : BitVec 64
  keys : BitVec 64
  node : BitVec 64
  depth : BitVec 64
  dest : BitVec 64
  pendingStart : BitVec 64
  pendingCount : BitVec 64
  pendingNode : BitVec 64
  keyFor : BitVec 64 → ByteKeys.Key
  input : List (BitVec 64)
  position : Nat
  start : Nat
  limit : Nat

def zeroCount (context : SplitContext) : Nat := ScatterProgram.zeros context.keyFor context.position context.input
def cursorState {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : PanSemStateFiniteExact 64 F :=
  bind source "zero_cursor" (BitVec.ofNat 64 context.start)
def entered {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : PanSemStateFiniteExact 64 F :=
  bind (cursorState source context) "one_cursor" (BitVec.ofNat 64 (context.start + zeroCount context))
def sorted {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : PanSemStateFiniteExact 64 F :=
  SortProgram.sorted (entered source context) context.src context.dst context.keyFor context.position context.start context.input
def base {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : PanSemStateFiniteExact 64 F :=
  { source with
    memory := SortProgram.sortedMemory source.memory context.src context.dst context.keyFor context.position context.start context.input
    clock := source.clock - 2 * context.input.length }
def post {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : PanSemStateFiniteExact 64 F :=
  SplitProgram.branchPost (base source context) context.node context.depth (BitVec.ofNat 64 context.start)
    (BitVec.ofNat 64 context.input.length) (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position)
    context.dest context.pendingStart context.pendingCount context.pendingNode

structure Inputs {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : Prop where
  inside : context.position < 256
  fits : context.start + context.input.length ≤ context.limit
  allocation : context.dst.toNat + 8 * context.limit < 2 ^ 64
  enough : 2 * context.input.length ≤ source.clock
  srcLocal : source.locals.lookup (ofString "src") = some (.val (.word context.src))
  dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word context.dst))
  keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word context.keys))
  indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 context.input.length)))
  locals : SplitProgram.EntryLocals source context.node context.depth (BitVec.ofNat 64 context.start)
    (BitVec.ofNat 64 context.input.length) (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position)
    context.dest context.pendingStart context.pendingCount context.pendingNode
  mapped : SplitProgram.Mapped source context.node context.depth context.dest context.pendingStart context.pendingCount context.pendingNode
  ready : ScatterProgram.Ready source context.src context.dst (BitVec.ofNat 64 context.start) context.keys
    context.keyFor context.input 0 context.limit

theorem entered_other {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) (query : MlS)
    (notZero : query ≠ ofString "zero_cursor") (notOne : query ≠ ofString "one_cursor") :
    (entered source context).locals.lookup query = source.locals.lookup query := by
  simp [entered, cursorState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update,
    FUPDATE, Ne.symm notZero, Ne.symm notOne]

theorem sort_inputs {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) :
    SortProgram.Inputs (entered source context) context.src context.dst context.keys context.keyFor
      context.input context.position context.start context.limit := by
  have other (name : String) (nz : ofString name ≠ ofString "zero_cursor") (no : ofString name ≠ ofString "one_cursor") :=
    entered_other source context (ofString name) nz no
  refine ⟨premises.inside, premises.fits, premises.allocation,
    (other _ (by decide) (by decide)).trans premises.srcLocal,
    (other _ (by decide) (by decide)).trans premises.dstLocal,
    (other _ (by decide) (by decide)).trans premises.locals.startLocal,
    (other _ (by decide) (by decide)).trans premises.keysLocal,
    (other _ (by decide) (by decide)).trans premises.locals.bitLocal,
    (other _ (by decide) (by decide)).trans premises.locals.countLocal,
    (other _ (by decide) (by decide)).trans premises.indexLocal, ?_, ?_, ?_, premises.enough⟩
  · unfold entered
    rw [bind_lookup_other (cursorState source context) "one_cursor" "zero_cursor" _ (by decide)]
    exact bind_lookup_same source "zero_cursor" _
  · exact bind_lookup_same (cursorState source context) "one_cursor" _
  · exact ScatterProgram.ready_of_fields source (entered source context) rfl rfl rfl _ _ _ _ _ _ _ _ premises.ready

end InitECandidate.Solver.WitnessRadix.SplitScope

#print axioms InitECandidate.Solver.WitnessRadix.SplitScope.sort_inputs
