import InitECandidate.Solver.WitnessRadix.QueryMemory

namespace InitECandidate.Solver.WitnessRadix.QueryLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def loop : ProgHOL 64 := .while QueryEmpty.condition QueryEmpty.loopBody

theorem condition_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (root : BitVec 64)
    (node : source.locals.lookup (ofString "node") = some (.val (.word root))) :
    @evalHOLFinite 64 F _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) QueryEmpty.condition =
      some (.val (.word (if root = 0#64 then 0#64 else 1#64))) := by
  classical
  by_cases zero : root = 0#64
  all_goals simp [QueryEmpty.condition, evalHOLFinite, evalHOLExact, toExact, node,
    zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem empty {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node : source.locals.lookup (ofString "node") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source loop = (none, source) := by
  classical
  rw [loop, evaluateHOLFiniteState_while_total, condition_read source 0#64 node]
  simp

theorem branch {F : Type} (source : PanSemStateFiniteExact 64 F)
    (root child : BitVec 64)
    (node : source.locals.lookup (ofString "node") = some (.val (.word root)))
    (nonzero : root ≠ 0#64) (enough : source.clock ≠ 0)
    (body : evaluateHOLFiniteState (decClockHOLFinite source) QueryEmpty.loopBody =
      (none, bind (decClockHOLFinite source) "node" child)) :
    evaluateHOLFiniteState source loop =
      evaluateHOLFiniteState (bind (decClockHOLFinite source) "node" child) loop := by
  classical
  rw [loop, evaluateHOLFiniteState_while_total, condition_read source root node]
  simp only [if_neg nonzero]
  rw [if_pos (by decide)]
  simp only [if_neg enough, body]
  have fixed : fixClockHOLFinite (decClockHOLFinite source)
      ((none : Option (PanSemResultExact 64)), bind (decClockHOLFinite source) "node" child) =
      (none, bind (decClockHOLFinite source) "node" child) := by
    simp [fixClockHOLFinite, QueryBranch.bind, setVarHOLFinite]
  simp only [fixed]

theorem returned {F : Type} (source : PanSemStateFiniteExact 64 F)
    (root : BitVec 64) (value : ValueHOL 64) (paid : Nat)
    (node : source.locals.lookup (ofString "node") = some (.val (.word root)))
    (nonzero : root ≠ 0#64) (enough : source.clock ≠ 0)
    (body : (evaluateHOLFiniteState (decClockHOLFinite source) QueryEmpty.loopBody).1 =
      some (.returned value))
    (frame : emptyLocalsHOLFinite
      (evaluateHOLFiniteState (decClockHOLFinite source) QueryEmpty.loopBody).2 =
      emptyLocalsHOLFinite { decClockHOLFinite source with
        clock := (decClockHOLFinite source).clock - paid }) :
    (evaluateHOLFiniteState source loop).1 = some (.returned value) ∧
    emptyLocalsHOLFinite (evaluateHOLFiniteState source loop).2 =
      emptyLocalsHOLFinite { source with clock := source.clock - (paid + 1) } := by
  classical
  have clockEq := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) frame
  change (evaluateHOLFiniteState (decClockHOLFinite source) QueryEmpty.loopBody).2.clock =
    source.clock - 1 - paid at clockEq
  have notGreater : ¬ (decClockHOLFinite source).clock <
      (evaluateHOLFiniteState (decClockHOLFinite source) QueryEmpty.loopBody).2.clock := by
    rw [clockEq]
    change ¬ source.clock - 1 < source.clock - 1 - paid
    omega
  rw [loop, evaluateHOLFiniteState_while_total, condition_read source root node]
  simp only [if_neg nonzero]
  rw [if_pos (by decide)]
  simp only [if_neg enough,
    body, fixClockHOLFinite, notGreater, ↓reduceIte]
  have clockSub : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  constructor
  · trivial
  · simpa only [decClockHOLFinite, clockSub] using frame

end InitECandidate.Solver.WitnessRadix.QueryLoop

#print axioms InitECandidate.Solver.WitnessRadix.QueryLoop.branch
#print axioms InitECandidate.Solver.WitnessRadix.QueryLoop.returned
