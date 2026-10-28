import InitECandidate.Solver.Headers.PipelineObligations
import InitECandidate.Solver.Input.LoopNormal
import InitECandidate.Solver.Input.PureGuard

namespace InitECandidate.Solver.Headers.Pipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem seq_skip (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first : ProgHOL 64) :
    evaluateHOLFiniteState source (.seq first .skip)=evaluateHOLFiniteState source first := by
  rw [evaluateHOLFiniteState_seq_line780]
  generalize evaluateHOLFiniteState source first=output
  obtain ⟨result,middle⟩ := output
  cases result <;> simp [evaluateHOLFiniteState_skip]

/-- The original syntax omits trailing skips; these execution equalities
allow a uniform finite induction without changing the original program. -/
theorem store_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (offset : Nat) (value : StoreValue) (rest : Code) :
    evaluateHOLFiniteState source (program (.store offset value rest))=
      evaluateHOLFiniteState source (.seq (storeProgram offset value) (program rest)) := by
  cases rest <;> simp only [program]
  exact (seq_skip source _).symm

theorem assign_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (slot : Slot) (kind : Helper.Kind) (index : Nat) (control : BitVec 64) (rest : Code) :
    evaluateHOLFiniteState source (program (.assign slot kind index control rest))=
      evaluateHOLFiniteState source (.seq (assigned slot kind index control) (program rest)) := by
  cases rest <;> simp only [program]
  exact (seq_skip source _).symm

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (cell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (kind : Helper.Kind) (index : Nat) (control : BitVec 64) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (arguments kind index control)=
      some (kind.values array (BitVec.ofNat 64 index) control) := by
  cases kind <;> simp [arguments,Helper.Kind.values,Helper.Kind.ternary,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,cell]

def guardProgram (slot : Slot) (maximum error : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .lower (.const maximum) (.rfield 1 (.var .local slot.name))) (.raise (ofString "HdrErr") (.const error)) .skip

theorem guard_pure (slot : Slot) (maximum error : BitVec 64) : Input.PureGuard (guardProgram slot maximum error) :=
  .ite _ (.raise _ _) .skip

theorem choice_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (current : BitVec 64)
    (cell : source.locals.lookup (ofString "is_current")=some (.val (.word current))) (yes no : Code) :
    evaluateHOLFiniteState source (.ite (.cmp .notEqual (.var .local (ofString "is_current")) (.const 0#64)) (program yes) (program no))=
      evaluateHOLFiniteState source (program (if current=0#64 then no else yes)) := by
  by_cases zero : current=0#64
  · simp [evaluateHOLFiniteState_ite,evalHOLExact,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
  · simp [evaluateHOLFiniteState_ite,evalHOLExact,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]

end InitECandidate.Solver.Headers.Pipeline

#print axioms InitECandidate.Solver.Headers.Pipeline.seq_skip
#print axioms InitECandidate.Solver.Headers.Pipeline.store_step
#print axioms InitECandidate.Solver.Headers.Pipeline.assign_step
#print axioms InitECandidate.Solver.Headers.Pipeline.arguments_read
#print axioms InitECandidate.Solver.Headers.Pipeline.guard_pure
#print axioms InitECandidate.Solver.Headers.Pipeline.choice_step
