import InitECandidate.Solver.Input.BnModmulBody
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.BnModmul
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 100000

/-- Arithmetic preserves the same nonlocal control fields as hashing; the
real accumulated event sequence is retained by the post-state. -/
theorem body_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words) :
    KeccakAbsorb.hashControl (bodyPost source pointer a b) = KeccakAbsorb.hashControl source := by
  simp only [bodyPost,reply,BnArithmetic.post,BnArithmetic.nextFfi,operands,KeccakAbsorb.hashControl,emptyLocalsHOLFinite]

theorem body_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words) :
    (bodyPost source pointer a b).clock = source.clock - 1 := rfl

theorem Environment.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (entry : Environment source pointer) (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source)
    (modulus : ∀ index : Fin 4,target.memory (byteAddress pointer (96 + 8 * index.val)) = .word (Main.BnAccelInitialization.modulus index)) :
    Environment target pointer := by
  have globals := congrArg (fun state => state.globals) same
  have code := congrArg (fun state => state.code) same
  have domain := congrArg (fun state => state.memaddrs) same
  have endian := congrArg (fun state => state.be) same
  have oracle := congrArg (fun state => state.ffi.oracle) same
  change target.globals = source.globals at globals
  change target.code = source.code at code
  change target.memaddrs = source.memaddrs at domain
  change target.be = source.be at endian
  change target.ffi.oracle = source.ffi.oracle at oracle
  refine ⟨?_,?_,?_,?_,?_,?_,?_,entry.arena,entry.aligned,?_,modulus⟩
  · rw [code]; exact entry.installed
  · rw [globals]; exact entry.params
  · rw [globals]; exact entry.a
  · rw [globals]; exact entry.b
  · rw [globals]; exact entry.d
  · rw [oracle]; exact entry.oracle
  · exact domain.trans entry.domain
  · exact endian.trans entry.little

/-- Complete original602 wrapper: the real tail call runs593 and returns
its actual reply quad, preserving the current arithmetic environment. -/
theorem fq_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words)
    (entry : Environment source pointer)
    (aLocal : source.locals.lookup (ofString "a") = some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b") = some (RlpWrite.U256Value.tuple b)) (enough : 2 ≤ source.clock) :
    ∃ target answer,evaluateHOLFiniteState source fqBody = (some (.returned (RlpWrite.U256Value.tuple answer)),target) ∧
      target.clock = source.clock - 2 ∧ KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source ∧ Environment target pointer ∧
      ∀ offset,64 ≤ offset → offset < 128 → target.memory (byteAddress pointer offset) = source.memory (byteAddress pointer offset) := by
  obtain ⟨callee,called,aRead,bRead⟩ := environment source.code.lookup (ofString "bn254_accel_modmul") body a b (original_code source.code entry.installed)
  let inner := callEntryStateHOLFinite source callee
  have innerEnvironment : Environment inner pointer := entry.of_control source inner pointer rfl entry.modulus
  have run := execute inner pointer a b innerEnvironment aRead bRead (by change 1 ≤ source.clock - 1; omega)
  have arguments : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [.var .local (ofString "a"),.var .local (ofString "b")] = some (values a b) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,aLocal,bLocal,values]
  have actual := evaluateHOLFiniteState_call_return_none source (RlpWrite.U256Value.tuple (bodyResult inner pointer a b))
    (ofString "bn254_accel_modmul") _ (values a b) body callee RlpWrite.U256Value.tupleShape
    (emptyLocalsHOLFinite (bodyPost inner pointer a b)) arguments called (by omega) run
    (by simp [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  refine ⟨emptyLocalsHOLFinite (emptyLocalsHOLFinite (bodyPost inner pointer a b)),bodyResult inner pointer a b,?_,?_,?_,?_,?_⟩
  · rw [fq_body_shape]; exact actual
  · change (bodyPost inner pointer a b).clock = _
    rw [body_clock]
    change source.clock - 1 - 1 = source.clock - 2
    omega
  · exact body_control inner pointer a b
  · exact (body_environment inner pointer a b innerEnvironment).of_control (bodyPost inner pointer a b) _ pointer rfl
      (body_environment inner pointer a b innerEnvironment).modulus
  · exact body_prefix inner pointer a b innerEnvironment

/-- The actual scoped fq_mul resumes its literal continuation after three
source ticks. All arguments and state effects are derived from the real calls. -/
theorem fq_call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (entry : Environment source pointer)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (values a b))
    (enough : 3 ≤ source.clock) :
    ∃ target answer,
      evaluateHOLFiniteState source (.decCall (ofString name) RlpWrite.U256Value.tupleShape (ofString "fq_mul") arguments continuation) =
        (let output := evaluateHOLFiniteState (CallNormal.continuationEntry source target name (RlpWrite.U256Value.tuple answer)) continuation;
          (output.1,restore source name output.2)) ∧
      target.clock = source.clock - 3 ∧ KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source ∧ Environment target pointer ∧
      ∀ offset,64 ≤ offset → offset < 128 → target.memory (byteAddress pointer offset) = source.memory (byteAddress pointer offset) := by
  obtain ⟨callee,called,aRead,bRead⟩ := environment source.code.lookup (ofString "fq_mul") fqBody a b (fq_original_code source.code entry.installed)
  let inner := callEntryStateHOLFinite source callee
  have innerEnvironment : Environment inner pointer := entry.of_control source inner pointer rfl entry.modulus
  obtain ⟨target,answer,run,clock,control,preserved,frame⟩ := fq_execute inner pointer a b innerEnvironment aRead bRead (by change 2 ≤ source.clock - 1; omega)
  have actual := CallNormal.return_execute source target name RlpWrite.U256Value.tupleShape (ofString "fq_mul") arguments (values a b) fqBody continuation callee
    RlpWrite.U256Value.tupleShape (RlpWrite.U256Value.tuple answer) args called (by omega) run
    (by simp [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  refine ⟨target,answer,actual,?_,control,preserved,frame⟩
  change target.clock = source.clock - 1 - 2 at clock
  omega

end InitECandidate.Solver.Input.BnModmul

#print axioms InitECandidate.Solver.Input.BnModmul.body_control
#print axioms InitECandidate.Solver.Input.BnModmul.body_clock
#print axioms InitECandidate.Solver.Input.BnModmul.Environment.of_control
#print axioms InitECandidate.Solver.Input.BnModmul.fq_execute
#print axioms InitECandidate.Solver.Input.BnModmul.fq_call_execute
