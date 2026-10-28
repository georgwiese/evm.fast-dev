import InitECandidate.Solver.Input.CurrentHash.Sha256Pair
import InitECandidate.Solver.Input.ByteOutputFrame
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Input.CurrentHash.Sha256Memory
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

-- The expanded software pair's only writes are its32output bytes.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem supported : ByteOutputFrame.accepts (ofString "out") 32 (Code.body .sha256_pair) = true := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_sha256_pair, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  rfl

/-- Every body outcome preserves words outside the output. There are no
mutable SHA globals, accelerator buffers or successful-read premises. -/
theorem body_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out query : BitVec 64)
    (cell : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (away : ∀ offset : Nat, offset < 32 → query ≠ panByteAlignHOL (width := 64) (out + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState source (Code.body .sha256_pair)).2.memory query = source.memory query :=
  (ByteOutputFrame.sound (ofString "out") 32 (Code.body .sha256_pair) supported out query away source cell).1

def values (a b out : BitVec 64) : List (ValueHOL 64) := [.val (.word a), .val (.word b), .val (.word out)]

theorem environment (code) (installed : OriginalCode.Installed code) (a b out : BitVec 64) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite code.lookup (Code.name .sha256_pair) (values a b out) =
        some (Code.body .sha256_pair, callee, Code.shape .sha256_pair) ∧
      callee.lookup (ofString "out") = some (.val (.word out)) := by
  have entry : code.lookup (Code.name .sha256_pair) =
      some ([(ofString "input_a",.one),(ofString "input_b",.one),(ofString "out",.one)], Code.body .sha256_pair, Code.shape .sha256_pair) := by
    simpa only [Code.formals,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_pair,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed code installed .sha256_pair
  obtain ⟨callee,called,_,_,output⟩ := word_triple_environment code.lookup (Code.name .sha256_pair)
    (ofString "input_a") (ofString "input_b") (ofString "out") (Code.body .sha256_pair) (Code.shape .sha256_pair) a b out
    (by decide) (by decide) (by decide) entry
  exact ⟨callee,called,output⟩

/-- The real normally continuing ignored caller inherits the memory frame.
The actual ABI identifies the output local in that same callee invocation. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values a b out))
    (away : ∀ offset : Nat, offset < 32 → query ≠ panByteAlignHOL (width := 64) (out + BitVec.ofNat 64 offset))
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) (Code.name .sha256_pair) arguments) = (none, post)) :
    post.memory query = source.memory query := by
  obtain ⟨callee, called, output⟩ := environment source.code installed a b out
  exact MemoryAt.call_normal source post (Code.name .sha256_pair) arguments (values a b out)
    (Code.body .sha256_pair) callee (Code.shape .sha256_pair) query args called
    (by intro target value returned
        have same := body_memory (callEntryStateHOLFinite source callee) out query output away
        rw [returned] at same
        exact same) actual

/-- Checked lookup identifies the real output slot without assuming values
or mapped bytes for either input expression. -/
theorem checked_output (code) (installed : OriginalCode.Installed code) (a b : ValueHOL 64) (out : BitVec 64)
    (actualBody : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite code.lookup (Code.name .sha256_pair) [a,b,.val (.word out)] = some (actualBody,callee,shape)) :
    actualBody = Code.body .sha256_pair ∧ callee.lookup (ofString "out") = some (.val (.word out)) := by
  have formals : Code.formals .sha256_pair = [(ofString "input_a",.one),(ofString "input_b",.one),(ofString "out",.one)] := by
    simp only [Code.formals,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_pair,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
  have raw := lookupCodeHOLFinite_eq_some code.lookup (Code.name .sha256_pair) _ actualBody callee shape called
  simp only [lookupCodeHOLExact,Code.installed code installed .sha256_pair,formals] at raw
  split at raw
  · have bodyEq : Code.body .sha256_pair = actualBody := congrArg Prod.fst (Option.some.inj raw)
    have localsEq := congrArg (fun triple => triple.2.1) (Option.some.inj raw)
    dsimp only at localsEq
    refine ⟨bodyEq.symm,?_⟩
    rw [←localsEq]
    rfl
  · cases raw

/-- The real normal SHA caller preserves protected words even when its two
input expressions are otherwise unrestricted. Only its output is located. -/
theorem call_output_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (left right output : ExpHOL 64) (out query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (read : evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) output = some (.val (.word out)))
    (away : ∀ offset : Nat, offset < 32 → query ≠ panByteAlignHOL (width := 64) (out + BitVec.ofNat 64 offset))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .sha256_pair) [left,right,output]) = (none,post)) :
    post.memory query = source.memory query := by
  classical
  obtain ⟨positive,args,actualBody,callee,shape,target,value,arguments,called,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (Code.name .sha256_pair) [left,right,output] actual
  have argsEq : ∃ a b, args = [a,b,.val (.word out)] := by
    simp only [evalHOLFinite] at read
    change evalListHOLExact source.toExact [left,right,output] = some args at arguments
    cases leftRead : evalHOLExact source.toExact left with
    | none => simp [evalListHOLExact,leftRead] at arguments
    | some a =>
      cases rightRead : evalHOLExact source.toExact right with
      | none => simp [evalListHOLExact,leftRead,rightRead] at arguments
      | some b => exact ⟨a,b,Option.some.inj (by simpa [evalListHOLExact,leftRead,rightRead,read] using arguments.symm)⟩
  obtain ⟨a,b,rfl⟩ := argsEq
  obtain ⟨bodyEq,outputCell⟩ := checked_output source.code installed a b out actualBody callee shape called
  rw [bodyEq] at bodyRun
  have frame := body_memory (callEntryStateHOLFinite source callee) out query outputCell away
  rw [bodyRun] at frame
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.Sha256Memory

#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Memory.supported
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Memory.body_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Memory.environment
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Memory.call_memory

#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Memory.checked_output
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Memory.call_output_memory
