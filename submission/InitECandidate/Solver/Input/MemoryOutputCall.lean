import InitECandidate.Solver.Input.WordTripleLookup
import InitECandidate.Solver.Input.MemoryNormal

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real normal three-argument call inherits a body memory frame when its
last output pointer is known. The other argument expressions are unrestricted. -/
theorem call_last_word_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function firstName secondName lastName : MlS) (body : ProgHOL 64) (shape : ShapeHOL)
    (left right output : ExpHOL 64) (out query : BitVec 64)
    (known : source.code.lookup function=some ([(firstName,.one),(secondName,.one),(lastName,.one)],body,shape))
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) output=some (.val (.word out)))
    (frame : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64), ∀ target value,
      callee.lookup lastName=some (.val (.word out)) →
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target) → target.memory query=source.memory query)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) function [left,right,output])=(none,post)) : post.memory query=source.memory query := by
  classical
  obtain ⟨positive,args,actualBody,callee,actualShape,target,value,arguments,called,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post function [left,right,output] actual
  have argsEq : ∃ a b, args=[a,b,.val (.word out)] := by
    simp only [evalHOLFinite] at read
    change evalListHOLExact source.toExact [left,right,output]=some args at arguments
    cases leftRead : evalHOLExact source.toExact left with
    | none => simp [evalListHOLExact,leftRead] at arguments
    | some a =>
      cases rightRead : evalHOLExact source.toExact right with
      | none => simp [evalListHOLExact,leftRead,rightRead] at arguments
      | some b => exact ⟨a,b,Option.some.inj (by simpa [evalListHOLExact,leftRead,rightRead,read] using arguments.symm)⟩
  obtain ⟨a,b,rfl⟩ := argsEq
  obtain ⟨bodyEq,outputCell⟩ := checked_triple_last source.code.lookup function firstName secondName lastName body shape a b out known actualBody callee actualShape called
  rw [bodyEq] at bodyRun
  have memory := frame callee target value outputCell bodyRun
  rw [endpoint]
  exact memory

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.call_last_word_memory
