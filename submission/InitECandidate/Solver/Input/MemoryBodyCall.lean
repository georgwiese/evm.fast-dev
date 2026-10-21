import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A normal caller of an original body that preserves a word for every
callee environment inherits that frame. The same actual ABI lookup derives
which body ran; no argument-read or future callee success is assumed. -/
theorem call_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS×ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL) (query : BitVec 64)
    (code : source.code.lookup function=some (formals,body,shape))
    (frame : ∀ entry target : PanSemStateFiniteExact 64 Guest.HostMemory,∀ value,evaluateHOLFiniteState entry body=(some (.returned value),target) → target.memory query=entry.memory query)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post function arguments run
  have raw := lookupCodeHOLFinite_eq_some source.code.lookup function actualValues actualBody actualCallee actualShape actualCalled
  simp only [lookupCodeHOLExact,code] at raw
  split at raw
  · have bodyEq : body=actualBody := congrArg Prod.fst (Option.some.inj raw)
    rw [←bodyEq] at bodyRun
    have preserved := frame (callEntryStateHOLFinite source actualCallee) target returned bodyRun
    rw [endpoint]
    exact preserved
  · cases raw

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.call_body_normal
