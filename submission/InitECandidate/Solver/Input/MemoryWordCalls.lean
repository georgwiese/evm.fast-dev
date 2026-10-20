import InitECandidate.Solver.GasBudget.Be32Call
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "v",.one)]
def rawLocals (pointer value : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "v" then some (.val (.word value)) else if name = ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (function : MlS) (body : ProgHOL 64) (pointer value : BitVec 64)
    (code : codeFn function = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn function [.val (.word pointer),.val (.word value)] = some (body,callee,.one) ∧
      callee.lookup (ofString "p") = some (.val (.word pointer)) ∧ callee.lookup (ofString "v") = some (.val (.word value)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = ([.val (.word pointer),.val (.word value)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word pointer),.val (.word value)]).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn function [.val (.word pointer),.val (.word value)] = some (body,rawLocals pointer value,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn function _ body _ .one raw
  refine ⟨callee,called,?_,?_⟩
  · rw [locals]
    simp [rawLocals,show ofString "p" ≠ ofString "v" from by decide]
  · rw [locals]
    simp [rawLocals]

/-- Current mapped bytes give the actual fixed32-bit writer call, including
its caller clock and precise ordered partial-word updates. -/
theorem be32_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some [.val (.word pointer),.val (.word value)])
    (mapped : ∀ clause ∈ GasBudget.Be32Stores.clauses,source.memaddrs (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 clause.1)))
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be32") arguments) =
      (none,{source with memory := GasBudget.Be32Stores.written source.memory source.be pointer value GasBudget.Be32Stores.clauses,clock := source.clock - 1}) := by
  obtain ⟨callee,called,p,v⟩ := environment source.code.lookup (ofString "st_be32") GasBudget.MemoryWriter.Kind.be32.body pointer value (GasBudget.Be32Stores.original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := GasBudget.Be32Stores.execute entry pointer value GasBudget.Be32Stores.clauses p v
    (by intro clause member; simp only [GasBudget.Be32Stores.clauses,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl | rfl | rfl <;> decide) mapped
  rw [← GasBudget.Be32Stores.original_body] at run
  exact evaluateHOLFiniteState_call_return_caller_locals source none (ofString "st_be32") arguments [.val (.word pointer),.val (.word value)] _ callee .one
    (.val (.word 0#64)) _ args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.environment
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.be32_execute
