import InitECandidate.Solver.Input.LiteralMemoryFrame
import InitECandidate.Solver.Input.ShaGlobals

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def initializeFields : List (Nat×BitVec 64) := [(0,1779033703#64),(8,3144134277#64),(16,1013904242#64),(24,2773480762#64),
  (32,1359893119#64),(40,2600822924#64),(48,528734635#64),(56,1541459225#64)]

theorem initialize_store_shape : initializeBody=MemoryAt.literalStores "stp" initializeFields := by
  simp only [initializeBody,Guest.guestFn_sha256_state_init,progToHOL,expToHOL,List.map_cons,List.map_nil,initializeFields,MemoryAt.literalStores,localVar]

theorem initialize_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 64)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source initializeBody=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [initialize_store_shape] at run
  apply MemoryAt.literal_stores_returned initializeFields source post "stp" pointer query cell _ value run
  intro entry member
  have offset : entry.1<64 := by
    simp only [initializeFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (away entry.1 offset).1

theorem initialize_environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer : BitVec 64)
    (code : codeFn (ofString "sha256_state_init")=some (initializeFormals,initializeBody,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "sha256_state_init") [.val (.word pointer)]=some (initializeBody,callee,.one) ∧
      callee.lookup (ofString "stp")=some (.val (.word pointer)) := by
  let locals : MlS→Option (ValueHOL 64) := fun name=>if name=ofString "stp" then some (.val (.word pointer)) else none
  have raw : lookupCodeHOLExact codeFn (ofString "sha256_state_init") [.val (.word pointer)]=some (initializeBody,locals,.one) := by
    simp [lookupCodeHOLExact,code,initializeFormals,shapeEqHOL,shapeOfHOLExact]
    rfl
  obtain ⟨callee,called,cells⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [cells]; simp [locals]⟩

/-- Actual normal original SHA initialization changes only its eight
state words, independently of their initial contents or hash outputs. -/
theorem initialize_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer)])
    (away : CopyGeneral.Away pointer query 64)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_state_init") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,cell⟩ := initialize_environment source.code.lookup pointer (initialize_code source.code installed)
  exact MemoryAt.call_normal source post (ofString "sha256_state_init") arguments [.val (.word pointer)] initializeBody callee .one query args called
    (fun target value evaluated=>initialize_memory (callEntryStateHOLFinite source callee) target pointer query cell away value evaluated) run

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.initialize_store_shape
#print axioms InitECandidate.Solver.Input.ShaFixedCost.initialize_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.initialize_environment
#print axioms InitECandidate.Solver.Input.ShaFixedCost.initialize_call_memory
