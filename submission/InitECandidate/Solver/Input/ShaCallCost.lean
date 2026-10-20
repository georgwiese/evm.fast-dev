import InitECandidate.Solver.Input.ShaBlockCost
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
set_option maxRecDepth 100000

def initializeFormals : List (MlS×ShapeHOL) := [(ofString "stp",.one)]
def finishFormals : List (MlS×ShapeHOL) := [(ofString "stp",.one),(ofString "out",.one)]
def blockFormals : List (MlS×ShapeHOL) := [(ofString "stp",.one),(ofString "blk",.one)]

theorem initialize_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "sha256_state_init")=some (initializeFormals,initializeBody,.one) := by
  have checked := OriginalCode.indexed code installed 84 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_sha256_state_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,initializeFormals,initializeBody,Guest.guestFn_sha256_state_init,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem finish_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "sha256_finish")=some (finishFormals,finishBody,.one) := by
  have checked := OriginalCode.indexed code installed 86 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_sha256_finish) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,finishFormals,finishBody,Guest.guestFn_sha256_finish,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem block_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "sha256_block")=some (blockFormals,blockBody,.one) := by
  have checked := OriginalCode.indexed code installed 85 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_sha256_block) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,blockFormals,blockBody,Guest.guestFn_sha256_block,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem initialize_call_price (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "sha256_state_init") arguments) 1 :=
  ClockCost.call_body code destination _ arguments initializeFormals initializeBody .one 0 (initialize_code code installed) (initialize_price code)

theorem finish_call_price (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "sha256_finish") arguments) 17 :=
  ClockCost.call_body code destination _ arguments finishFormals finishBody .one 16 (finish_code code installed) (finish_price code installed)

def blockValues (stp block : BitVec 64) : List (ValueHOL 64) := [.val (.word stp),.val (.word block)]
def blockLocals (stp block : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "blk" then some (.val (.word block)) else if name=ofString "stp" then some (.val (.word stp)) else none

theorem block_environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (stp block : BitVec 64)
    (code : codeFn (ofString "sha256_block")=some (blockFormals,blockBody,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "sha256_block") (blockValues stp block)=some (blockBody,callee,.one) ∧
      callee.lookup (ofString "blk")=some (.val (.word block)) := by
  have valid : (blockFormals.map Prod.fst).Nodup ∧ blockFormals.length=(blockValues stp block).length ∧
      ((blockFormals.zip (blockValues stp block)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [blockFormals,blockValues,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "sha256_block") (blockValues stp block)=some (blockBody,blockLocals stp block,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [blockLocals]⟩

/-- Actual original SHA block caller costs at most18 source ticks, deriving
its real ABI/callee bindings. Current workspace/input mapping suffices. -/
theorem block_call_price_current (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp block accel : BitVec 64)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (blockValues stp block))
    (workspace : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (blockArena : AllocatedBytes.Arena block 64) (workspaceArena : AllocatedBytes.Arena (accel+32#64) 64) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "sha256_block") arguments)).2.clock≤18 := by
  obtain ⟨callee,called,blockLocal⟩ := block_environment source.code.lookup stp block (block_code source.code installed)
  have cost := block_price_current (callEntryStateHOLFinite source callee) block accel installed blockLocal workspace domain blockArena workspaceArena
  exact ClockCost.call_current source destination (ofString "sha256_block") arguments (blockValues stp block) blockBody callee .one 17 args called cost

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.initialize_code
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_code
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_code
#print axioms InitECandidate.Solver.Input.ShaFixedCost.initialize_call_price
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_call_price
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_environment
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_call_price_current
