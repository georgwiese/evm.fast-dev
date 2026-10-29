import InitECandidate.Solver.Input.CurrentVerify.HeaderProgram
import InitECandidate.Solver.Input.CallPrefixTrace
import InitECandidate.Solver.Input.CallPrefixLocals
import InitECandidate.Solver.Input.ClockCost
import InitECandidate.Solver.Input.QuietHandlerClock
import InitECandidate.Solver.Input.CurrentVerify.DataGlobals
import InitECandidate.Solver.Input.CurrentVerify.HeaderReturned

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def nodeActions : List CallPrefix.Action := (CallPrefix.cut (ofString "nodedb_build") afterHeaders).1
def nodeCall : ProgHOL 64 := (CallPrefix.cut (ofString "nodedb_build") afterHeaders).2

theorem node_reconstruct : CallPrefix.program nodeActions nodeCall=afterHeaders := CallPrefix.reconstruct _ _

set_option maxRecDepth 100000 in
theorem node_actions_data : ∀ action∈nodeActions,DataAction action := by
  simp only [nodeActions,afterHeaders,headerCall,afterPayload,body,Guest.Software.guestFn_run_attempt,progToHOL,shapeToHOL,CallPrefix.cut,if_neg (show ofString "check_gas_limit"≠ofString "nodedb_build" from by decide),↓reduceIte]
  intro action member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact .declare _ _ _ (by decide)
  · exact .decision _ (.ite _ (.raised _ _) .skip)
  · exact .declare _ _ _ (by decide)
  · exact .global _ _ (by decide)
  · exact .global _ _ (by decide)
  · exact .decision _ .skip
  · exact .decision _ (.ite _ (.raised _ _) .skip)
  · exact .gas (ofString "gas_ok") _ (by decide)
  · exact .decision _ (.ite _ (.raised _ _) .skip)

set_option maxRecDepth 100000 in
theorem node_actions_payload_local : ∀ action∈nodeActions,CallPrefix.KeepsLocal (ofString "pl") action := by
  simp only [nodeActions,afterHeaders,headerCall,afterPayload,body,Guest.Software.guestFn_run_attempt,progToHOL,shapeToHOL,CallPrefix.cut,if_neg (show ofString "check_gas_limit"≠ofString "nodedb_build" from by decide),↓reduceIte]
  intro action member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact CallPrefix.KeepsLocal.declared _ _ _ _ (by decide)
  · exact CallPrefix.KeepsLocal.decision _ _ (.ite _ (.raised _ _) .skip)
  · exact CallPrefix.KeepsLocal.declared _ _ _ _ (by decide)
  · exact CallPrefix.KeepsLocal.global_assignment _ _ _
  · exact CallPrefix.KeepsLocal.global_assignment _ _ _
  · exact CallPrefix.KeepsLocal.decision _ _ .skip
  · exact CallPrefix.KeepsLocal.decision _ _ (.ite _ (.raised _ _) .skip)
  · exact CallPrefix.KeepsLocal.scoped _ _ _ _ _ (by decide)
  · exact CallPrefix.KeepsLocal.decision _ _ (.ite _ (.raised _ _) .skip)

set_option maxRecDepth 100000 in
/-- The complete actual post-header prefix through gas validation costs at
most67 source ticks. Both block-hash writes and both gas guards are included. -/
theorem node_prefix_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code (CallPrefix.program nodeActions .skip) 67 := by
  simp only [nodeActions,afterHeaders,headerCall,afterPayload,body,Guest.Software.guestFn_run_attempt,progToHOL,shapeToHOL,CallPrefix.cut,CallPrefix.program,↓reduceIte]
  apply ClockCost.declared
  apply ClockCost.sequence (firstPrice:=0) (secondPrice:=67)
  · exact ClockCost.conditional code _ _ _ 0 0 (ClockCost.raised code _ _) (ClockCost.skip code)
  · apply ClockCost.declared
    apply ClockCost.sequence (firstPrice:=0) (secondPrice:=67)
    · exact ClockCost.of_quiet code _ (QuietClock.assign_global code _ _)
    · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=67)
      · exact ClockCost.of_quiet code _ (QuietClock.assign_global code _ _)
      · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=67)
        · exact ClockCost.skip code
        · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=67)
          · exact ClockCost.conditional code _ _ _ 0 0 (ClockCost.raised code _ _) (ClockCost.skip code)
          · apply ClockCost.scoped_body (calleePrice:=66) (continuationPrice:=0)
              (formals:=GasLimit.formals) (body:=GasLimit.body) (returnShape:=.one)
            · exact GasLimit.original_code code installed
            · exact GasLimit.body_cost code installed
            · exact ClockCost.sequence code _ _ 0 0
                (ClockCost.conditional code _ _ _ 0 0 (ClockCost.raised code _ _) (ClockCost.skip code)) (ClockCost.skip code)

/-- The genuine post-header execution stops within67ticks or exposes the
actual node-database caller, preserving all decoded witness/gas input data.
Parent reads and gas-check success are derived from this same action trace. -/
theorem node_prefix_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterHeaders=(outcome,post)) :
    source.clock-post.clock≤67 ∨ ∃ current inner,Data input current pointer si record gasWord boundary ∧
      current.locals.lookup (ofString "pl")=source.locals.lookup (ofString "pl") ∧ current.clock≤source.clock ∧ source.clock-current.clock≤67 ∧
      evaluateHOLFiniteState current nodeCall=(outcome,inner) ∧ post.clock=inner.clock ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  have price:=node_prefix_cost source.code data.arena.code source rfl
  rw [←node_reconstruct] at run
  rcases CallPrefix.priced_trace source post nodeActions nodeCall 67 price outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,cost,clock,continued⟩:=reached
    have frame:=execution.erase nodeCall
    rw [run,continued] at frame
    exact Or.inr ⟨current,inner,data.actions node_actions_data execution,execution.keeps_local _ node_actions_payload_local,forward,cost,continued,clock,frame⟩

/-- Main's actual run_attempt reaches its first Patricia database with all
input data intact, or stops within the complete current header/gas allowance.
This is an all-outcome source prefix bound, not the global target bound. -/
theorem to_nodes {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤51528390 ∨ ∃ current inner,Data input current pointer si record gasWord boundary ∧
      current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧ current.clock≤source.clock ∧ source.clock-current.clock≤51528390 ∧
      evaluateHOLFiniteState current nodeCall=(outcome,inner) ∧ post.clock=inner.clock ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  rcases header_data_trace data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨headerCurrent,headerInner,headerData,headerPayload,headerForward,headerCost,continued,clock,frame⟩:=reached
    rcases node_prefix_trace headerData outcome continued with stopped|reached
    · exact Or.inl (by omega)
    · obtain ⟨current,inner,nextData,payloadLocal,forward,cost,next,endpoint,erased⟩:=reached
      exact Or.inr ⟨current,inner,nextData,payloadLocal.trans headerPayload,by omega,by omega,next,clock.trans endpoint,frame.trans erased⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.node_actions_data
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.node_prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.node_prefix_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_nodes

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.node_actions_payload_local
