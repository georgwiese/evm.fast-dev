import InitECandidate.Solver.Input.CurrentHash.PayloadBalance
import InitECandidate.Solver.Input.CurrentHash.PContainerCost

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def containerTail : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "htr_pcontainer") StaticFields.containerArguments) FixedRecord.releaseSuffix
def afterBalance : ProgHOL 64 := .seq (StaticFields.step (.scalar 532 18)) containerTail
def afterFinalScalars : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "htr_pbytes") StaticFields.balanceArguments) afterBalance

theorem container_tail_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch out : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source containerTail=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤4861 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) StaticFields.containerArguments=
      some [.val (.word ch),.val (.word 19#64),.val (.word out)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,StaticFields.containerArguments,localVar,chunks,output]
  unfold containerTail at actual
  exact ClockCost.sequence_terminating source post _ FixedRecord.releaseSuffix 4860 1
    (by intro observed target evaluated noTimeout
        exact PContainer.call_cost source target ch out 19 (by decide) installed (some none) _ args observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        have release : ClockCost.Bound source.code FixedRecord.releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
          (AllocatorCost.release_call source.code installed (some none) _) (ClockCost.returned source.code _)
        have paid := release middle ((evaluation_fields source middle _ none normal).2.2.2)
        rw [evaluated] at paid
        exact paid) result actual notTimeout

theorem after_balance_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch out : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterBalance=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤4915 := by
  unfold afterBalance at actual
  exact ClockCost.sequence_terminating source post _ containerTail 54 4861
    (by intro observed target evaluated noTimeout
        have paid := FixedHashCost.u64_call source.code installed (some none) (StaticFields.arguments (.scalar 532 18)) source rfl
        change source.clock-(evaluateHOLFiniteState source (StaticFields.step (.scalar 532 18))).2.clock≤54 at paid
        rw [evaluated] at paid
        exact paid)
    (by intro middle normal observed target evaluated noTimeout
        have code : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact installed
        have kept (name : String) := CallNormal.ignored_lookup source middle (ofString name) (ofString "htr_u64_at") (StaticFields.arguments (.scalar 532 18)) normal
        exact container_tail_cost middle target ch out code ((kept "ch").trans chunks) ((kept "out").trans output) observed evaluated noTimeout)
    result actual notTimeout

theorem State.after_final_scalars_cost {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source afterFinalScalars=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤5*balanceLength input length+8217 := by
  unfold afterFinalScalars at actual
  have paid := ClockCost.sequence_terminating source post _ afterBalance (5*balanceLength input length+3302) 4915
    (by intro observed target evaluated noTimeout; exact data.balance_cost observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        have next := data.after_balance normal
        exact after_balance_cost middle target ch out next.context.installed next.chunks next.output observed evaluated noTimeout)
    result actual notTimeout
  omega

/-- Actual last payload fields, real balance hash, nineteen-field container
and final release, including earlier observed non-timeout stopping paths. -/
theorem State.final_cost {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source finalFields=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤5*balanceLength input length+8325 := by
  rw [StaticFields.final_shape] at actual
  change evaluateHOLFiniteState source (StaticFields.program [.scalar 512 15,.scalar 520 16] afterFinalScalars)=(result,post) at actual
  have paid := StaticFields.program_cost [.scalar 512 15,.scalar 520 16] source post (blob+62#64) ch afterFinalScalars (5*balanceLength input length+8217)
    (by intro field member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl|rfl <;> trivial)
    data.context.installed data.raw data.chunks
    (by intro middle normal observed target evaluated noTimeout
        have next := data.after_static [.scalar 512 15,.scalar 520 16]
          (by intro field member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl|rfl <;> simp [StaticFields.lastFields]) normal
        exact next.after_final_scalars_cost observed evaluated noTimeout) result actual notTimeout
  change source.clock-post.clock≤108+(5*balanceLength input length+8217) at paid
  omega

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.container_tail_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.after_balance_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_final_scalars_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.final_cost
