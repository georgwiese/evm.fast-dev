import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionScopeCost
import InitECandidate.Solver.Input.CurrentHash.PayloadExtra

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem State.middle_fields_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source (StaticFields.program StaticFields.middleFields transactionScope)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤transactionTailPrice input length start size+87 := by
  have members : ∀ field∈StaticFields.middleFields,field∈StaticFields.firstFields++StaticFields.middleFields++StaticFields.lastFields := by intro field member; simp [member]
  have paid := StaticFields.program_cost StaticFields.middleFields source post (blob+62#64) ch transactionScope (transactionTailPrice input length start size+3)
    (by intro field member; exact (StaticFields.fields_valid field (members field member)).1) data.context.installed data.raw data.chunks
    (by intro middle normal observed target evaluated noTimeout
        have next := data.after_static (post:=middle) StaticFields.middleFields members normal
        exact next.transaction_cost (post:=target) observed evaluated noTimeout) result actual notTimeout
  rw [StaticFields.field_prices.2.1] at paid
  have arithmetic : ∀ k : Nat,84+(k+3)≤k+87 := by intro k; omega
  exact Nat.le_trans paid (arithmetic _)

def afterFirstFields : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "htr_bytes_list") StaticFields.extraArguments) (StaticFields.program StaticFields.middleFields transactionScope)

theorem State.after_first_fields_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterFirstFields=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤transactionTailPrice input length start size+357 := by
  unfold afterFirstFields at actual
  have paid : source.clock-post.clock≤270+(transactionTailPrice input length start size+87) := ClockCost.sequence_terminating source post _ _ 270 (transactionTailPrice input length start size+87)
    (by intro observed target evaluated noTimeout; exact data.extra_cost (post:=target) observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        have next := data.after_extra (post:=middle) normal
        exact next.middle_fields_cost (post:=target) observed evaluated noTimeout) result actual notTimeout
  have arithmetic : ∀ k : Nat,270+(k+87)≤k+357 := by intro k; omega
  exact Nat.le_trans paid (arithmetic _)

/-- Whole current payload continuation after its real nineteen-chunk
allocation. All actual field reads, dynamic hashes and earlier stops are joined. -/
theorem State.prefix_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source PayloadHash.afterChunks=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤transactionTailPrice input length start size+2025 := by
  have members : ∀ field∈StaticFields.firstFields,field∈StaticFields.firstFields++StaticFields.middleFields++StaticFields.lastFields := by intro field member; simp [member]
  rw [StaticFields.prefix_shape] at actual
  change evaluateHOLFiniteState source (StaticFields.program StaticFields.firstFields afterFirstFields)=(result,post) at actual
  have paid := StaticFields.program_cost StaticFields.firstFields source post (blob+62#64) ch afterFirstFields (transactionTailPrice input length start size+357)
    (by intro field member; exact (StaticFields.fields_valid field (members field member)).1) data.context.installed data.raw data.chunks
    (by intro middle normal observed target evaluated noTimeout
        have next := data.after_static (post:=middle) StaticFields.firstFields members normal
        exact next.after_first_fields_cost (post:=target) observed evaluated noTimeout) result actual notTimeout
  rw [StaticFields.field_prices.1] at paid
  have arithmetic : ∀ k : Nat,1668+(k+357)≤k+2025 := by intro k; omega
  exact Nat.le_trans paid (arithmetic _)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.middle_fields_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_first_fields_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.prefix_cost
