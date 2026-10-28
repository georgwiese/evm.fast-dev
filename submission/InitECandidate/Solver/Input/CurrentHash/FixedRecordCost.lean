import InitECandidate.Solver.Input.CurrentHash.FixedRecordSteps
import InitECandidate.Solver.Input.CurrentHash.MerkleCallCost
import InitECandidate.Solver.Input.CurrentHash.StraightCost
import InitECandidate.Solver.Input.ClockCostScalarTerminating
import InitECandidate.Solver.Input.WordPairEnvironment

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.FixedRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def Kind.tailPrice (kind : Kind) := 88*kind.count+4*kind.depth+50
def Kind.price (kind : Kind) := (kind.steps.map Step.price).sum+kind.tailPrice+3

theorem pipeline_prefix (key : MlS) (inputName : String) (steps : List Step) :
    LocalPrefix key (pipeline inputName steps .skip) := by
  induction steps with
  | nil => exact .skip
  | cons step rest ih => exact .seq (.call none _ _ (by intro name impossible; cases impossible)) ih

theorem after_steps_cost (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch out : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (chunks : source.locals.lookup (ofString "ch") = some (.val (.word ch)))
    (output : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source kind.afterSteps = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ kind.tailPrice := by
  have number : (BitVec.ofNat 64 kind.count).toNat = kind.count := by cases kind <;> decide
  have bound : kind.count ≤ 2^kind.depth := by cases kind <;> decide
  have small : kind.depth < 58 := by cases kind <;> decide
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) kind.merkleArguments =
      some (Merkle.values ch (BitVec.ofNat 64 kind.count) (BitVec.ofNat 64 kind.count) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,Kind.merkleArguments,localVar,chunks,output,Merkle.values]
  unfold Kind.afterSteps at actual
  have paid := ClockCost.sequence_terminating source post _ releaseSuffix (88*kind.count+4*kind.depth+49) 1
    (by intro result target evaluated notTimeout
        have price := MerkleCallCost.cost source target ch (BitVec.ofNat 64 kind.count) (BitVec.ofNat 64 kind.count) out kind.depth small
          (by rw [number]; exact bound) (by rw [number]; exact bound) installed (some none) kind.merkleArguments args result evaluated notTimeout
        simpa only [number] using price)
    (by intro middle normal result target evaluated notTimeout
        have suffix : ClockCost.Bound source.code releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
          (AllocatorCost.release_call source.code installed (some none) _) (ClockCost.returned source.code _)
        have price := suffix middle ((evaluation_fields source middle _ none normal).2.2.2)
        rw [evaluated] at price
        exact price) result actual notTimeout
  exact Nat.le_trans paid (by unfold Kind.tailPrice; omega)

theorem after_allocation_cost (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString kind.inputName) = some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch") = some (.val (.word ch)))
    (output : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source kind.afterAllocation = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ (kind.steps.map Step.price).sum+kind.tailPrice := by
  exact pipeline_cost kind.steps kind.inputName kind.afterSteps kind.tailPrice (steps_valid kind) source post p ch installed pointer chunks
    (by intro middle normal result target evaluated notTimeout
        have kept (name : MlS) : middle.locals.lookup name = source.locals.lookup name := by
          have summary := (pipeline_prefix name kind.inputName kind.steps).summary_full source
          unfold LocalSummary at summary
          rw [normal] at summary
          exact summary.1 rfl
        have nextCode : OriginalCode.Installed middle.code := by
          rw [(evaluation_fields source middle _ none normal).2.2.2]
          exact installed
        exact after_steps_cost kind middle target ch out nextCode ((kept _).trans chunks) ((kept _).trans output) result evaluated notTimeout)
    result actual notTimeout

theorem after_mark_cost (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString kind.inputName) = some (.val (.word p)))
    (output : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source kind.afterMark = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ (kind.steps.map Step.price).sum+kind.tailPrice+2 := by
  unfold Kind.afterMark at actual
  have paid := ClockCost.scalar_scope_terminating source post "ch" (ofString "alloc") kind.allocationArguments
    PersistentAlloc.formals PersistentAlloc.body kind.afterAllocation .one 1 ((kind.steps.map Step.price).sum+kind.tailPrice)
    (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed)
    (by intro target ch codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "ch" (.val (.word ch))
        have kept (name : String) (different : ofString "ch" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "ch" name ch different
        have nextCode : OriginalCode.Installed entry.code := by
          change OriginalCode.Installed target.code
          rw [codeEq]
          exact installed
        exact after_allocation_cost kind entry final p ch out nextCode
          ((kept kind.inputName (by cases kind <;> decide)).trans pointer) (bind_lookup_same _ _ _)
          ((kept "out" (by decide)).trans output) result evaluated notTimeout) result actual notTimeout
  omega

/-- Six actual fixed-record hashes, with same-trace non-timeout failures and
arbitrary input/output pointers. No obsolete accelerator or geometry premises. -/
theorem body_cost (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString kind.inputName) = some (.val (.word p)))
    (output : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source kind.body = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ kind.price := by
  rw [body_shape] at actual
  have paid := ClockCost.scalar_scope_terminating source post "mark" (Code.name .heap_mark) [] (Code.formals .heap_mark)
    (Code.body .heap_mark) kind.afterMark (Code.shape .heap_mark) 0 ((kind.steps.map Step.price).sum+kind.tailPrice+2)
    (Code.installed source.code installed .heap_mark)
    (StraightCost.body source.code .heap_mark (StraightCost.basic_supported .heap_mark (by simp)))
    (by intro target mark codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "mark" (.val (.word mark))
        have kept (name : String) (different : ofString "mark" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "mark" name mark different
        have nextCode : OriginalCode.Installed entry.code := by
          change OriginalCode.Installed target.code
          rw [codeEq]
          exact installed
        exact after_mark_cost kind entry final p out nextCode ((kept kind.inputName (by cases kind <;> decide)).trans pointer)
          ((kept "out" (by decide)).trans output) result evaluated notTimeout) result actual notTimeout
  exact Nat.le_trans paid (by unfold Kind.price; omega)

theorem call_cost (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (scalarValues p out))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) kind.name arguments) = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ kind.price+1 := by
  obtain ⟨callee,called,pointer,output⟩ := word_pair_environment source.code.lookup kind.name (ofString kind.inputName) (ofString "out")
    kind.body .one p out (by cases kind <;> decide) (original_code kind source.code installed)
  exact ClockCost.call_current_terminating source post destination kind.name arguments (scalarValues p out) kind.body callee .one kind.price args called
    (fun result target evaluated notTimeout => body_cost kind (callEntryStateHOLFinite source callee) target p out installed pointer output result evaluated notTimeout)
    result actual notTimeout

/-- Kernel-evaluated prices for the actual fixed field pipelines. -/
theorem fixed_prices : Kind.withdrawal.price=758 ∧ Kind.deposit.price=1425 ∧ Kind.wdreq.price=880 ∧
    Kind.cons.price=1144 ∧ Kind.bdep.price=1279 ∧ Kind.bexit.price=734 := by decide

end InitECandidate.Solver.Input.CurrentHash.FixedRecord

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.pipeline_prefix
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.after_steps_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.after_allocation_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.body_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.call_cost

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.fixed_prices
