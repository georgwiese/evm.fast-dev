import InitECandidate.Solver.MutableTable.GetCallOrigin
import InitECandidate.Solver.GasBudget.AccountCacheProgram
import InitECandidate.Solver.MutableTable.GetExceptionPrefix
import InitECandidate.Solver.MutableTable.SetNoOtherException
import InitECandidate.Solver.Input.ExceptionControl

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- The account prefixes below cover normal returns and exceptions other
than allocator traps. This does not make an assertion about a trapped run. -/
inductive Outcome where
  | returned (value : ValueHOL 64)
  | exception (identifier : MlS) (payload : ValueHOL 64) (other : ofString "TrapErr" ≠ identifier)
def Outcome.result : Outcome → Option (PanSemResultExact 64)
  | .returned value => some (.returned value)
  | .exception identifier payload _ => some (.exception identifier payload)

theorem set_before_outcome (outcome : Outcome) (kind : Kind)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : WarmKeys.Environment source)
    (run : evaluateHOLFiniteState source kind.body = (outcome.result, post)) :
    ∃ called, evaluateHOLFiniteState source setCall = (none, called) ∧
      evaluateHOLFiniteState called kind.afterSet = (outcome.result, post) := by
  rw [kind.body_shape] at run
  cases outcome with
  | returned value =>
    have safe : Input.LocalPrefix (ofString "addr") setCall := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨called, setRun, tailRun, saved⟩ := safe.normal_continue source post kind.afterSet value run
    exact ⟨called, setRun, tailRun⟩
  | exception identifier payload other =>
    rcases Input.sequence_exception source post setCall kind.afterSet identifier payload run with failed | continued
    · have safe := Input.NoNamedException.call_body source.code identifier (ofString "htab_set") setArguments
        TableCall.formals Set.body .one environment.setCode (SetNoOtherException.set_safe source environment identifier other)
      exact (safe source rfl payload (congrArg Prod.fst failed)).elim
    · exact continued

theorem getter_before_outcome_origin (outcome : Outcome) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (run : evaluateHOLFiniteState source (.decCall (ofString name) Get.pairShape (ofString "htab_get") arguments continuation) = (outcome.result, post)) :
    ∃ paid flag value inner, 1 ≤ paid ∧ paid ≤ Get.bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      Get.ValueOrigin source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) flag value (fun slot=>slot.toNat∈slots) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (Get.pair flag value) {source with clock := source.clock - paid}) continuation = (outcome.result, inner) ∧
      post = restore source name inner := by
  cases outcome with
  | returned value =>
    exact Get.model_normal_entry_origin source post kind plan slots cursor floor table environment query queryFits queryMapped getCode name arguments continuation args value run
  | exception identifier payload other =>
    exact Get.model_exception_prefix_origin source post kind plan slots cursor floor table environment query queryFits queryMapped getCode name arguments continuation args identifier payload run

theorem getter_before_outcome (outcome : Outcome) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (run : evaluateHOLFiniteState source (.decCall (ofString name) Get.pairShape (ofString "htab_get") arguments continuation) = (outcome.result, post)) :
    ∃ paid flag value inner, 1 ≤ paid ∧ paid ≤ Get.bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (Get.pair flag value) {source with clock := source.clock - paid}) continuation = (outcome.result, inner) ∧
      post = restore source name inner := by
  obtain ⟨paid, flag, value, inner, positive, bounded, funded, binary, _, tailRun, scope⟩ :=
    getter_before_outcome_origin outcome source post kind plan slots cursor floor table environment query queryFits queryMapped
      getCode name arguments continuation args run
  exact ⟨paid, flag, value, inner, positive, bounded, funded, binary, tailRun, scope⟩

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.set_before_outcome
#print axioms InitECandidate.Solver.GasBudget.AccountCache.getter_before_outcome_origin
#print axioms InitECandidate.Solver.GasBudget.AccountCache.getter_before_outcome
