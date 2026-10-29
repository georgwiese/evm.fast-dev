import InitECandidate.Solver.Input.CurrentRlp.Code
import InitECandidate.Solver.Input.RlpLength.ListHeader
import InitECandidate.Solver.Input.LocalEffects
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.CurrentRlp.SmallSizes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive Function where | header | word | listHeader
  deriving DecidableEq

def function : Function→Code.Fn
  | .header=>.headerLength | .word=>.wordLength | .listHeader=>.listLength
def body (which : Function):=Code.body (function which)
def argument : Function→String
  | .header=>"n" | .word=>"w" | .listHeader=>"payload_len"
def price : Function→Nat
  | .header | .word=>9 | .listHeader=>10

private theorem be_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one) := by
  have known:=Code.installed source.code installed .beLength
  simpa only [Code.name,Code.formals,Code.shape,Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_be_len,RlpLength.Be.formals,RlpLength.Be.body,Guest.guestFn_rlp_be_len,
    paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using known

private theorem header_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    source.code.lookup (ofString "rlp_header_len")=some (RlpLength.Header.formals,RlpLength.Header.body,.one) := by
  have known:=Code.installed source.code installed .headerLength
  simpa only [Code.name,Code.formals,Code.shape,Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_header_len,RlpLength.Header.formals,RlpLength.Header.body,Guest.guestFn_rlp_header_len,
    paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using known

/-- Each small current scalar sizer returns a genuine length in1..9,
retaining every nonlocal field. These helper bodies perform no allocation. -/
theorem execute (which : Function) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString (argument which))=some (.val (.word word))) (funded : price which≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤price which ∧
      evaluateHOLFiniteState source (body which)=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  cases which with
  | header=>exact RlpLength.Header.execute source word cell (be_code source installed) funded
  | word=>exact RlpLength.WordSize.execute source word cell (be_code source installed) funded
  | listHeader=>exact RlpLength.ListHeader.execute source word cell (header_code source installed) (be_code source installed) funded

theorem body_cost (which : Function) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString (argument which))=some (.val (.word word))) :
    source.clock-(evaluateHOLFiniteState source (body which)).2.clock≤price which := by
  by_cases funded : price which≤source.clock
  · obtain ⟨target,encoded,paid,lower,upper,bound,run,frame⟩:=execute which source word installed cell funded
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clock
    rw [run]
    change source.clock-target.clock≤price which
    omega
  · omega

/-- The same normal-return and memory frame conclusions hold for actual
executions below the conservative entry allowance, by clock padding. -/
theorem body_normal (which : Function) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString (argument which))=some (.val (.word word)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body which)=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤price which ∧ LocalEffects.erase target=LocalEffects.erase source := by
  let padded:={source with clock:=source.clock+price which}
  obtain ⟨post,encoded,paid,lower,upper,bound,run,frame⟩:=execute which padded word installed cell (by change price which≤source.clock+price which; omega)
  have lifted:=panPropsEvaluateAddClockEq (body which) source (some (.returned value)) target (price which) ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+price which}=post at endpoint
  rw [←endpoint] at frame
  have metadata:=congrArg LocalEffects.erase frame
  have cost:=body_cost which source word installed cell
  rw [normal] at cost
  exact ⟨encoded,lower,upper,answer,cost,metadata⟩

end InitECandidate.Solver.Input.CurrentRlp.SmallSizes

#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.execute
#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.body_normal
