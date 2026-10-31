import InitECandidate.Solver.Input.CurrentRlp.Code
import InitECandidate.Solver.Input.RlpLength.ListHeader
import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.CallPrefixScopedActual
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

/-- Exact real list-header result with its original all-outcome allowance.
Clock padding handles normal executions below that conservative allowance. -/
theorem list_header_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString "payload_len")=some (.val (.word word)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body .listHeader)=(some (.returned value),target)) :
    ∃ encoded,encoded=RlpLength.Header.encodedLength word ∧ 1≤encoded ∧ encoded≤9 ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ source.clock-target.clock≤10 ∧ LocalEffects.erase target=LocalEffects.erase source := by
  let padded:={source with clock:=source.clock+10}
  obtain ⟨post,encoded,paid,exactCount,lower,upper,bound,run,frame⟩:=RlpLength.ListHeader.execute_exact padded word cell
    (header_code padded installed) (be_code padded installed) (by change 10≤source.clock+10; omega)
  change evaluateHOLFiniteState padded (body .listHeader)=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),post) at run
  have lifted:=panPropsEvaluateAddClockEq (body .listHeader) source (some (.returned value)) target 10 ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+10}=post at endpoint
  rw [←endpoint] at frame
  have metadata:=congrArg LocalEffects.erase frame
  have cost:=body_cost .listHeader source word installed cell
  rw [normal] at cost
  exact ⟨encoded,exactCount,lower,upper,answer,cost,metadata⟩

theorem list_header_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_list_header_len")=some (RlpLength.ListHeader.formals,body .listHeader,.one) := by
  apply Code.installed_as code installed .listLength
  simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_rlp_list_header_len,RlpLength.ListHeader.formals,body,function,Code.body,shapeToHOL,paramToHOL,List.map_cons,List.map_nil]

/-- The actual checked scoped length call delivers its exact header size,
restored caller state and at-most-eleven source ticks. -/
theorem scoped_list_header_normal_exact {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (word : BitVec 64) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word word)])
    (reached : CallPrefix.Reaches source (.scoped name .one (ofString "rlp_list_header_len") arguments) current) :
    ∃ encoded,encoded=RlpLength.Header.encodedLength word ∧ 1≤encoded ∧ encoded≤9 ∧
      current.locals.lookup name=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      (∀ other,name≠other→current.locals.lookup other=source.locals.lookup other) ∧
      LocalEffects.erase current=LocalEffects.erase source ∧ source.clock-current.clock≤11 := by
  obtain ⟨callee,called,cell⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_list_header_len") "payload_len" (body .listHeader) word (list_header_code source.code installed)
  obtain ⟨post,returned,run,endpoint⟩:=reached.scoped_known name .one (ofString "rlp_list_header_len") arguments [.val (.word word)] (body .listHeader) callee .one args called
  obtain ⟨encoded,exactCount,lower,upper,answer,price,frame⟩:=list_header_normal_exact (callEntryStateHOLFinite source callee) post word installed cell returned run
  refine ⟨encoded,exactCount,lower,upper,?_,?_,?_,?_⟩
  · rw [endpoint]; simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
  · intro other different
    rw [endpoint]; simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  · rw [endpoint]; exact frame
  · rw [endpoint]
    change source.clock-1-post.clock≤10 at price
    change source.clock-post.clock≤11
    have funded:=reached.scoped_funded
    omega

end InitECandidate.Solver.Input.CurrentRlp.SmallSizes

#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.execute
#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.body_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.list_header_normal_exact
#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.list_header_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.SmallSizes.scoped_list_header_normal_exact
