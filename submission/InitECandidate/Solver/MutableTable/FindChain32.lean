import InitECandidate.Solver.MutableTable.FindStep32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

noncomputable def usedByte (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64) : Option UInt8:=
  @panMemLoadByteHOL 64 _ source.memory source.memaddrs
    (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (p.used+index)

/-- Actual immutable memory along one masked probe path. Occupied prefixes
terminate at an empty byte; construction/order invariants must supply a chain. -/
inductive Chain32 (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) : BitVec 64→Nat→Type where
  | empty (index : BitVec 64) (loaded : usedByte snapshot p index=some 0) : Chain32 snapshot p index 0
  | occupied (index : BitVec 64) (key : WitnessRadix.ByteKeys.Key) (length : Nat)
      (loaded : usedByte snapshot p index=some 1)
      (view : WitnessRadix.MemoryBytes.ByteView snapshot (p.keys+index*p.stride) key)
      (fits : (p.keys+index*p.stride).toNat+32<2^64)
      (tail : Chain32 snapshot p (next p index) length) : Chain32 snapshot p index (length+1)

noncomputable def answer {snapshot : PanSemStateFiniteExact 64 Guest.HostMemory} {p : Parameters}
    {index : BitVec 64} {length : Nat} (chain : Chain32 snapshot p index length) (query : WitnessRadix.ByteKeys.Key) : Option (BitVec 64):=
  match chain with
  | .empty _ _=>none
  | .occupied index key _ _ _ _ tail=>if key=query then some index else answer tail query

def answerResult (value : Option (BitVec 64)) : Option (PanSemResultExact 64):=
  value.map (fun index=>.returned (.val (.word index)))

theorem usedByte_of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be) :
    usedByte source p index=usedByte target p index:=
  WitnessRadix.MemoryBytes.read_of_fields source target memory domain endian _

/-- Each occupied probe pays at most five comparator/call clocks and one
while clock. This runs the actual original lookup loop from a real byte chain. -/
theorem chain32_execute (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (index : BitVec 64) (length : Nat) (chain : Chain32 snapshot p index length)
    (query : WitnessRadix.ByteKeys.Key) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (locals : Locals source p index) (keyLength : p.keyLength=32#64)
    (memory : snapshot.memory=source.memory) (domain : snapshot.memaddrs=source.memaddrs) (endian : snapshot.be=source.be)
    (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query) (queryFits : p.key.toNat+32<2^64)
    (little : source.be=false)
    (code : source.code.lookup (ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (enough : 6*length≤source.clock) :
    ∃ paid target,paid≤6*length ∧ evaluateHOLFiniteState source loop=(answerResult (answer chain query),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      (answer chain query=none→target.locals.lookup (ofString "cap")=some (.val (.word p.capacity))) := by
  classical
  induction chain generalizing source with
  | empty index loaded=>
    have actual : usedByte source p index=some 0 := by rw [← usedByte_of_fields snapshot source p index memory domain endian];exact loaded
    have test:=condition_read source p index locals 0 actual
    refine ⟨0,source,by simp,?_,by simp,?_⟩
    · rw [loop,evaluateHOLFiniteState_while_total]
      simp only [eval,evalHOLFinite] at test ⊢
      rw [test]
      simp [answer,answerResult]
    · intro _;exact locals.cap
  | occupied index key length loaded view fits tail ih=>
    let entry:=decClockHOLFinite source
    have entryLocals : Locals entry p index:=⟨locals.cap,locals.klen,locals.stride,locals.keys,locals.used,locals.key,locals.index⟩
    have actual : usedByte source p index=some 1 := by rw [← usedByte_of_fields snapshot source p index memory domain endian];exact loaded
    have test:=condition_read source p index locals 1 actual
    have entryView:=WitnessRadix.MemoryBytes.byteView_of_fields snapshot entry memory domain endian _ _ view
    have queryEntry:=WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ queryView
    obtain ⟨stepPaid,post,bound,stepRun,stepFrame,advance⟩:=step32 entry p index entryLocals keyLength key query entryView queryEntry fits queryFits little code
      (by change 5≤source.clock-1;omega)
    have stepClock:=congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory=>s.clock) stepFrame
    change post.clock=source.clock-1-stepPaid at stepClock
    have fixed : fixClockHOLFinite entry ((if key=query then some (PanSemResultExact.returned (.val (.word index))) else none),post)=
        ((if key=query then some (PanSemResultExact.returned (.val (.word index))) else none),post):=
      WitnessRadix.StateSteps.fixed_clock entry post _ (by change post.clock≤source.clock-1;omega)
    have unfolded := evaluateHOLFiniteState_while_total source condition loopBody
    simp only [eval,evalHOLFinite] at test unfolded
    rw [test] at unfolded
    simp only [show (1 : UInt8).toNat≠0 by decide,show (1#64)≠0#64 by decide,↓reduceIte] at unfolded
    change evaluateHOLFiniteState source loop=(if source.clock=0 then _ else _) at unfolded
    rw [if_neg (by omega),stepRun,fixed] at unfolded
    by_cases same : key=query
    · rw [if_pos same] at unfolded
      refine ⟨stepPaid+1,post,by omega,?_,?_,?_⟩
      · simpa [answer,answerResult,same] using unfolded
      · have subtract : source.clock-1-stepPaid=source.clock-(stepPaid+1):=by omega
        simpa only [entry,decClockHOLFinite,subtract] using stepFrame
      · simp [answer,same]
    · rw [if_neg same] at unfolded
      have postEq:=advance same
      rw [postEq] at unfolded
      let nextState:=bind {entry with clock:=entry.clock-stepPaid} "i" (next p index)
      have nextLocals : Locals nextState p (next p index) := by
        constructor
        · exact (bind_lookup_other _ "i" "cap" _ (by decide)).trans locals.cap
        · exact (bind_lookup_other _ "i" "klen" _ (by decide)).trans locals.klen
        · exact (bind_lookup_other _ "i" "stride" _ (by decide)).trans locals.stride
        · exact (bind_lookup_other _ "i" "keys" _ (by decide)).trans locals.keys
        · exact (bind_lookup_other _ "i" "used" _ (by decide)).trans locals.used
        · exact (bind_lookup_other _ "i" "key" _ (by decide)).trans locals.key
        · exact bind_lookup_same _ _ _
      have queryNext:=WitnessRadix.MemoryBytes.byteView_of_fields source nextState rfl rfl rfl _ _ queryView
      obtain ⟨paid,target,paidBound,recursive,frame,cap⟩:=ih nextState nextLocals memory domain endian queryNext little code
        (by change 6*length≤source.clock-1-stepPaid;omega)
      refine ⟨paid+stepPaid+1,target,by omega,?_,?_,?_⟩
      · change evaluateHOLFiniteState source loop=evaluateHOLFiniteState nextState loop at unfolded
        rw [unfolded,recursive]
        simp only [answer,if_neg same]
      · have subtract : source.clock-1-stepPaid-paid=source.clock-(paid+stepPaid+1):=by omega
        simpa only [nextState,entry,decClockHOLFinite,WitnessRadix.QueryBranch.bind,setVarHOLFinite,emptyLocalsHOLFinite,subtract] using frame
      · intro absent
        apply cap
        simpa only [answer,if_neg same] using absent

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.usedByte_of_fields
#print axioms InitECandidate.Solver.MutableTable.Find.chain32_execute
