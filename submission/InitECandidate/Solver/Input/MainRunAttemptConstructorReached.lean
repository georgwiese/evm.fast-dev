import InitECandidate.Solver.Input.MainRunAttemptData
import InitECandidate.Solver.Input.RunAttemptStateFields
import InitECandidate.Solver.Input.RunAttemptConstructorInputs

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessConstructors

abbrev countWord (input : Guest.InputBlob) := BitVec.ofNat 64 (HeaderSlices.count input)
abbrev initialHeap (root : BitVec 64) := PersistentAlloc.rounded root 32#64
abbrev hashArray (input : Guest.InputBlob) (root : BitVec 64) := Headers.Validate.hashesPointer (initialHeap root) (countWord input)
abbrev validatorEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) := RunAttempt.headerEntry source (PayloadPrefix.cursor input)
abbrev parentSource (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (root : BitVec 64) :=
  CallNormal.continuationEntry (validatorEntry source input) target "vh" (Headers.Validate.result (initialHeap root) (hashArray input root))

theorem parentSource_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (root : BitVec 64) :
    (parentSource source target input root).memory=target.memory := CallNormal.continuation_memory _ _ _ _

theorem parentSource_clock (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (root : BitVec 64) :
    (parentSource source target input root).clock=target.clock := CallNormal.continuation_clock _ _ _ _

def headerPrice (input : Guest.InputBlob) := Headers.Validate.bodyPrice (countWord input) (input.length%2^64)+1
def tablesPrice (input : Guest.InputBlob) := MutableTable.WitnessBuild.bodyPrice (nodeSlices input) (nodeCount input)+1+
  MutableTable.WitnessBuild.bodyPrice (codeSlices input) (codeCount input)+1
def price (input : Guest.InputBlob) := headerPrice input+tablesPrice input

/-- A concrete real continuation after both original database calls. Its
returned tables retain the actual input-dependent collision histories,
with the original caller states, clocks and every lexical restoration. -/
def Reached (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (outcome : Option (PanSemResultExact 64)) : Prop :=
  ∃ headerTarget parent nodeTarget codeTarget codeArray heap codeTable inner,
    let afterHeader:=parentSource source headerTarget input root
    let ready:=RunAttempt.constructorEntry afterHeader (countWord input) (hashArray input root) parent
    MutableTable.WitnessBuild.Returned ready nodeTarget (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) heap (nodeCount input) (nodeSlices input)
      2713714976#64 2713715176#64 2713717584#64 ∧
    MutableTable.WitnessBuild.Returned (RunAttempt.codeEntry ready nodeTarget heap) codeTarget (VarList.decodedArray codeArray (codeBytes input)) codeTable (codeCount input) (codeSlices input)
      2713714976#64 2713715176#64 2713717584#64 ∧
    MutableTable.WitnessBuild.Database codeTarget (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) heap (nodeCount input) 1024 (nodeSlices input) 2713717584#64 ∧
    MutableTable.WitnessBuild.Database codeTarget (VarList.decodedArray codeArray (codeBytes input)) codeTable (codeCount input) 65536 (codeSlices input) 2713717584#64 ∧
    codeTarget.clock≤source.clock ∧ source.clock-codeTarget.clock≤price input ∧
    evaluateHOLFiniteState (CallNormal.continuationEntry (RunAttempt.codeEntry ready nodeTarget heap) codeTarget "codedb" (.val (.word codeTable))) RunAttempt.afterCodes=(outcome,inner) ∧
    post=RunAttempt.restoreHeader source (PayloadPrefix.cursor input)
      (RunAttempt.restoreConstructor afterHeader (countWord input) (restore ready "nodedb" (restore (RunAttempt.codeEntry ready nodeTarget heap) "codedb" inner)))

/-- Assemble the real returned-clock chain independently of main's parser
provenance. This keeps the final proof term small and shares the state aliases. -/
theorem reached_of_returns (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (headerTarget : PanSemStateFiniteExact 64 Guest.HostMemory) (parent : ValueHOL 64)
    (nodeTarget codeTarget : PanSemStateFiniteExact 64 Guest.HostMemory) (codeArray heap codeTable : BitVec 64) (inner : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodeReturned : MutableTable.WitnessBuild.Returned (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent)
      nodeTarget (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) heap (nodeCount input) (nodeSlices input) 2713714976#64 2713715176#64 2713717584#64)
    (codeReturned : MutableTable.WitnessBuild.Returned (RunAttempt.codeEntry (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent) nodeTarget heap)
      codeTarget (VarList.decodedArray codeArray (codeBytes input)) codeTable (codeCount input) (codeSlices input) 2713714976#64 2713715176#64 2713717584#64)
    (nodeDatabase : MutableTable.WitnessBuild.Database codeTarget (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) heap (nodeCount input) 1024 (nodeSlices input) 2713717584#64)
    (codeDatabase : MutableTable.WitnessBuild.Database codeTarget (VarList.decodedArray codeArray (codeBytes input)) codeTable (codeCount input) 65536 (codeSlices input) 2713717584#64)
    (headerForward : headerTarget.clock≤source.clock) (headerCost : source.clock-headerTarget.clock≤headerPrice input)
    (outcome : Option (PanSemResultExact 64))
    (continued : evaluateHOLFiniteState (CallNormal.continuationEntry (RunAttempt.codeEntry (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent) nodeTarget heap) codeTarget "codedb" (.val (.word codeTable))) RunAttempt.afterCodes=(outcome,inner))
    (endpoint : post=RunAttempt.restoreHeader source (PayloadPrefix.cursor input)
      (RunAttempt.restoreConstructor (parentSource source headerTarget input root) (countWord input)
        (restore (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent) "nodedb"
          (restore (RunAttempt.codeEntry (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent) nodeTarget heap) "codedb" inner)))) :
    Reached input source post root outcome := by
  have nodeCost:=nodeReturned.cost
  have codeCost:=codeReturned.cost
  have nodeForward:=nodeReturned.forward
  have codeForward:=codeReturned.forward
  have readyClock : (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent).clock=headerTarget.clock :=
    (RunAttempt.constructor_clock _ _ _ _).trans (parentSource_clock source headerTarget input root)
  have codeClock : (RunAttempt.codeEntry (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent) nodeTarget heap).clock=nodeTarget.clock :=
    CallNormal.continuation_clock _ _ _ _
  rw [readyClock] at nodeCost nodeForward
  rw [codeClock] at codeCost codeForward
  have first:=ClockCost.spend_chain source.clock headerTarget.clock nodeTarget.clock (headerPrice input)
    (MutableTable.WitnessBuild.bodyPrice (nodeSlices input) (nodeCount input)+1) headerForward nodeForward headerCost nodeCost
  have second:=ClockCost.spend_chain source.clock nodeTarget.clock codeTarget.clock
    (headerPrice input+(MutableTable.WitnessBuild.bodyPrice (nodeSlices input) (nodeCount input)+1))
    (MutableTable.WitnessBuild.bodyPrice (codeSlices input) (codeCount input)+1) (nodeForward.trans headerForward) codeForward first codeCost
  refine ⟨headerTarget,parent,nodeTarget,codeTarget,codeArray,heap,codeTable,inner,nodeReturned,codeReturned,nodeDatabase,codeDatabase,
    codeForward.trans (nodeForward.trans headerForward),?_,continued,endpoint⟩
  simpa only [price,tablesPrice,Nat.add_assoc] using second

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.parentSource_memory
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.parentSource_clock
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.reached_of_returns
