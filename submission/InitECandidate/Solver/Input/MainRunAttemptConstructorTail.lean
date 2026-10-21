import InitECandidate.Solver.Input.MainRunAttemptConstructorReached

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessConstructors

/-- The reached header boundary is sufficient for the remaining real
constructor prefix; parser provenance is handled by the invoking theorem. -/
theorem tail_of_inputs (input : Guest.InputBlob) (source post headerTarget first : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root headerRows codeArray heap : BitVec 64)
    (headerReturned : Headers.Validate.Returned (validatorEntry source input) headerTarget headerRows (initialHeap root) (countWord input)
      2713714688#64 2701135872#64 2713714976#64 2713715176#64 (HeaderSlices.pointer input) (HeaderSlices.length input)
      inputPointer.toNat (initialHeap root).toNat (input.length%2^64))
    (nodeInputs : MutableTable.WitnessBuild.Inputs headerTarget (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) heap
      (nodeCount input) 1024 (nodeSlices input) 2713714976#64 2713715176#64 2713717584#64)
    (codeInputs : MutableTable.WitnessBuild.Inputs headerTarget (VarList.decodedArray codeArray (codeBytes input)) heap
      (codeCount input) 65536 (codeSlices input) 2713714976#64 2713715176#64 2713717584#64)
    (room : heap.toNat+72+57*(4*nodeCount input+4)+7+72+57*(4*codeCount input+4)+7≤33806089496)
    (actualSiArena : AllocatedBytes.Arena (RequestPrefix.cursor input) 96) (actualSiAligned : (RequestPrefix.cursor input).toNat%8=0)
    (siBefore : (RequestPrefix.cursor input).toNat+96≤heap.toNat) (siLower : inputPointer.toNat≤(RequestPrefix.cursor input).toNat)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (headerCountCell : headerTarget.memory (byteAddress (RequestPrefix.cursor input) 80)=.word (countWord input))
    (nodePointer : headerTarget.memory (byteAddress (RequestPrefix.cursor input) 40)=.word (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)))
    (nodeCountCell : headerTarget.memory (byteAddress (RequestPrefix.cursor input) 48)=.word (BitVec.ofNat 64 (nodeCount input)))
    (codePointer : headerTarget.memory (byteAddress (RequestPrefix.cursor input) 56)=.word (VarList.decodedArray codeArray (codeBytes input)))
    (codeCountCell : headerTarget.memory (byteAddress (RequestPrefix.cursor input) 64)=.word (BitVec.ofNat 64 (codeCount input)))
    (outcome : Option (PanSemResultExact 64))
    (remaining : evaluateHOLFiniteState (parentSource source headerTarget input root) RunAttempt.afterHeaders=(outcome,first))
    (headerEndpoint : post=RunAttempt.restoreHeader source (PayloadPrefix.cursor input) first) :
    source.clock-post.clock≤price input ∨ Reached input source post root outcome := by
  let afterHeader:=parentSource source headerTarget input root
  have nodeContext:=nodeInputs.of_fields headerTarget afterHeader _ heap _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  have codeContext:=codeInputs.of_fields headerTarget afterHeader _ heap _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  have afterMemory : afterHeader.memory=headerTarget.memory := parentSource_memory source headerTarget input root
  have afterClock : afterHeader.clock=headerTarget.clock := parentSource_clock source headerTarget input root
  have headerSi:=RunAttempt.headerEntry_si source (PayloadPrefix.cursor input) (RequestPrefix.cursor input) siCell
  have afterSi : afterHeader.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))) :=
    (CallNormal.continuation_lookup_other _ _ "vh" "si" _ (by decide)).trans headerSi
  have pair : afterHeader.locals.lookup (ofString "vh")=some (Headers.Validate.result (initialHeap root) (hashArray input root)) :=
    CallNormal.continuation_lookup_same _ _ _ _
  obtain ⟨oldHashes,oldHashesCell⟩ := scalars _ RunAttemptData.block_hash_names.1
  obtain ⟨oldCount,oldCountCell⟩ := scalars _ RunAttemptData.block_hash_names.2
  have hashCell : afterHeader.globals.lookup (ofString "block_hashes")=some (.val (.word oldHashes)) :=
    (headerReturned.globals _ (by decide)).trans oldHashesCell
  have globalCount : afterHeader.globals.lookup (ofString "block_hashes_n")=some (.val (.word oldCount)) :=
    (headerReturned.globals _ (by decide)).trans oldCountCell
  change evaluateHOLFiniteState afterHeader RunAttempt.afterHeaders=(outcome,first) at remaining
  rcases RunAttempt.parent_prefix afterHeader first (RequestPrefix.cursor input) (initialHeap root) (hashArray input root) (countWord input) oldHashes oldCount
      nodeContext.environment.domain actualSiArena actualSiAligned afterSi pair ((congrFun afterMemory _).trans headerCountCell) hashCell globalCount outcome remaining with stopped|parentReached
  · have headerCost:=headerReturned.cost
    have headerForward:=headerReturned.forward
    have finalClock : post.clock=first.clock := by
      have projected:=congrArg PanSemStateFiniteExact.clock headerEndpoint
      simpa only [RunAttempt.restoreHeader_clock] using projected
    have firstForward:=evaluateHOLFiniteState_clock_le afterHeader RunAttempt.afterHeaders
    rw [remaining] at firstForward
    change source.clock-headerTarget.clock≤headerPrice input at headerCost
    rw [afterClock] at stopped
    rw [afterClock] at firstForward
    rw [finalClock]
    exact Or.inl (by unfold price; omega)
  · obtain ⟨parent,constructorPost,nonempty,constructorRun,parentEndpoint⟩ := parentReached
    let ready:=RunAttempt.constructorEntry afterHeader (countWord input) (hashArray input root) parent
    have nodeReady:=RunAttempt.constructor_inputs afterHeader _ heap (countWord input) (hashArray input root) 2713714976#64 2713715176#64 2713717584#64 _ _ _ nodeContext parent
    have codeReady:=RunAttempt.constructor_inputs afterHeader _ heap (countWord input) (hashArray input root) 2713714976#64 2713715176#64 2713717584#64 _ _ _ codeContext parent
    have readySi : ready.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))) :=
      RunAttempt.constructor_si afterHeader _ _ _ parent afterSi
    have readyMemory : ready.memory=headerTarget.memory := (RunAttempt.constructor_memory afterHeader _ _ parent).trans afterMemory
    have readyClock : ready.clock=headerTarget.clock := (RunAttempt.constructor_clock afterHeader _ _ parent).trans afterClock
    have buffersBefore : (2713714976#64 : BitVec 64).toNat+200≤(RequestPrefix.cursor input).toNat ∧
        (2713715176#64 : BitVec 64).toNat+136≤(RequestPrefix.cursor input).toNat ∧ (2713717584#64 : BitVec 64).toNat+32≤(RequestPrefix.cursor input).toNat := by
      change 2713731432≤_ at siLower
      change 2713715176≤_ ∧ 2713715312≤_ ∧ 2713717616≤_
      omega
    rcases RunAttempt.constructors_trace ready constructorPost (RequestPrefix.cursor input) _ _ heap 2713714976#64 2713715176#64 2713717584#64 _ _ _ _ _ _
        nodeReady codeReady room actualSiArena actualSiAligned siBefore buffersBefore (by constructor <;> decide) (by constructor <;> decide) (by constructor <;> decide)
        readySi ((congrFun readyMemory _).trans nodePointer) ((congrFun readyMemory _).trans nodeCountCell) ((congrFun readyMemory _).trans codePointer) ((congrFun readyMemory _).trans codeCountCell) outcome constructorRun with stopped|built
    · have headerCost:=headerReturned.cost
      have headerForward:=headerReturned.forward
      have headerClock : post.clock=first.clock := by
        have projected:=congrArg PanSemStateFiniteExact.clock headerEndpoint
        simpa only [RunAttempt.restoreHeader_clock] using projected
      have parentClock : first.clock=constructorPost.clock := by
        have projected:=congrArg PanSemStateFiniteExact.clock parentEndpoint
        simpa only [RunAttempt.restoreConstructor_clock] using projected
      have finalClock:=headerClock.trans parentClock
      have forward:=evaluateHOLFiniteState_clock_le ready RunAttempt.constructors
      rw [constructorRun] at forward
      change source.clock-headerTarget.clock≤headerPrice input at headerCost
      rw [readyClock] at stopped
      change headerTarget.clock-constructorPost.clock≤tablesPrice input at stopped
      rw [readyClock] at forward
      rw [finalClock]
      exact Or.inl (by unfold price; omega)
    · obtain ⟨nodeTarget,codeTarget,codeTable,currentHeap,inner,nodeReturned,codeReturned,nodeDatabase,codeDatabase,currentHeapCell,nodeBefore,codeBefore,continued,endpoint⟩ := built
      have headerCost:=headerReturned.cost
      have headerForward:=headerReturned.forward
      change source.clock-headerTarget.clock≤headerPrice input at headerCost
      change headerTarget.clock≤source.clock at headerForward
      apply Or.inr
      exact reached_of_returns input source post root headerTarget parent nodeTarget codeTarget codeArray heap codeTable currentHeap inner nodeReturned codeReturned
        nodeDatabase codeDatabase currentHeapCell nodeBefore codeBefore headerForward headerCost outcome continued (by
          have firstEnd:=congrArg (RunAttempt.restoreHeader source (PayloadPrefix.cursor input)) parentEndpoint
          have secondEnd:=congrArg (fun current=>RunAttempt.restoreHeader source (PayloadPrefix.cursor input)
            (RunAttempt.restoreConstructor afterHeader (countWord input) current)) endpoint
          exact headerEndpoint.trans (firstEnd.trans secondEnd))

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.tail_of_inputs
