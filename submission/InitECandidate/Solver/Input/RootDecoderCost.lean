import InitECandidate.Solver.Input.RootMaterializeEntry
import InitECandidate.Solver.Mpt.WitnessMaterializeBodyCost
import InitECandidate.Solver.Mpt.WitnessDecodeSuffixCost

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessConstructors

def rootDecoderPrice (input : Guest.InputBlob) : Nat :=
  (Mpt.WitnessCore.Stack.iterationCost input+1)*6864962+6*nodeCount input+60

/-- Whole original241 on every outcome: real empty-root comparison,
database lookup, bounded original materializer, allocation/copy/cache and
all caller restorations. No future successful call is a premise. -/
theorem root_decoder_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : RootBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64) :
    source.clock-(evaluateHOLFiniteState source Mpt.WitnessDecodeRoot.body).2.clock ≤ rootDecoderPrice input := by
  let output := evaluateHOLFiniteState source Mpt.WitnessDecodeRoot.body
  rcases materialize_entry_of_root input source output.2 root boundary installed scalars rootCell scratch environment output.1 rfl with stopped|reached
  · exact stopped.trans (by unfold rootDecoderPrice; omega)
  · obtain ⟨lookupSource,caller,nodes,slice,index,entry,target,childResult,inner,entryBoundary,pure,entryInstalled,entryScalars,
      dbCell,pCell,nCell,indexInside,sliceEq,size,sliceArena,lower,before,entryScratch,entryEnvironment,forward,spent,run,resumes,callerRoot,endpoint⟩ := reached
    have savedBoundary := entryBoundary
    obtain ⟨codeArray,nodeTable,codeTable,heap,nodeData,codeData,nodeCell,heapCell,heapArena,heapAligned,nodeBefore,codeBefore⟩ := savedBoundary
    have same : nodeTable=nodes := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nodeCell.symm.trans dbCell)))
    obtain ⟨capacity,capacityCell,tableBefore⟩ := nodeBefore
    have heapLower : 2713731432≤heap.toNat := by rw [same] at tableBefore; omega
    have bodyCost := materialize_body_cost input entry nodes slice.1 slice.2 heap 2713714688#64 2701135872#64 entryBoundary
      dbCell pCell nCell heapCell heapLower entryScratch (by decide) before size lower entryInstalled
    rw [run] at bodyCost
    change entry.clock-target.clock≤(Mpt.WitnessCore.Stack.iterationCost input+1)*6864962+6 at bodyCost
    have bodyClock := evaluateHOLFiniteState_clock_le entry Mpt.WitnessMaterialize.body
    rw [run] at bodyClock
    change target.clock≤entry.clock at bodyClock
    have endpointClock : output.2.clock=inner.clock := (congrArg PanSemStateFiniteExact.clock endpoint).trans
      ((QueryBranch.restore_clock source (QueryBranch.restore lookupSource "r" inner) "is_empty").trans (QueryBranch.restore_clock lookupSource inner "r"))
    change source.clock-output.2.clock≤rootDecoderPrice input
    rw [endpointClock]
    rcases resumes with stopped|returned
    · unfold rootDecoderPrice
      omega
    · obtain ⟨returned,continued,resultEq,checked,tailRun,tailEnd⟩ := returned
      have targetCode := (evaluation_fields entry target Mpt.WitnessMaterialize.body childResult run).2.2.2
      let ready := CallNormal.continuationEntry caller target "nd" returned
      have readyInstalled : OriginalCode.Installed ready.code := by change OriginalCode.Installed target.code; rw [targetCode]; exact entryInstalled
      have readyRoot : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)) := by
        simp only [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE, if_neg (show ofString "nd"≠ofString "root_hash" from by decide)]
        exact callerRoot
      have tailCost := Mpt.WitnessDecodeRoot.suffix_cost ready root readyInstalled readyRoot
      rw [tailRun] at tailCost
      change target.clock-continued.clock≤44 at tailCost
      have tailClock := evaluateHOLFiniteState_clock_le ready Mpt.WitnessDecodeRoot.afterMaterialize
      rw [tailRun] at tailClock
      change continued.clock≤target.clock at tailClock
      have innerClock : inner.clock=continued.clock := (congrArg PanSemStateFiniteExact.clock tailEnd).trans (QueryBranch.restore_clock caller continued "nd")
      unfold rootDecoderPrice
      omega

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.root_decoder_cost
