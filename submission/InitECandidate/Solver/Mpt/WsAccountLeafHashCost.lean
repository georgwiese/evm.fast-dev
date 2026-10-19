import InitECandidate.Solver.Mpt.WsAccountLeafData

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem lookup_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root h nibs : BitVec 64)
    (data : Data source ws root h nibs)
    (outputCell : source.locals.lookup (ofString "h")=some (.val (.word h)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source lookup).2.clock≤2092 := by
  have args := lookup_arguments source ws root h data.worldState data.rootMapped data.rootStored outputCell
  exact TrieLookup.scoped_cost source root h nibs data.graph data.member data.protectedGraph data.scratch data.little data.fits
    data.inputMapped data.outputMapped data.separate (ofString "r") lookupArguments finish 1 args installed (finish_cost source.code installed)

/-- The actual original address hash feeds the actual original trie lookup.
Incoming physical ownership is current entry data; no reached hash result,
trie model or future helper execution is a premise. -/
theorem after_alloc_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (outputCell : source.locals.lookup (ofString "h")=some (.val (.word h)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterAlloc).2.clock≤2295 := by
  have args := hash_arguments source addr h addressCell outputCell
  have code := hash_original_code source.code installed
  have firstCost := Keccak256.call_cost source hashArguments (some none) stp addr pad h 20 args code hashData (by decide)
  change source.clock-(evaluateHOLFiniteState source hash).2.clock≤203 at firstCost
  have firstClock := evaluateHOLFiniteState_clock_le source hash
  rw [afterAlloc,evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source hash=output at firstCost firstClock ⊢
  obtain ⟨result,reached⟩ := output
  change source.clock-reached.clock≤203 at firstCost
  change reached.clock≤source.clock at firstClock
  cases result with
  | none =>
    obtain ⟨locals,upper,lower,control,memory⟩ := Keccak256.call_normal source reached hashArguments stp addr pad h 20 args code hashData (by decide) computed
    obtain ⟨nextData⟩ := Data.after_hash source reached ws root h nibs stp pad data graphProtection rootProtection control memory
    have currentH : reached.locals.lookup (ofString "h")=some (.val (.word h)) := by rw [locals]; exact outputCell
    have codeEq := congrArg PanSemStateFiniteExact.code control
    change reached.code=source.code at codeEq
    have currentInstalled : Input.OriginalCode.Installed reached.code := by rw [codeEq]; exact installed
    have secondCost := lookup_cost reached ws root h nibs nextData currentH currentInstalled
    have secondClock := evaluateHOLFiniteState_clock_le reached lookup
    change source.clock-(evaluateHOLFiniteState reached lookup).2.clock≤2295
    omega
  | some result =>
    change source.clock-reached.clock≤2295
    omega

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.lookup_cost
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_alloc_cost
