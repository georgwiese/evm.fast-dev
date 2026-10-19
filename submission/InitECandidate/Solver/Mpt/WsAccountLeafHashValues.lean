import InitECandidate.Solver.Mpt.WsAccountLeafValueData
import InitECandidate.Solver.Mpt.TrieLookupCallValues

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {property : BitVec 64 → BitVec 64 → Prop}

theorem finish_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (answer returned : ValueHOL 64)
    (cell : source.locals.lookup (ofString "r")=some answer)
    (normal : evaluateHOLFiniteState source finish=(some (.returned returned),post)) : returned=answer := by
  have safe : Input.LocalPrefix (ofString "r") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,firstRun,tailRun,localEq⟩ := safe.normal_continue source post (.return (localVar "r")) returned normal
  have current : middle.locals.lookup (ofString "r")=some answer := localEq.trans cell
  have read : eval middle (localVar "r")=some answer := by simp [eval,localVar,evalHOLExact,toExact,current]
  have actual := (Input.return_normal middle post (localVar "r") returned tailRun).1
  exact (Option.some.inj (read.symm.trans actual)).symm

set_option maxRecDepth 100000 in
theorem lookup_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root h nibs : BitVec 64)
    (data : Data source ws root h nibs) (valueLimit : Nat) (values : TrieWalk.Values data.graph valueLimit property)
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (outputCell : source.locals.lookup (ofString "h")=some (.val (.word h)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source lookup=(some (.returned returned),post)) :
    TrieWalk.Answer post.memaddrs valueLimit (property:=property) returned := by
  have args := lookup_arguments source ws root h data.worldState data.rootMapped data.rootStored outputCell
  obtain ⟨funded,target,answer,inner,result,upper,lower,frame,finishRun,restored⟩ :=
    TrieLookup.scoped_normal source post root h nibs data.graph valueLimit values data.member data.protectedGraph protectedValues
      data.scratch data.little data.fits data.inputMapped data.outputMapped data.separate "r" lookupArguments finish args installed returned normal
  let ready := Input.CallNormal.continuationEntry source target "r" answer
  have cell : ready.locals.lookup (ofString "r")=some answer := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have returnedEq := finish_normal_value ready inner answer returned cell finishRun
  have domain := (Input.evaluation_fields ready inner finish (some (.returned returned)) finishRun).1
  change inner.memaddrs=target.memaddrs at domain
  have postDomain : post.memaddrs=target.memaddrs := by rw [restored]; exact domain
  rw [postDomain,returnedEq]
  exact result

set_option maxRecDepth 100000 in
/-- The actual address hash feeds an actual lookup value through the real
release/return continuation, retaining its mapped bounded payload. -/
theorem after_alloc_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs) (valueLimit : Nat) (values : TrieWalk.Values data.graph valueLimit property)
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (valueProtection : ∀ query,TrieWalk.ValueFootprint data.graph query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (outputCell : source.locals.lookup (ofString "h")=some (.val (.word h)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) :
    TrieWalk.Answer post.memaddrs valueLimit (property:=property) returned := by
  have safe : Input.LocalPrefix (ofString "h") hash := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨reached,hashRun,lookupRun,localEq⟩ := safe.normal_continue source post lookup returned normal
  have args := hash_arguments source addr h addressCell outputCell
  obtain ⟨locals,upper,lower,control,memory⟩ := Keccak256.call_normal source reached hashArguments stp addr pad h 20 args
    (hash_original_code source.code installed) hashData (by decide) hashRun
  obtain ⟨nextData,nextProtection,⟨nextValues⟩⟩ := Data.values_after_hash source reached ws root h nibs stp pad data valueLimit values protectedValues
    graphProtection valueProtection rootProtection control memory
  have currentH : reached.locals.lookup (ofString "h")=some (.val (.word h)) := by rw [locals]; exact outputCell
  have codeEq := congrArg PanSemStateFiniteExact.code control
  change reached.code=source.code at codeEq
  have currentInstalled : Input.OriginalCode.Installed reached.code := by rw [codeEq]; exact installed
  exact lookup_normal_value reached post ws root h nibs nextData valueLimit nextValues nextProtection currentH currentInstalled returned lookupRun

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.finish_normal_value
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.lookup_normal_value
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_alloc_normal_value
