import InitECandidate.Solver.Mpt.SetNormal
import InitECandidate.Solver.Mpt.SetEnvironment
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- The actual ignored setter calls used by state-root computation derive
their complete physical result from the current graph and actual arguments.
Caller locals are restored and the genuine call adds one source tick. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m flag root rawKey stp pad hash heap cursor frame pointer size : BitVec 64) (byteLength : Nat) (small : byteLength≤32)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (member : graph.valid root) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (rootMapped : source.memaddrs m) (rootStored : source.memory m=.word root)
    (flagMapped : source.memaddrs (m+8#64)) (flagStored : source.memory (m+8#64)=.word flag)
    (headerAbove : DeleteFrame.ceiling≤m.toNat) (headerBefore : m.toNat<heap.toNat) (headerSafe : graph.ProtectedWord m)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (data : Keccak256.EntryData source stp rawKey pad hash byteLength)
    (hashArena : AllocatedBytes.Arena hash 32) (hashBefore : hash.toNat+32≤heap.toNat)
    (inputArena : AllocatedBytes.Arena rawKey byteLength) (inputBefore : rawKey.toNat+byteLength≤heap.toNat)
    (stateEnd : stp.toNat+200≤DeleteFrame.ceiling) (padEnd : pad.toNat+136≤DeleteFrame.ceiling) (hashEnd : hash.toNat+32≤DeleteFrame.ceiling)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (values m rawKey (BitVec.ofNat 64 byteLength) pointer size))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_set") arguments)=(none,post)) :
    post.locals=source.locals ∧ Nonempty (Output source post (.val (.word 0#64)) m graph heap heap
      (BitVec.ofNat 64 (NibbleKey.nibbleLength flag byteLength)) limit nodeLower pathLower property (bodyAllowance pathLower+1)) := by
  obtain ⟨callee,called,mCell,keyCell,lengthCell,pointerCell,sizeCell⟩:=environment source.code.lookup m rawKey (BitVec.ofNat 64 byteLength) pointer size (original_code source.code installed)
  obtain ⟨funded,target,value,run⟩:=Input.CallNormal.ignored_callee_return source post (ofString "mpt_set") arguments _ body callee .one args called normal
  let entry:=callEntryStateHOLFinite source callee
  have entryScratch:=scratch.of_fields source entry cursor frame rfl rfl
  have entryData:=Keccak256.EntryData.of_control source entry stp rawKey pad hash byteLength rfl data
  obtain ⟨output⟩:=body_normal entry target value m flag root rawKey stp pad hash heap cursor frame pointer size byteLength small graph limit nodeLower pathLower property
    valuesModel regions disjoint paths pathRegions separated member empty owned mCell keyCell lengthCell pointerCell sizeCell rootMapped rootStored flagMapped flagStored
    headerAbove headerBefore headerSafe hashCell entryData hashArena hashBefore inputArena inputBefore stateEnd padEnd hashEnd heapCell frontier aligned entryScratch scratchBefore floor pathFloor nodeFloor little installed run
  have priced : source.clock-target.clock≤bodyAllowance pathLower+1:=by
    have price:=output.price
    change source.clock-1-target.clock≤bodyAllowance pathLower at price
    omega
  rw [output.answer] at run
  have actual:=evaluateHOLFiniteState_call_return_caller_locals source none (ofString "mpt_set") arguments _ body callee .one (.val (.word 0#64)) target
    args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have postEq:=congrArg Prod.snd (normal.symm.trans actual)
  change post={target with locals:=source.locals} at postEq
  subst post
  exact ⟨rfl,⟨{output with answer:=rfl,price:=priced}⟩⟩

/-- Every outcome of a real setter call, including errors and exhaustion,
costs at most its established body allowance plus the one caller tick. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m flag root rawKey stp pad hash heap cursor frame pointer size : BitVec 64) (byteLength : Nat) (small : byteLength≤32)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (member : graph.valid root) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (rootMapped : source.memaddrs m) (rootStored : source.memory m=.word root)
    (flagMapped : source.memaddrs (m+8#64)) (flagStored : source.memory (m+8#64)=.word flag)
    (headerAbove : DeleteFrame.ceiling≤m.toNat) (headerBefore : m.toNat<heap.toNat)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (data : Keccak256.EntryData source stp rawKey pad hash byteLength)
    (hashArena : AllocatedBytes.Arena hash 32) (hashBefore : hash.toNat+32≤heap.toNat)
    (inputArena : AllocatedBytes.Arena rawKey byteLength) (inputBefore : rawKey.toNat+byteLength≤heap.toNat)
    (stateEnd : stp.toNat+200≤DeleteFrame.ceiling) (padEnd : pad.toNat+136≤DeleteFrame.ceiling) (hashEnd : hash.toNat+32≤DeleteFrame.ceiling)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (destination : Option (Option MlS))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (values m rawKey (BitVec.ofNat 64 byteLength) pointer size)) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "mpt_set") arguments)).2.clock≤bodyAllowance pathLower+1 := by
  obtain ⟨callee,called,mCell,keyCell,lengthCell,pointerCell,sizeCell⟩:=environment source.code.lookup m rawKey (BitVec.ofNat 64 byteLength) pointer size (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have entryScratch:=scratch.of_fields source entry cursor frame rfl rfl
  have entryData:=Keccak256.EntryData.of_control source entry stp rawKey pad hash byteLength rfl data
  have priced:=body_cost entry m flag root rawKey stp pad hash heap cursor frame pointer size byteLength small graph limit nodeLower pathLower property
    valuesModel regions disjoint paths pathRegions separated member empty owned mCell keyCell lengthCell pointerCell sizeCell rootMapped rootStored flagMapped flagStored
    headerAbove headerBefore hashCell entryData hashArena hashBefore inputArena inputBefore stateEnd padEnd hashEnd heapCell frontier aligned entryScratch scratchBefore floor pathFloor nodeFloor little installed
  exact Input.ClockCost.call_current source destination (ofString "mpt_set") arguments _ body callee .one (bodyAllowance pathLower) args called priced

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.call_normal
#print axioms InitECandidate.Solver.Mpt.SetTrie.call_cost
