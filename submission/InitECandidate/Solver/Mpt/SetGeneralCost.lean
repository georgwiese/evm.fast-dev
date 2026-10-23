import InitECandidate.Solver.Mpt.SetMutationCost
import InitECandidate.Solver.Mpt.NibbleKeyGraphFrame

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def bodyAllowance (pathLower : Nat) : Nat:=218+mutationAllowance pathLower

/-- Every outcome of the whole unchanged256 setter, for both secure
flags, arbitrary registered roots and actual delete/insert payload words.
Only a genuine key-helper return derives the current allocation, graph,
protected query and header before pricing mutation. This is local source
accounting, with copy amortization still separate from final target K. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m flag root rawKey stp pad hash heap cursor frame pointer size : BitVec 64) (byteLength : Nat) (small : byteLength≤32)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (member : graph.valid root) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word rawKey)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 byteLength))))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
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
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyAllowance pathLower := by
  by_cases zero : source.clock=0
  · simp only [zero,Nat.zero_sub,Nat.zero_le]
  · obtain ⟨callee,called,mLocal,keyLocal,lengthLocal⟩:=NibbleKey.environment source.code.lookup m rawKey (BitVec.ofNat 64 byteLength) (NibbleKey.original_code source.code installed)
    have args:=key_arguments source m rawKey byteLength mCell keyCell lengthCell
    let entry:=callEntryStateHOLFinite source callee
    have entryData:=Keccak256.EntryData.of_control source entry stp rawKey pad hash byteLength rfl data
    have keyPrice:=NibbleKey.general_cost entry m flag rawKey stp pad hash byteLength small installed mLocal keyLocal lengthLocal flagMapped flagStored hashCell entryData
    have suffix (childTarget : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
        (normal : evaluateHOLFiniteState entry NibbleKey.body=(some (.returned returned),childTarget))
        (checked : (shapeEqHOL (shapeOfHOLExact returned) NibbleKey.returnShape && shapeEqHOL (shapeOfHOLExact returned) NibbleKey.returnShape)=true) :
        childTarget.clock-(evaluateHOLFiniteState (Input.CallNormal.continuationEntry source childTarget "nk" returned) afterKey).2.clock≤mutationAllowance pathLower:=by
      let current:=Input.CallNormal.continuationEntry source childTarget "nk" returned
      have reached : Input.CallPrefix.Reaches source (.scoped (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") keyArguments) current:=
        .scoped source (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") keyArguments _ NibbleKey.body callee NibbleKey.returnShape returned childTarget args called zero normal checked
      obtain ⟨arena,nk,saved,view,_price,control,memory⟩:=NibbleKey.scoped_general_normal (ofString "nk") keyArguments m flag rawKey stp pad hash heap byteLength small installed scratch.domain little
        args flagMapped flagStored hashCell data hashArena hashBefore inputArena inputBefore heapCell frontier aligned reached
      let count:=NibbleKey.nibbleLength flag byteLength
      let length:=BitVec.ofNat 64 count
      have countBound : count≤64:=NibbleKey.nibble_length_bound flag byteLength small
      have lengthNumber : length.toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      obtain ⟨nextHeapCell,nextArena,nextAligned,grows,globals,band,_fields,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,query⟩:=
        NibbleKey.graph_after_query source current heap stp pad hash count countBound graph limit nodeLower pathLower DeleteFrame.ceiling property
          valuesModel regions disjoint paths pathRegions separated floor pathFloor nodeFloor (by decide) stateEnd padEnd hashEnd arena aligned view control memory
      let nextHeap:=PersistentAlloc.rounded heap (BitVec.ofNat 64 count)
      have domainEq : current.memaddrs=source.memaddrs:=by have projected:=congrArg PanSemStateFiniteExact.memaddrs control; exact projected
      have endianEq : current.be=source.be:=by have projected:=congrArg PanSemStateFiniteExact.be control; exact projected
      have codeEq : current.code=source.code:=by have projected:=congrArg PanSemStateFiniteExact.code control; exact projected
      have currentScratch : Rlp.Validation.Arena current cursor frame:={
        domain:=domainEq.trans scratch.domain
        cursorGlobal:=(globals (ofString "scratch_ptr") (by decide)).trans scratch.cursorGlobal
        limitGlobal:=(globals (ofString "frame_mem_ptr") (by decide)).trans scratch.limitGlobal
        ordered:=scratch.ordered
        aligned:=scratch.aligned
        lower:=scratch.lower
        upper:=scratch.upper }
      have currentOwned : pointer≠0#64→size≠0#64→TrieWalk.Payload current.memaddrs pointer size limit ∧ property pointer size:=by
        intro pa sa
        obtain ⟨payload,extra⟩:=owned pa sa
        exact ⟨by rwa [domainEq],extra⟩
      have currentMember : next.valid root:=by rw [same]; exact member
      have currentQuery : next.PathBuffer current.be pathLower nextHeap.toNat heap length.toNat:=by rw [lengthNumber]; exact query
      obtain ⟨currentValues⟩:=nextValues
      exact after_key_cost current nextHeap cursor frame root m heap length pointer size next limit nodeLower pathLower property currentValues nextRegions nextDisjoint nextPaths nextPathRegions nextSeparated
        currentQuery currentMember (by rw [lengthNumber]; exact countBound) empty currentOwned
        ((saved (ofString "m") (by decide)).trans mCell) (by rw [domainEq]; exact rootMapped) ((band m headerAbove headerBefore).trans rootStored)
        nk ((saved (ofString "vptr") (by decide)).trans pointerCell) ((saved (ofString "vlen") (by decide)).trans sizeCell)
        nextHeapCell nextArena nextAligned currentScratch scratchBefore floor pathFloor (nodeFloor.trans grows) (endianEq.trans little) (by rw [codeEq]; exact installed)
    rw [body_shape]
    have priced:=Input.ClockCost.scoped_reached_current source "nk" NibbleKey.returnShape (ofString "mpt_nibble_key") keyArguments _ NibbleKey.body afterKey callee NibbleKey.returnShape
      217 (mutationAllowance pathLower) args called keyPrice suffix
    exact priced.trans (by unfold bodyAllowance; omega)

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.body_cost
