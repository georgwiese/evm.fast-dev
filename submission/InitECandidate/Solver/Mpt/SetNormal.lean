import InitECandidate.Solver.Mpt.SetAfterKeyNormal
import InitECandidate.Solver.Mpt.SetKeyGeneralEntry
import InitECandidate.Solver.Mpt.SetGeneralCost
import InitECandidate.Solver.Mpt.TrieProtectedFreshPath
import InitECandidate.Solver.Mpt.TrieGraphPathErase

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Whole unchanged256 normal setter. Its actual secure/general key
conversion, root declaration, deletion/insertion and final root store
supply the complete final graph and caller-word frame. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
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
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    Nonempty (Output source target value m graph heap heap (BitVec.ofNat 64 (NibbleKey.nibbleLength flag byteLength))
      limit nodeLower pathLower property (bodyAllowance pathLower)) := by
  have priced:=body_cost source m flag root rawKey stp pad hash heap cursor frame pointer size byteLength small graph limit nodeLower pathLower property
    valuesModel regions disjoint paths pathRegions separated member empty owned mCell keyCell lengthCell pointerCell sizeCell rootMapped rootStored flagMapped flagStored
    headerAbove headerBefore hashCell data hashArena hashBefore inputArena inputBefore stateEnd padEnd hashEnd heapCell frontier aligned scratch scratchBefore floor pathFloor nodeFloor little installed
  rw [normal] at priced
  obtain ⟨current,inner,arena,nk,saved,view,_paid,control,memory,_clock,erased,continued⟩:=general_key_entry source target m flag rawKey stp pad hash heap byteLength small
    installed scratch.domain little mCell keyCell lengthCell flagMapped flagStored hashCell data hashArena hashBefore inputArena inputBefore heapCell frontier aligned value normal
  let count:=NibbleKey.nibbleLength flag byteLength
  let length:=BitVec.ofNat 64 count
  have countBound : count≤64:=NibbleKey.nibble_length_bound flag byteLength small
  have lengthNumber : length.toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨nextHeapCell,nextArena,nextAligned,grows,globals,band,sourceFields,currentGraph,currentSame,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated,query⟩:=
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
  have currentMember : currentGraph.valid root:=by rw [currentSame]; exact member
  have currentQuery : currentGraph.PathBuffer current.be pathLower nextHeap.toNat heap length.toNat:=by rw [lengthNumber]; exact query
  have currentHeader:=headerSafe.of_fields graph currentGraph m currentSame sourceFields
  have headerAway : TrieWalk.PathWordAway heap length.toNat m:=by
    rw [lengthNumber]
    exact TrieWalk.PathWordAway.above_frontier heap m count heap.toNat query.span.fits aligned headerBefore (Nat.le_refl _)
  obtain ⟨output⟩:=after_key_normal current inner value nextHeap cursor frame root m heap length pointer size currentGraph limit nodeLower pathLower property
    currentValues currentRegions currentDisjoint currentPaths currentPathRegions currentSeparated currentQuery currentMember (by rw [lengthNumber]; exact countBound) empty currentOwned
    ((saved (ofString "m") (by decide)).trans mCell) (by rw [domainEq]; exact rootMapped) ((band m headerAbove headerBefore).trans rootStored)
    currentHeader headerAbove (headerBefore.trans_le grows) headerAway nk
    ((saved (ofString "vptr") (by decide)).trans pointerCell) ((saved (ofString "vlen") (by decide)).trans sizeCell)
    nextHeapCell nextArena nextAligned currentScratch scratchBefore floor pathFloor (nodeFloor.trans grows) (endianEq.trans little) (by rw [codeEq]; exact installed) continued
  have finalMemory:=Input.LocalEffects.memory_of_erase inner target erased
  have finalGlobals:=congrArg PanSemStateFiniteExact.globals erased
  change target.globals=inner.globals at finalGlobals
  obtain ⟨next,finalSame,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=
    output.next.after_erase inner target limit nodeLower output.heap.toNat pathLower output.heap.toNat property
      output.values output.regions output.disjoint output.paths output.pathRegions output.separated erased
  have returnedFields : output.next.PathFields target.memory:=by
    rw [finalMemory]
    exact ⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩
  have evaluatedFields:=Input.evaluation_fields source target body (some (.returned value)) normal
  exact ⟨{
    root:=output.root
    heap:=output.heap
    answer:=output.answer
    rootStored:=by rw [finalMemory]; exact output.rootStored
    domain:=evaluatedFields.1
    endian:=evaluatedFields.2.1
    code:=evaluatedFields.2.2.2
    globalsNonHeap:=by
      intro name other
      rw [finalGlobals]
      exact (output.globalsNonHeap name other).trans (globals name other)
    price:=priced
    heapCell:=by rw [finalGlobals]; exact output.heapCell
    heapArena:=output.heapArena
    heapAligned:=output.heapAligned
    grows:=grows.trans output.grows
    fields:=by
      rw [finalMemory]
      exact sourceFields.trans graph currentGraph output.fields (by intro node live; rw [currentSame]; exact live)
    next:=next
    members:=by
      intro node live
      rw [finalSame]
      exact output.members node (by rw [currentSame]; exact live)
    freshMembers:=by
      intro node live
      rw [finalSame] at live
      rcases output.freshMembers node live with old|fresh
      · exact Or.inl (by rwa [currentSame] at old)
      · exact Or.inr (grows.trans fresh)
    rootMember:=by rw [finalSame]; exact output.rootMember
    regions:=nextRegions
    disjoint:=nextDisjoint
    values:=nextValues
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated
    protectedWords:=by
      intro address safe above before away
      have currentSafe:=safe.of_fields graph currentGraph address currentSame sourceFields
      obtain ⟨word,nextSafe⟩:=output.protectedWords address currentSafe above (before.trans_le grows) away
      exact ⟨(fun different=>(congrFun finalMemory address).trans ((word different).trans (band address above before))),
        nextSafe.of_fields output.next next address finalSame returnedFields⟩ }⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.body_normal
