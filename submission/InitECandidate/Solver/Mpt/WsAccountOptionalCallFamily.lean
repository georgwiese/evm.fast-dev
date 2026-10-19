import InitECandidate.Solver.Mpt.WsAccountOptionalFamilyFrame

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original actual provider caller retains all current live tables
through real hashing/lookup/decoding and advances their shared cursor by
exactly0 or120 bytes before its genuine continuation. -/
theorem scoped_family {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash : BitVec 64)
    (objects : ι → MutableTable.TableFamily.Object)
    (family : MutableTable.TableFamily.Model source heap.toNat objects)
    (cutoff valueLimit : Nat) (separate : FamilySeparated objects cutoff stp pad nibs) (data : WsAccountLeaf.Data source ws root heap nibs)
    (values : TrieWalk.Values data.graph valueLimit (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat))
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (hashData : Keccak256.EntryData source stp addr pad heap 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad heap query)
    (valueProtection : ∀ query,TrieWalk.ValueFootprint data.graph query → Keccak256.Protected stp pad heap query)
    (rootProtection : Keccak256.Protected stp pad heap (ws+24#64))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word addr)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "ws_get_account_optional") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ target answer inner nextCursor,
      (nextCursor=heap.toNat ∨ nextCursor=heap.toNat+120) ∧ MutableTable.TableFamily.Model target nextCursor objects ∧
      Result target heap cursor limit answer ∧ HeapGlobals source target ∧
      (answer=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image target heap)) ∧
      target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      source.clock-target.clock≤31052 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name answer) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨positive,target,answer,inner,result,nonheap,image,memory,domain,endian,codeEq,price,tailRun,restored⟩ :=
    scoped_image source post ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash cutoff valueLimit data values protectedValues hashData
      graphProtection valueProtection rootProtection arena heapGlobal heapBound heapLower heapAligned sizeBound aligned scratchBelow
      rootGlobal hashGlobal rootArena hashArena installed name arguments continuation args returned normal
  obtain ⟨nextCursor,choice,nextFamily⟩ := result.family source target heap cursor limit stp pad nibs cutoff objects family separate heapBound heapAligned scratchBelow domain endian answer memory
  exact ⟨positive,target,answer,inner,nextCursor,choice,nextFamily,result,nonheap,image,domain,endian,codeEq,price,tailRun,restored⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.scoped_family
