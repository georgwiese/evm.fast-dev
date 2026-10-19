import InitECandidate.Solver.Mpt.WsAccountOptionalImage

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual original provider caller: real optional account image, retained
allocation, complete persistent-word frame, immutable fields and source
price before its genuine continuation. Entry facts concern current state. -/
theorem scoped_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash : BitVec 64)
    (cutoff valueLimit : Nat) (data : WsAccountLeaf.Data source ws root heap nibs)
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
    1≤source.clock ∧ ∃ target answer inner,Result target heap cursor limit answer ∧ HeapGlobals source target ∧
      (answer=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image target heap)) ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat → Keccak256.Protected stp pad heap query →
        (∀ offset<64,query≠panByteAlignHOL (width:=64) (byteAddress nibs offset)) → target.memory query=source.memory query) ∧
      target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      source.clock-target.clock≤191*valueLimit+2594 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name answer) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,addressCell⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "ws_get_account_optional") "addr" body addr
    (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name .one (ofString "ws_get_account_optional")
    arguments _ body continuation callee .one args called returned normal
  let entry := callEntryStateHOLFinite source callee
  let entryData := WsAccountLeaf.Data.of_fields source entry ws root heap nibs data rfl rfl rfl rfl rfl
  let entryValues := TrieWalk.Values.rebase source.memory entry.memory source.memaddrs entry.memaddrs data.graph valueLimit values rfl rfl
  have entryHash := Keccak256.EntryData.of_fields source entry stp addr pad heap 20 rfl rfl rfl rfl rfl hashData
  obtain ⟨result,nonheap,price,image,memory⟩ := body_image entry target ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash cutoff valueLimit entryData entryValues protectedValues entryHash
    graphProtection valueProtection rootProtection addressCell (Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl)
    heapGlobal heapBound heapLower heapAligned sizeBound aligned scratchBelow rootGlobal hashGlobal rootArena hashArena installed answer bodyRun
  have clock := evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at clock
  change target.clock≤source.clock-1 at clock
  change source.clock-1-target.clock≤191*valueLimit+2593 at price
  have codeEq := (Input.evaluation_fields entry target body _ bodyRun).2.2.2
  have fields := Input.evaluation_fields entry target body _ bodyRun
  exact ⟨positive,target,answer,inner,result,nonheap,image,memory,fields.1,fields.2.1,codeEq,by omega,tailRun,restored⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.scoped_image
