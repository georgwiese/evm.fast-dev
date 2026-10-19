import InitECandidate.Solver.Mpt.WsAccountOptionalWorld

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix MutableTable

/-- Real provider caller delivers its current result, immutable witness,
live tables and hash environment at the actual reached continuation,
deriving every callee model and retained allocation from execution. -/
theorem scoped_world_family {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit)
    (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0) (queryArena : AllocatedBytes.Arena addr 20)
    (stateBelow : stp.toNat+200≤cutoff) (padBelow : pad.toNat+136≤cutoff)
    (objects : ι → TableFamily.Object) (family : TableFamily.Model source heap.toNat objects) (floors : ∀ index,frozenEnd≤(objects index).floor)
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0) (afterWorld : frozenEnd≤heap.toNat)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word addr)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "ws_get_account_optional") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ ready answer inner nextCursor,
      ready.locals.lookup (ofString name)=some answer ∧
      (nextCursor=heap.toNat ∨ nextCursor=heap.toNat+120) ∧ TableFamily.Model ready nextCursor objects ∧
      Nonempty (WsAccountLeaf.World ready ws root nibs cutoff frozenEnd valueLimit) ∧ Keccak256.Environment ready stp pad ∧
      Result ready heap cursor limit answer ∧ HeapGlobals source ready ∧ TableFamily.PersistentFrame cutoff heap.toNat objects objects source ready ∧
      (∀ query : BitVec 64,cutoff≤query.toNat → query.toNat<heap.toNat → ready.memory query=source.memory query) ∧ ready.code=source.code ∧ source.clock-ready.clock≤31052 ∧
      (answer=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image ready heap)) ∧
      evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨callee,called,addressCell⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "ws_get_account_optional") "addr" body addr
    (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name .one (ofString "ws_get_account_optional")
    arguments _ body continuation callee .one args called returned normal
  let entry := callEntryStateHOLFinite source callee
  let entryWorld := world.of_agreement source entry ws root nibs cutoff frozenEnd valueLimit rfl rfl rfl rfl (by intros; rfl)
  have entryEnvironment := environment.of_fields source entry stp pad rfl rfl rfl (HeapGlobals.refl source)
  have entryFamily : TableFamily.Model entry heap.toNat objects := family.of_control rfl rfl rfl rfl
  obtain ⟨nextCursor,choice,nextFamily,⟨targetWorld⟩,targetEnvironment,result,nonheap,persistent,beforeMemory,price,image⟩ :=
    body_world_family entry target ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash cutoff frozenEnd valueLimit entryWorld entryEnvironment
      stateArena stateAligned padArena padAligned queryArena stateBelow padBelow objects entryFamily floors addressCell
      (Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl) heapGlobal heapBound heapAligned afterWorld sizeBound aligned scratchBelow
      rootGlobal hashGlobal rootArena hashArena installed answer bodyRun
  let ready := Input.CallNormal.continuationEntry source target name answer
  let readyWorld := targetWorld.of_agreement target ready ws root nibs cutoff frozenEnd valueLimit rfl rfl rfl rfl (by intros; rfl)
  have readyEnvironment := targetEnvironment.of_fields target ready stp pad rfl rfl rfl (HeapGlobals.refl target)
  have readyFamily : TableFamily.Model ready nextCursor objects := nextFamily.of_control rfl rfl rfl rfl
  have readyResult := Result.of_fields target ready heap cursor limit answer result rfl rfl
  have readyFrame : TableFamily.PersistentFrame cutoff heap.toNat objects objects source ready := ⟨persistent.words⟩
  have codeEq := (Input.evaluation_fields entry target body _ bodyRun).2.2.2
  have clock := evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at clock
  change target.clock≤source.clock-1 at clock
  change source.clock-1-target.clock≤31051 at price
  have readyImage : answer=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image ready heap) := by
    rcases image with absent | image
    · exact Or.inl absent
    · obtain ⟨current⟩ := image
      exact Or.inr ⟨AccountDecode.Image.of_agreement target ready heap current rfl (by rfl) (by rfl)⟩
  exact ⟨positive,ready,answer,inner,nextCursor,Input.CallNormal.continuation_lookup_same source target name answer,
    choice,readyFamily,⟨readyWorld⟩,readyEnvironment,readyResult,nonheap,readyFrame,beforeMemory,codeEq,by change source.clock-target.clock≤31052; omega,readyImage,tailRun,restored⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.scoped_world_family
