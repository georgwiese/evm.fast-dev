import InitECandidate.Solver.MutableTable.GetAnyCost
import InitECandidate.Solver.MutableTable.FindAnyBodySelection
import InitECandidate.Solver.MutableTable.GetSizedOrigin

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original getter return is absent or the actual value word
of a physically occupied slot. This derives provenance without a readable
query, logical key equality, hash assumption or future successful call. -/
theorem any_body_origin (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (cells : Find.HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (order : List Nat) (room : order.length<2^bits)
    (binary : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (mapped : ∀ i<2^bits,∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress (p.keys+BitVec.ofNat 64 i*p.stride) offset)))
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (vals : BitVec 64) (valsMapped : source.memaddrs (table+40#64)) (valsCell : source.memory (table+40#64)=.word vals)
    (values : ∀ slot : BitVec 64,slot.toNat<p.capacity.toNat→∃ value,source.memaddrs (vals+slot*8#64) ∧ source.memory (vals+slot*8#64)=.word value)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ flag result,(flag=0#64 ∨ flag=1#64) ∧ value=pair flag result ∧
      ValueOrigin source vals p.capacity flag result (fun slot=>∃ byte : UInt8,byte≠0 ∧ Find.usedByte source p slot=some byte) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t",localVar "key"]=
      some [.val (.word table),.val (.word p.key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,cells.tableLocal,cells.keyLocal]
  obtain ⟨callee,called,tCell,keyCell⟩ := Find.environment source.code.lookup table p.key findCode
  let entry:=callEntryStateHOLFinite source callee
  have entryCells : Find.HeaderCells entry table p := ⟨tCell,keyCell,cells.mapped,cells.capacity,cells.keyLength,cells.stride,cells.keys,cells.used⟩
  rw [body_shape] at normal
  obtain ⟨funded,target,returned,inner,bodyRun,checked,continued,endpoint⟩ := Input.CallNormal.scoped_normal source post "i" .one (ofString "htab_find_slot")
    [localVar "t",localVar "key"] _ Find.body afterIndex callee .one args called value normal
  obtain ⟨index,returnedEq,entrySelected⟩ := Find.any_body_selection entry target table p entryCells keyLength bits small capacity order room binary covered fits mapped hashCode memeqCode returned bodyRun
  have selected : Find.Selection source p index := Find.Selection.of_fields entry source p index rfl rfl rfl entrySelected
  have pure:=Find.any_body_readonly source.code hashCode memeqCode entry rfl
  rw [bodyRun] at pure
  have targetFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase source := pure
  rw [returnedEq] at continued
  let current:=Input.CallNormal.continuationEntry source target "i" (.val (.word index))
  have currentFrame : Input.LocalEffects.erase current=Input.LocalEffects.erase source :=
    (Input.CallNormal.continuation_erase source target "i" (.val (.word index))).trans targetFrame
  have memory:=Input.LocalEffects.memory_of_erase source current currentFrame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs currentFrame
  change current.memaddrs=source.memaddrs at domain
  have currentT : current.locals.lookup (ofString "t")=some (.val (.word table)) :=
    (Input.CallNormal.continuation_lookup_other source target "i" "t" (.val (.word index)) (by decide)).trans cells.tableLocal
  have currentI : current.locals.lookup (ofString "i")=some (.val (.word index)) := Input.CallNormal.continuation_lookup_same _ _ _ _
  have indexBound : index.toNat≤p.capacity.toNat := by
    rcases selected with absent|present
    · rw [absent]
    · exact Nat.le_of_lt present.1
  have eligibleIndex : index.toNat<p.capacity.toNat→∃ byte : UInt8,byte≠0 ∧ Find.usedByte source p index=some byte := by
    intro inside
    rcases selected with absent|present
    · rw [absent] at inside; omega
    · exact present.2
  have currentCapMapped : current.memaddrs (table+16#64) := by rw [domain]; exact cells.mapped 16 (by simp)
  have currentCap : current.memory (table+16#64)=.word p.capacity := by rw [memory]; exact cells.capacity
  have currentValsMapped : current.memaddrs (table+40#64) := by rw [domain]; exact valsMapped
  have currentVals : current.memory (table+40#64)=.word vals := by rw [memory]; exact valsCell
  have currentValues : ∀ slot : BitVec 64,slot.toNat<p.capacity.toNat→∃ word,current.memaddrs (vals+slot*8#64) ∧ current.memory (vals+slot*8#64)=.word word := by
    intro slot inside
    rw [domain,memory]
    exact values slot inside
  obtain ⟨flag,result,flagBinary,origin,tailRun⟩ := sized_tail_origin current table vals index p.capacity currentT currentI
    currentCapMapped currentCap currentValsMapped currentVals currentValues indexBound
    (fun slot=>∃ byte : UInt8,byte≠0 ∧ Find.usedByte source p slot=some byte) eligibleIndex
  have valueEq : value=pair flag result := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst (continued.symm.trans tailRun)
  unfold ValueOrigin at origin ⊢
  rw [memory] at origin
  exact ⟨flag,result,flagBinary,valueEq,origin⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.any_body_origin
