import InitECandidate.Solver.MutableTable.FindAnyBodyCost
import InitECandidate.Solver.MutableTable.FindAnyReadonly
import InitECandidate.Solver.MutableTable.GetTail32
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem tail_decision : Input.PureDecision afterIndex :=
  .seq (.ite condition (.returned _) .skip) (.returned _)

/-- Complete original getter cost from the actual table, with arbitrary
query memory. Its value-cell reads cost no source-call/loop ticks. -/
theorem any_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (cells : Find.HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (order : List Nat) (room : order.length<2^bits)
    (binary : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (mapped : ∀ i<2^bits,∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress (p.keys+BitVec.ofNat 64 i*p.stride) offset)))
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one)) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤6*order.length+2 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t",localVar "key"]=
      some [.val (.word table),.val (.word p.key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,cells.tableLocal,cells.keyLocal]
  obtain ⟨callee,called,tCell,keyCell⟩ := Find.environment source.code.lookup table p.key findCode
  let entry:=callEntryStateHOLFinite source callee
  have entryCells : Find.HeaderCells entry table p := ⟨tCell,keyCell,cells.mapped,cells.capacity,cells.keyLength,cells.stride,cells.keys,cells.used⟩
  have price:=Find.any_body_cost entry table p entryCells keyLength bits small capacity order room binary covered fits mapped hashCode memeqCode
  have caller:=Input.ClockCost.scoped_current source (ofString "i") .one (ofString "htab_find_slot") [localVar "t",localVar "key"] _ Find.body afterIndex callee .one
    (6*order.length+1) 0 args called price (Input.ClockCost.of_quiet source.code _ (tail_decision.quiet source.code))
  rw [body_shape]
  exact caller

theorem any_body_readonly (code)
    (hashCode : code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one)) : Input.LocalEffects.Preserves code body := by
  rw [body_shape]
  exact Input.LocalEffects.scoped_body code (ofString "i") .one (ofString "htab_find_slot") [localVar "t",localVar "key"] afterIndex Find.formals Find.body .one
    findCode (Find.any_body_readonly code hashCode memeqCode)
    (Input.LocalEffects.sequence code _ _ (Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.returned code _) (Input.LocalEffects.skip code)) (Input.LocalEffects.returned code _))

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.tail_decision
#print axioms InitECandidate.Solver.MutableTable.Get.any_body_cost
#print axioms InitECandidate.Solver.MutableTable.Get.any_body_readonly
