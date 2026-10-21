import InitECandidate.Solver.MutableTable.GetAnyCost
import InitECandidate.Solver.MutableTable.NodeDbTail32

namespace InitECandidate.Solver.MutableTable.NodeDb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem tail_decision : Input.PureDecision afterGet :=
  .seq (.ite condition (.returned _) .skip) (.returned _)

/-- The actual original witness lookup costs six ticks per occupied table
slot plus its three nested calls, with no query-memory premise. -/
theorem any_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (cells : Find.HeaderData source table p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (order : List Nat) (room : order.length<2^bits)
    (binary : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (mapped : ∀ i<2^bits,∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress (p.keys+BitVec.ofNat 64 i*p.stride) offset)))
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (getCode : source.code.lookup (ofString "htab_get")=some (Get.formals,Get.body,Get.pairShape))
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (hashCell : source.locals.lookup (ofString "hash")=some (.val (.word p.key))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤6*order.length+3 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "db",localVar "hash"]=
      some [.val (.word table),.val (.word p.key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,hashCell]
  obtain ⟨callee,called,tCell,keyCell⟩ := Get.environment source.code.lookup table p.key getCode
  let entry:=callEntryStateHOLFinite source callee
  have entryCells : Find.HeaderCells entry table p := ⟨tCell,keyCell,cells.mapped,cells.capacity,cells.keyLength,cells.stride,cells.keys,cells.used⟩
  have price:=Get.any_body_cost entry table p entryCells keyLength bits small capacity order room binary covered fits mapped hashCode memeqCode findCode
  have caller:=Input.ClockCost.scoped_current source (ofString "r") Get.pairShape (ofString "htab_get") [localVar "db",localVar "hash"] _ Get.body afterGet callee Get.pairShape
    (6*order.length+2) 0 args called price (Input.ClockCost.of_quiet source.code _ (tail_decision.quiet source.code))
  rw [body_shape]
  exact caller

theorem any_body_readonly (code)
    (hashCode : code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (getCode : code.lookup (ofString "htab_get")=some (Get.formals,Get.body,Get.pairShape)) : Input.LocalEffects.Preserves code body := by
  rw [body_shape]
  exact Input.LocalEffects.scoped_body code (ofString "r") Get.pairShape (ofString "htab_get") [localVar "db",localVar "hash"] afterGet Get.formals Get.body Get.pairShape
    getCode (Get.any_body_readonly code hashCode memeqCode findCode)
    (Input.LocalEffects.sequence code _ _ (Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.returned code _) (Input.LocalEffects.skip code)) (Input.LocalEffects.returned code _))

end InitECandidate.Solver.MutableTable.NodeDb

#print axioms InitECandidate.Solver.MutableTable.NodeDb.tail_decision
#print axioms InitECandidate.Solver.MutableTable.NodeDb.any_body_cost
#print axioms InitECandidate.Solver.MutableTable.NodeDb.any_body_readonly
