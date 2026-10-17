import InitECandidate.Solver.MutableTable.GetTail32
import InitECandidate.Solver.MutableTable.HeaderData

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original htab_get from the represented logical dictionary, including
actual find/hash/memeq/value-cell reads and all scopes. This is conditional on
the explicit physical table/placement/ownership and clock entry premises. -/
theorem dictionary32_get (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tableAddress : BitVec 64) (p : Find.Parameters)
    (cells : Find.HeaderCells source tableAddress p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (table : Find.Model32 (BitVec 64)) (model : Find.KeyModel32 source p (2^bits) table)
    (dictionary : Find.Key32→Option (BitVec 64)) (rep : Placement.Represents (2^bits) table dictionary)
    (placed : Placement.NoGaps (2^bits) (Find.hashHome bits) table)
    (order : List Nat) (room : order.length<2^bits) (covered : ∀ i<2^bits,table i≠none→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (query : Find.Key32) (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query)
    (queryFits : p.key.toNat+32<2^64) (little : source.be=false)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (vals : BitVec 64) (valsMapped : source.memaddrs (tableAddress+40#64))
    (valsCell : source.memory (tableAddress+40#64)=.word vals)
    (values : ∀ i<2^bits,∀ key value,table i=some (key,value)→
      source.memaddrs (vals+BitVec.ofNat 64 i*8#64) ∧ source.memory (vals+BitVec.ofNat 64 i*8#64)=.word value)
    (enough : 6*order.length+2≤source.clock) :
    ∃ paid target,paid≤6*order.length+2 ∧
      evaluateHOLFiniteState source body=(some (.returned (output (dictionary query))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t",localVar "key"]=some [.val (.word tableAddress),.val (.word p.key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,cells.tableLocal,cells.keyLocal]
  obtain ⟨paid,index,bound,spec,callRun⟩:=Find.dictionary32_call source tableAddress p cells keyLength bits small capacity table model dictionary rep placed order room covered fits query queryView queryFits little hashCode memeqCode findCode
    "i" [localVar "t",localVar "key"] afterIndex args enough
  let entered:=bind {source with clock:=source.clock-paid} "i" index
  have tEntered : entered.locals.lookup (ofString "t")=some (.val (.word tableAddress)):=
    (bind_lookup_other _ "i" "t" _ (by decide)).trans cells.tableLocal
  have tailRun:=tail32_execute entered tableAddress vals index p.capacity bits small capacity table dictionary query tEntered
    (bind_lookup_same _ _ _) (cells.mapped 16 (by simp)) cells.capacity valsMapped valsCell values spec
  change evaluateHOLFiniteState source (.decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t",localVar "key"] afterIndex)=
    (let result:=evaluateHOLFiniteState entered afterIndex;(result.1,restore source "i" result.2)) at callRun
  rw [tailRun] at callRun
  refine ⟨paid,restore source "i" (emptyLocalsHOLFinite entered),bound,?_,rfl⟩
  rw [body_shape]
  exact callRun

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.dictionary32_get
