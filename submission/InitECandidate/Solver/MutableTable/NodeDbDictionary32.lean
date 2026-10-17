import InitECandidate.Solver.MutableTable.NodeDbTail32

namespace InitECandidate.Solver.MutableTable.NodeDb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original witness lookup, returning the represented preimage slice
for every query, at every alignment. All physical and dictionary premises
remain explicit; construction/refinement still has to establish them. -/
theorem dictionary32_lookup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tableAddress : BitVec 64) (p : Find.Parameters)
    (cells : Find.HeaderData source tableAddress p) (keyLength : p.keyLength=32#64)
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
    (getCode : source.code.lookup (ofString "htab_get")=some (Get.formals,Get.body,Get.pairShape))
    (db : source.locals.lookup (ofString "db")=some (.val (.word tableAddress)))
    (hash : source.locals.lookup (ofString "hash")=some (.val (.word p.key)))
    (slices : BitVec 64→Slice)
    (records : ∀ key record,dictionary key=some record→source.memaddrs record ∧ source.memaddrs (record+8#64) ∧
      source.memory record=.word (slices record).1 ∧ source.memory (record+8#64)=.word (slices record).2)
    (enough : 6*order.length+3≤source.clock) :
    ∃ paid target,paid≤6*order.length+3 ∧
      evaluateHOLFiniteState source body=(some (.returned (output ((dictionary query).map slices))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "db",localVar "hash"]=some [.val (.word tableAddress),.val (.word p.key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,db,hash]
  obtain ⟨paid,bound,callRun⟩:=Get.dictionary32_call source tableAddress p cells keyLength bits small capacity table model dictionary rep placed order room covered fits query queryView queryFits little hashCode memeqCode findCode vals valsMapped valsCell values getCode
    "r" [localVar "db",localVar "hash"] afterGet args enough
  let entered:=setVarHOLFinite (ofString "r") (Get.output (dictionary query)) {source with clock:=source.clock-paid}
  have rEntered : entered.locals.lookup (ofString "r")=some (Get.output (dictionary query)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have tailRun:=tail32_execute entered (dictionary query) slices rEntered (by intro record hit;exact records query record hit)
  change evaluateHOLFiniteState source (.decCall (ofString "r") Get.pairShape (ofString "htab_get") [localVar "db",localVar "hash"] afterGet)=
    (let result:=evaluateHOLFiniteState entered afterGet;(result.1,restore source "r" result.2)) at callRun
  rw [tailRun] at callRun
  refine ⟨paid,restore source "r" (emptyLocalsHOLFinite entered),bound,?_,rfl⟩
  rw [body_shape]
  exact callRun

end InitECandidate.Solver.MutableTable.NodeDb

#print axioms InitECandidate.Solver.MutableTable.NodeDb.dictionary32_lookup
