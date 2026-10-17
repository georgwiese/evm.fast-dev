import InitECandidate.Solver.MutableTable.GetDictionary32
import InitECandidate.Solver.MutableTable.PureValueCall

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def pairShape : ShapeHOL:=.comb [.one,.one]

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (table key : BitVec 64)
    (code : codeFn (ofString "htab_get")=some (formals,body,pairShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htab_get") [.val (.word table),.val (.word key)]=some (body,callee,pairShape) ∧
      callee.lookup (ofString "t")=some (.val (.word table)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word table),.val (.word key)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word table),.val (.word key)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,Find.formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "htab_get") [.val (.word table),.val (.word key)]=some (body,Find.rawLocals table key,pairShape) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [Find.rawLocals,show ofString "t"≠ofString "key" from by decide]
  · simp [Find.rawLocals]

/-- Actual original get caller, returning the represented pair at all query
alignments. Caller parameter names are unrestricted; header data is physical. -/
theorem dictionary32_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tableAddress : BitVec 64) (p : Find.Parameters)
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
    (getCode : source.code.lookup (ofString "htab_get")=some (formals,body,pairShape))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word tableAddress),.val (.word p.key)])
    (enough : 6*order.length+3≤source.clock) :
    ∃ paid,paid≤6*order.length+3 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "htab_get") expressions continuation)=
        (let result:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) (output (dictionary query)) {source with clock:=source.clock-paid}) continuation
        (result.1,restore source name result.2)) := by
  obtain ⟨callee,called,tLocal,keyLocal⟩:=environment source.code.lookup tableAddress p.key getCode
  let entry:=callEntryStateHOLFinite source callee
  have entryCells:=Find.HeaderData.with_locals source entry tableAddress p cells rfl rfl tLocal keyLocal
  have queryEntry:=WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ queryView
  have entryModel : Find.KeyModel32 entry p (2^bits) table := by
    constructor
    · exact model.used
    · intro i inside key value cell
      exact WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ (model.view i inside key value cell)
  obtain ⟨paid,target,bound,run,frame⟩:=dictionary32_get entry tableAddress p entryCells keyLength bits small capacity table entryModel dictionary rep placed order room covered fits query queryEntry queryFits little hashCode memeqCode findCode vals valsMapped valsCell values
    (by change 6*order.length+2≤source.clock-1;omega)
  have shapePass : (shapeEqHOL (shapeOfHOLExact (output (dictionary query))) pairShape && shapeEqHOL (shapeOfHOLExact (output (dictionary query))) pairShape)=true := by
    cases selected : dictionary query <;> simp [output,pair,pairShape,shapeOfHOLExact,shapeEqHOL_eq_true]
  have callerFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}:=frame
  have actual:=pure_value_call source target name (ofString "htab_get") pairShape pairShape expressions _ body continuation callee (output (dictionary query)) paid args called (by omega) run shapePass callerFrame
  have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
  exact ⟨paid+1,by omega,by simpa only [subtract] using actual⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.environment
#print axioms InitECandidate.Solver.MutableTable.Get.dictionary32_call
