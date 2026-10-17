import InitECandidate.Solver.MutableTable.FindMemory32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rawLocals (table key : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "key" then some (.val (.word key)) else if name=ofString "t" then some (.val (.word table)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (table key : BitVec 64)
    (code : codeFn (ofString "htab_find_slot")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htab_find_slot") [.val (.word table),.val (.word key)]=some (body,callee,.one) ∧
      callee.lookup (ofString "t")=some (.val (.word table)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word table),.val (.word key)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word table),.val (.word key)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "htab_find_slot") [.val (.word table),.val (.word key)]=some (body,rawLocals table key,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "t"≠ofString "key" from by decide]
  · simp [rawLocals]

/-- Actual two-argument original lookup caller at every key alignment. All
header/hash/scan/return/call clocks are included; memory/control are pure. -/
theorem memory32_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (cells : HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (order : List Nat) (room : order.length<2^bits) (keys : Nat→WitnessRadix.ByteKeys.Key)
    (binary : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (views : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→
      WitnessRadix.MemoryBytes.ByteView source (p.keys+BitVec.ofNat 64 i*p.stride) (keys i))
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (query : WitnessRadix.ByteKeys.Key) (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query)
    (queryFits : p.key.toNat+32<2^64) (little : source.be=false)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (formals,body,.one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word table),.val (.word p.key)])
    (enough : 6*order.length+2≤source.clock) :
    ∃ paid value,paid≤6*order.length+2 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_slot") expressions continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-paid} name value) continuation
        (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,tLocal,keyLocal⟩:=environment source.code.lookup table p.key findCode
  let entry:=callEntryStateHOLFinite source callee
  have entryCells : HeaderCells entry table p:=⟨tLocal,keyLocal,cells.mapped,cells.capacity,cells.keyLength,cells.stride,cells.keys,cells.used⟩
  have queryEntry:=WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ queryView
  have tableViews : ∀ i<2^bits,usedByte entry p (BitVec.ofNat 64 i)=some 1→
      WitnessRadix.MemoryBytes.ByteView entry (p.keys+BitVec.ofNat 64 i*p.stride) (keys i) := by
    intro i inside occupied
    exact WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ (views i inside occupied)
  obtain ⟨paid,value,bound,result,frame⟩:=memory32_find entry table p entryCells keyLength bits small capacity order room keys binary covered tableViews fits query queryEntry queryFits little hashCode memeqCode
    (by change 6*order.length+1≤source.clock-1;omega)
  let post:=(evaluateHOLFiniteState entry body).2
  have run : evaluateHOLFiniteState entry body=(some (.returned (.val (.word value))),post):=Prod.ext result rfl
  have callerFrame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}:=frame
  have actual:=Input.CallNormal.pure_return_execute source post name (ofString "htab_find_slot") expressions _ body continuation callee value paid args called (by omega) run callerFrame
  have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
  exact ⟨paid+1,value,by omega,by simpa only [subtract] using actual⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.environment
#print axioms InitECandidate.Solver.MutableTable.Find.memory32_call
