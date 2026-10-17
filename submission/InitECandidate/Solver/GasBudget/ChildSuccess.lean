import InitECandidate.Solver.GasBudget.ChildSuccessProgram

namespace InitECandidate.Solver.GasBudget.ChildSuccess
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Successful child incorporation through the real spill repayment. Following
log/delete-table work stays as a continuation: its memory frame is still needed. -/
theorem execute_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64)
    (p c : ChildError.Amounts) (parentSpill childSpill : BitVec 64)
    (ready : Ready source parent child p c parentSpill childSpill)
    (code : source.code.lookup (ofString "incorporate_child_on_error")=some (ChildError.formals,ChildError.body,.one))
    (fits : regularBudget source.memory parent+regularBudget source.memory child<2^64) (enough : 1≤source.clock) :
    ∃ target,
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1} ∧
      regularBudget target.memory parent=regularBudget source.memory parent+regularBudget source.memory child ∧
      (∀ name : String,ofString "rep"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      (∀ continuation,evaluateHOLFiniteState source (program continuation)=
        (let output:=evaluateHOLFiniteState target continuation
        (output.1,restore source "rep" output.2))) := by
  classical
  have pGas : source.memory (parent+64#64)=.word p.gas:=ready.parentCells 64 (by simp [ChildError.offsets])
  have pUsed : source.memory (parent+184#64)=.word p.used:=ready.parentCells 184 (by simp [ChildError.offsets])
  have cGas : source.memory (child+64#64)=.word c.gas:=ready.childCells 64 (by simp [ChildError.offsets])
  have cUsed : source.memory (child+184#64)=.word c.used:=ready.childCells 184 (by simp [ChildError.offsets])
  have total : p.gas.toNat+p.used.toNat+parentSpill.toNat+(c.gas.toNat+c.used.toNat+childSpill.toNat)<2^64 := by
    simpa only [regularBudget,wordAt,pGas,pUsed,cGas,cUsed,ready.parentSpillCell,ready.childSpillCell,WitnessRadix.MemoryBytes.wordBits] using fits
  have gasFits : p.gas.toNat+c.gas.toNat<2^64:=by omega
  have usedFits : p.used.toNat+c.used.toNat<2^64:=by omega
  have spillFits : parentSpill.toNat+childSpill.toNat<2^64:=by omega
  have repayFits : (p.gas+c.gas).toNat+(parentSpill+childSpill).toNat<2^64 := by
    rw [BitVec.toNat_add_of_lt gasFits,BitVec.toNat_add_of_lt spillFits]
    omega
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "child"]=some [.val (.word child)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,ready.childLocal]
  obtain ⟨callee,called,childLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "incorporate_child_on_error") "child" ChildError.body child code
  let entry:=callEntryStateHOLFinite source callee
  have enteredReady : ChildError.Ready entry parent child p c:=
    ⟨ready.ev,childLocal,ready.parentMapped,ready.childMapped,ready.parentCells,ready.childCells,ready.separate⟩
  have run:=ChildError.execute entry parent child p c enteredReady
  let memory:=WitnessRadix.WordWrites.write source.memory (ChildError.writes parent p c)
  let returned:={source with memory:=memory,clock:=source.clock-1}
  have frameEq : emptyLocalsHOLFinite (emptyLocalsHOLFinite {entry with memory:=memory})=emptyLocalsHOLFinite returned:=rfl
  have callRun:=ignored_return source _ _ [localVar "child"] _ ChildError.body callee 1 args called enough run frameEq
  have parentSpillR : returned.memory (parent+192#64)=.word parentSpill := by
    change WitnessRadix.WordWrites.write source.memory (ChildError.writes parent p c) (parent+192#64)=.word parentSpill
    rw [WitnessRadix.WordWrites.write_away]
    · exact ready.parentSpillCell
    · simp [ChildError.writes,offsets_ne parent 192#64 64#64 (by decide),offsets_ne parent 192#64 72#64 (by decide),offsets_ne parent 192#64 184#64 (by decide)]
  have childSpillR : returned.memory (child+192#64)=.word childSpill := by
    change WitnessRadix.WordWrites.write source.memory (ChildError.writes parent p c) (child+192#64)=.word childSpill
    rw [WitnessRadix.WordWrites.write_away]
    · exact ready.childSpillCell
    · simp only [ChildError.writes,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨Ne.symm (ready.childSpillSeparate 64 (by simp [ChildError.offsets])),
        Ne.symm (ready.childSpillSeparate 72 (by simp [ChildError.offsets])),
        Ne.symm (ready.childSpillSeparate 184 (by simp [ChildError.offsets]))⟩
  have spillRun:=ChildError.sum_execute returned parent child 192#64 parentSpill childSpill ready.ev ready.childLocal
    ready.parentSpillMapped ready.childSpillMapped parentSpillR childSpillR
  let merged:={returned with memory:=WitnessRadix.StoreWord.put returned.memory (parent+192#64) (parentSpill+childSpill)}
  have distinct : ((ChildError.writes parent p c).map Prod.fst).Nodup := by
    simp [ChildError.writes,offsets_ne parent 64#64 72#64 (by decide),offsets_ne parent 64#64 184#64 (by decide),offsets_ne parent 72#64 184#64 (by decide)]
  have gasR : returned.memory (parent+64#64)=.word (p.gas+c.gas):=
    WitnessRadix.WordWrites.write_unique source.memory (ChildError.writes parent p c) (parent+64#64,p.gas+c.gas) distinct (by simp [ChildError.writes])
  have stateR : returned.memory (parent+72#64)=.word (p.state+c.state):=
    WitnessRadix.WordWrites.write_unique source.memory (ChildError.writes parent p c) (parent+72#64,p.state+c.state) distinct (by simp [ChildError.writes])
  have gasM : merged.memory (parent+64#64)=.word (p.gas+c.gas):=ChildError.stored_away returned.memory _ _ _ _
    (offsets_ne parent 64#64 192#64 (by decide)) gasR
  have stateM : merged.memory (parent+72#64)=.word (p.state+c.state):=ChildError.stored_away returned.memory _ _ _ _
    (offsets_ne parent 72#64 192#64 (by decide)) stateR
  have spillM : merged.memory (parent+192#64)=.word (parentSpill+childSpill) := by simp [merged,WitnessRadix.StoreWord.put]
  have mappedM : ∀ offset∈([64,72,192] : List Nat),merged.memaddrs (parent+BitVec.ofNat 64 offset) := by
    intro offset member
    have choices : offset=64 ∨ offset=72 ∨ offset=192:=by simpa using member
    rcases choices with rfl|rfl|rfl
    · exact ready.parentMapped 64 (by simp [ChildError.offsets])
    · exact ready.parentMapped 72 (by simp [ChildError.offsets])
    · exact ready.parentSpillMapped
  obtain ⟨target,memoryEq,repayFrame,locals,repayRun⟩:=Repayment.execute merged parent (p.gas+c.gas) (p.state+c.state) (parentSpill+childSpill)
    ready.ev mappedM gasM stateM spillM
  have transfer:=ChildError.budget_transfer source parent child p c ready.toReady gasFits usedFits
  have mergeBudget : regularBudget merged.memory parent=regularBudget returned.memory parent+childSpill.toNat := by
    simp only [regularBudget,wordAt,merged,WitnessRadix.StoreWord.put,
      if_neg (offsets_ne parent 64#64 192#64 (by decide)),if_neg (offsets_ne parent 184#64 192#64 (by decide)),if_pos rfl,
      parentSpillR,ite_true,WitnessRadix.MemoryBytes.wordBits]
    change (wordAt returned.memory (parent+64#64)).toNat+(wordAt returned.memory (parent+184#64)).toNat+
      (parentSpill+childSpill).toNat=
      (wordAt returned.memory (parent+64#64)).toNat+(wordAt returned.memory (parent+184#64)).toNat+parentSpill.toNat+childSpill.toNat
    rw [BitVec.toNat_add_of_lt spillFits]
    omega
  have repayBudget:=Repayment.preserves_regular_budget merged.memory parent (p.gas+c.gas) (p.state+c.state) (parentSpill+childSpill) gasM spillM repayFits
  refine ⟨target,repayFrame,?_,locals,?_⟩
  · rw [memoryEq,repayBudget,mergeBudget]
    change regularBudget memory parent+childSpill.toNat=regularBudget source.memory parent+regularBudget source.memory child
    simpa only [wordAt,ready.childSpillCell,WitnessRadix.MemoryBytes.wordBits] using transfer
  · intro continuation
    rw [program,WitnessRadix.StateSteps.next_sequence source returned _ _ callRun (by change source.clock-1≤source.clock;omega),
      WitnessRadix.StateSteps.next_sequence returned merged _ _ spillRun (Nat.le_refl _)]
    simpa only [restore,returned,merged] using repayRun continuation

end InitECandidate.Solver.GasBudget.ChildSuccess

#print axioms InitECandidate.Solver.GasBudget.ChildSuccess.execute_prefix
