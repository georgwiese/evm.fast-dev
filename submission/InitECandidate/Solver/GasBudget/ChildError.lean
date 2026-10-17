import InitECandidate.Solver.GasBudget.ChildErrorProgram

namespace InitECandidate.Solver.GasBudget.ChildError
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual child-error incorporation, with read/write separation supplied by
the frame layout. All three parent stores and the literal return execute. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64) (p c : Amounts)
    (ready : Ready source parent child p c) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),
      emptyLocalsHOLFinite {source with memory:=WitnessRadix.WordWrites.write source.memory (writes parent p c)}) := by
  classical
  have firstRun:=sum_execute source parent child 64#64 p.gas c.gas ready.ev ready.childLocal
    (ready.parentMapped 64 (by simp [offsets])) (ready.childMapped 64 (by simp [offsets]))
    (ready.parentCells 64 (by simp [offsets])) (ready.childCells 64 (by simp [offsets]))
  let first:={source with memory:=WitnessRadix.StoreWord.put source.memory (parent+64#64) (p.gas+c.gas)}
  have parent72 : first.memory (parent+72#64)=.word p.state:=stored_away source.memory _ _ _ _
    (offsets_ne parent 72#64 64#64 (by decide)) (ready.parentCells 72 (by simp [offsets]))
  have child72 : first.memory (child+72#64)=.word c.state:=stored_away source.memory _ _ _ _
    (Ne.symm (ready.separate 64 (by simp [offsets]) 72 (by simp [offsets]))) (ready.childCells 72 (by simp [offsets]))
  have secondRun:=sum_execute first parent child 72#64 p.state c.state ready.ev ready.childLocal
    (ready.parentMapped 72 (by simp [offsets])) (ready.childMapped 72 (by simp [offsets])) parent72 child72
  let second:={first with memory:=WitnessRadix.StoreWord.put first.memory (parent+72#64) (p.state+c.state)}
  have parent184First : first.memory (parent+184#64)=.word p.used:=stored_away source.memory _ _ _ _
    (offsets_ne parent 184#64 64#64 (by decide)) (ready.parentCells 184 (by simp [offsets]))
  have parent184 : second.memory (parent+184#64)=.word p.used:=stored_away first.memory _ _ _ _
    (offsets_ne parent 184#64 72#64 (by decide)) parent184First
  have child184First : first.memory (child+184#64)=.word c.used:=stored_away source.memory _ _ _ _
    (Ne.symm (ready.separate 64 (by simp [offsets]) 184 (by simp [offsets]))) (ready.childCells 184 (by simp [offsets]))
  have child184 : second.memory (child+184#64)=.word c.used:=stored_away first.memory _ _ _ _
    (Ne.symm (ready.separate 72 (by simp [offsets]) 184 (by simp [offsets]))) child184First
  have thirdRun:=sum_execute second parent child 184#64 p.used c.used ready.ev ready.childLocal
    (ready.parentMapped 184 (by simp [offsets])) (ready.childMapped 184 (by simp [offsets])) parent184 child184
  let third:={second with memory:=WitnessRadix.StoreWord.put second.memory (parent+184#64) (p.used+c.used)}
  rw [body_shape,WitnessRadix.StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence second third _ _ thirdRun (Nat.le_refl _)]
  simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rfl

/-- Incorporation transfers the child's liquid/used regular gas. Its spill is
omitted on the error path; after actual refill that omitted spill is zero. -/
theorem budget_transfer (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64) (p c : Amounts)
    (ready : Ready source parent child p c)
    (gasFits : p.gas.toNat+c.gas.toNat<2^64) (usedFits : p.used.toNat+c.used.toNat<2^64) :
    regularBudget (WitnessRadix.WordWrites.write source.memory (writes parent p c)) parent+
        (wordAt source.memory (child+192#64)).toNat=
      regularBudget source.memory parent+regularBudget source.memory child := by
  have d6472:=offsets_ne parent 64#64 72#64 (by decide)
  have d64184:=offsets_ne parent 64#64 184#64 (by decide)
  have d72184:=offsets_ne parent 72#64 184#64 (by decide)
  have distinct : ((writes parent p c).map Prod.fst).Nodup := by simp [writes,d6472,d64184,d72184]
  have gasAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes parent p c) (parent+64#64,p.gas+c.gas) distinct (by simp [writes])
  have usedAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes parent p c) (parent+184#64,p.used+c.used) distinct (by simp [writes])
  have spillAfter:=WitnessRadix.WordWrites.write_away source.memory (writes parent p c) (parent+192#64)
    (by simp [writes,offsets_ne parent 192#64 64#64 (by decide),offsets_ne parent 192#64 72#64 (by decide),offsets_ne parent 192#64 184#64 (by decide)])
  have pGas : source.memory (parent+64#64)=.word p.gas:=ready.parentCells 64 (by simp [offsets])
  have pUsed : source.memory (parent+184#64)=.word p.used:=ready.parentCells 184 (by simp [offsets])
  have cGas : source.memory (child+64#64)=.word c.gas:=ready.childCells 64 (by simp [offsets])
  have cUsed : source.memory (child+184#64)=.word c.used:=ready.childCells 184 (by simp [offsets])
  simp only [regularBudget,wordAt,gasAfter,usedAfter,spillAfter,pGas,pUsed,cGas,cUsed,WitnessRadix.MemoryBytes.wordBits]
  change ((p.gas+c.gas).toNat+(p.used+c.used).toNat+(wordAt source.memory (parent+192#64)).toNat)+
    (wordAt source.memory (child+192#64)).toNat=
    (p.gas.toNat+p.used.toNat+(wordAt source.memory (parent+192#64)).toNat)+
    (c.gas.toNat+c.used.toNat+(wordAt source.memory (child+192#64)).toNat)
  rw [BitVec.toNat_add_of_lt gasFits,BitVec.toNat_add_of_lt usedFits]
  omega

end InitECandidate.Solver.GasBudget.ChildError

#print axioms InitECandidate.Solver.GasBudget.ChildError.execute
#print axioms InitECandidate.Solver.GasBudget.ChildError.budget_transfer
