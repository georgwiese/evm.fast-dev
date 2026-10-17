import InitECandidate.Solver.GasBudget.RegularCharge

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem quantitative (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used amount : BitVec 64)
    (gasCell : source.memory (frame+64#64)=.word gas) (usedCell : source.memory (frame+184#64)=.word used)
    (affordable : amount≤gas) (fits : gas.toNat+used.toNat<2^64) :
    let memory:=WitnessRadix.WordWrites.write source.memory (writes frame gas used amount)
    regularBudget memory frame=regularBudget source.memory frame ∧
      (wordAt memory (frame+64#64)).toNat+amount.toNat=gas.toNat ∧
      (wordAt memory (frame+184#64)).toNat=used.toNat+amount.toNat := by
  have distinct : ((writes frame gas used amount).map Prod.fst).Nodup := by
    simp [writes,offsets_ne frame 64#64 184#64 (by decide)]
  have gasAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes frame gas used amount) (frame+64#64,gas-amount) distinct (by simp [writes])
  have usedAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes frame gas used amount) (frame+184#64,used+amount) distinct (by simp [writes])
  have spillAfter:=WitnessRadix.WordWrites.write_away source.memory (writes frame gas used amount) (frame+192#64)
    (by simp [writes,offsets_ne frame 192#64 64#64 (by decide),offsets_ne frame 192#64 184#64 (by decide)])
  have amountBound : amount.toNat≤gas.toNat:=affordable
  have sumFits : used.toNat+amount.toNat<2^64 := by omega
  refine ⟨?_,?_,?_⟩
  · simp only [regularBudget,wordAt,gasAfter,usedAfter,spillAfter,gasCell,usedCell,WitnessRadix.MemoryBytes.wordBits]
    change (gas-amount).toNat+(used+amount).toNat+(wordAt source.memory (frame+192#64)).toNat=
      gas.toNat+used.toNat+(wordAt source.memory (frame+192#64)).toNat
    rw [BitVec.toNat_sub_of_le affordable,BitVec.toNat_add_of_lt sumFits]
    omega
  · simp only [wordAt,gasAfter,WitnessRadix.MemoryBytes.wordBits,BitVec.toNat_sub_of_le affordable]
    omega
  · simp only [wordAt,usedAfter,WitnessRadix.MemoryBytes.wordBits,BitVec.toNat_add_of_lt sumFits]

/-- Actual source charge caller with exact natural debit/used-counter credit.
This supplies the source gas invariant while the existing Stack theorem prices
its compiled charge routine; connecting the whole execution remains open. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used amount : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word amount)])
    (code : source.code.lookup (ofString "charge_gas")=some (formals,body,.one))
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (gasMapped : source.memaddrs (frame+64#64)) (usedMapped : source.memaddrs (frame+184#64))
    (gasCell : source.memory (frame+64#64)=.word gas) (usedCell : source.memory (frame+184#64)=.word used)
    (affordable : amount≤gas) (fits : gas.toNat+used.toNat<2^64) (enough : 1≤source.clock) :
    ∃ memory,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "charge_gas") expressions)=
        (none,{source with memory:=memory,clock:=source.clock-1}) ∧
      regularBudget memory frame=regularBudget source.memory frame ∧
      (wordAt memory (frame+64#64)).toNat+amount.toNat=gas.toNat ∧
      (wordAt memory (frame+184#64)).toNat=used.toNat+amount.toNat := by
  obtain ⟨callee,called,amountLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "charge_gas") "amount" body amount code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,run,memory,frameEq⟩:=execute entry frame gas used amount ev amountLocal gasMapped usedMapped gasCell usedCell affordable
  refine ⟨target.memory,ignored_return source target _ expressions _ body callee 1 args called enough run frameEq,?_⟩
  rw [memory]
  exact quantitative source frame gas used amount gasCell usedCell affordable fits

theorem failed_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas amount : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word amount)])
    (code : source.code.lookup (ofString "charge_gas")=some (formals,body,.one))
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (gasMapped : source.memaddrs (frame+64#64)) (gasCell : source.memory (frame+64#64)=.word gas)
    (unaffordable : gas<amount) (exceptionShape : source.eshapes.lookup (ofString "EvmErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "charge_gas") expressions)=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1}) := by
  obtain ⟨callee,called,amountLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "charge_gas") "amount" body amount code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,run,frameEq⟩:=failed entry frame gas amount ev amountLocal gasMapped gasCell unaffordable exceptionShape
  have actual:=evaluateHOLFiniteState_call_exception_no_handler source none (ofString "charge_gas") expressions [.val (.word amount)] body callee .one
    (ofString "EvmErr") (.val (.word 4#64)) target args called (by omega) run
  rw [frameEq] at actual
  exact actual

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.quantitative
#print axioms InitECandidate.Solver.GasBudget.RegularCharge.call_execute
#print axioms InitECandidate.Solver.GasBudget.RegularCharge.failed_call
