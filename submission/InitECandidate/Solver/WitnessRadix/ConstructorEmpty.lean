import InitECandidate.Solver.WitnessRadix.ConstructorPlan

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real zero-record constructor accepts any record pointer, including
zero returned by the empty SSZ decoder. It reads no records or hash buffers.
The positive logical record arena below is unused because its extent is zero. -/
theorem execute_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : Nat)
    (tableLower : 2701131776≤table) (tableAligned : table%8=0) (room : table+307≤33806089496)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word 0#64)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (helperCode : source.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one))
    (enough : 47≤source.clock) :
    ∃ target root,
      let layout:=AllocatedLayout.layout (allocationPlan table table 0 4)
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 table)))),target) ∧
      target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24)=.word root ∧
      QueryMemory.Represents target layout.table layout.keys layout.vals root
        (initialTree (fun _ _=>0#8) (fun _=>(0#64,0#64)) (ordinals 0)) ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (table+304)))) ∧
      source.clock-43≤target.clock ∧ target.clock≤source.clock := by
  classical
  obtain ⟨capped,paid,capacity,capRun,paidBound,sufficient,capBound,capTop,shape,capLocal,capFrame,capOther⟩:=
    capacity_entry source 0 (by decide) countLocal (by omega)
  have capFour : capacity=4 := by rcases shape with four|aligned; exact four; omega
  subst capacity
  let plan:=allocationPlan table table 0 4
  let layout:=AllocatedLayout.layout plan
  have ready : AllocatedLayout.Ready plan:=allocation_ready table table 0 4 tableLower (by omega) tableAligned tableAligned (by omega)
    sufficient capBound (Or.inl rfl)
  have capClock:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.clock) capFrame
  change capped.clock=source.clock-paid at capClock
  have capDomain:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memaddrs) capFrame
  change capped.memaddrs=source.memaddrs at capDomain
  have capCode:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.code) capFrame
  change capped.code=source.code at capCode
  have capGlobals:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals) capFrame
  change capped.globals=source.globals at capGlobals
  have tablePrice : TableNew.price 4+1=12 := by simp [TableNew.price,TableNew.clearCost]
  obtain ⟨restoreStack,restoreFrame,prepareRun⟩:=prepare_execute_framed capped plan ready (capDomain.trans domain) (Or.inl rfl)
    capLocal (by rw [capGlobals]; exact heapGlobal) (by rw [capCode]; exact tableCode) (by rw [capCode]; exact allocCode)
    (by rw [capCode]; exact zeroCode) (by change TableNew.price 4+1≤capped.clock; rw [tablePrice]; omega)
  change evaluateHOLFiniteState capped allocatedTail=_ at prepareRun
  let called:=TableNew.callState capped "t" plan
  let entered:=preparedState capped plan
  have fixedCalled : FixedData called layout (fun _=>(0#64,0#64)):=TableNew.call_fixed_data capped "t" plan ready (capDomain.trans domain)
    (fun _=>(0#64,0#64)) (by intro index inside; change index<0 at inside; omega) (by intro index inside; change index<0 at inside; omega)
  have fixed : FixedData entered layout (fun _=>(0#64,0#64)):=fixed_of_fields called entered layout _ rfl rfl fixedCalled
  have mapped : Mapped entered layout:=AllocatedLayout.mapped capped plan ready (capDomain.trans domain)
  have tableLocal : entered.locals.lookup (ofString "t")=some (.val (.word layout.table)) :=
    (array_lookup_other called layout "t" (by decide) (by decide) (by decide) (by decide)).trans (bind_lookup_same _ _ _)
  have nLocal : entered.locals.lookup (ofString "n")=some (.val (.word 0#64)) :=
    (array_lookup_other called layout "n" (by decide) (by decide) (by decide) (by decide)).trans
      ((bind_lookup_other _ "t" "n" _ (by decide)).trans ((capOther (ofString "n") (by decide)).trans countLocal))
  have iLocal : entered.locals.lookup (ofString "i")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have test : evalHOLFinite entered condition=some (.val (.word 0#64)) := by
    simp [evalHOLFinite,condition,localVar,evalHOLExact,toExact,iLocal,nLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have loopRun : evaluateHOLFiniteState entered recordLoop=(none,entered) := by
    rw [loop_shape,evaluateHOLFiniteState_while_total,test]
    simp
  have entryClock : entered.clock=capped.clock-12 := by
    change capped.clock-(TableNew.price 4+1)=capped.clock-12
    rw [tablePrice]
  obtain ⟨filled,root,finishRun,rootMapped,rootWord,represented,controls,lower,upper⟩:=finish entered layout (AllocatedLayout.valid plan ready)
    mapped (fun _ _=>0#8) (fun _=>(0#64,0#64)) fixed (prefix_empty entered layout _) tableLocal nLocal
    (by change capped.code.lookup _=_; rw [capCode]; exact helperCode) (by change 1≤entered.clock; omega)
  have fullTail : evaluateHOLFiniteState entered (.seq recordLoop afterRecords)=(some (.returned (.val (.word layout.table))),filled) :=
    (StateSteps.next_sequence entered entered _ _ loopRun (Nat.le_refl _)).trans finishRun
  let target:=restore source "cap" (restore capped "t" (restoreStack filled))
  have restored : emptyLocalsHOLFinite target=emptyLocalsHOLFinite filled := by
    change emptyLocalsHOLFinite (restoreStack filled)=emptyLocalsHOLFinite filled
    exact restoreFrame filled
  have memory:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memory) restored
  have domains:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memaddrs) restored
  have endian:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.be) restored
  have clock:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.clock) restored
  have globals:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals) restored
  have filledGlobals:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals) controls
  change target.memory=filled.memory at memory
  change target.memaddrs=filled.memaddrs at domains
  change target.be=filled.be at endian
  change target.globals=filled.globals at globals
  change filled.globals=entered.globals at filledGlobals
  refine ⟨target,root,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [capRun,prepareRun,fullTail]
    rfl
  · rw [domains]; exact rootMapped
  · rw [memory]; exact rootWord
  · exact QueryMemory.represents_of_fields filled target memory.symm domains.symm endian.symm _ _ _ _ _ represented
  · change target.globals.lookup _=_
    rw [globals,filledGlobals]
    change (capped.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*4+4))))).lookup _=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · change source.clock-43≤target.clock
    change entered.clock-1≤filled.clock at lower
    change target.clock=filled.clock at clock
    omega
  · change target.clock≤source.clock
    change target.clock=filled.clock at clock
    omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.execute_empty
