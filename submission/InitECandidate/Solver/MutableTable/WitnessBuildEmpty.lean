import InitECandidate.Solver.MutableTable.WitnessBuildPrepare
import InitECandidate.Solver.MutableTable.WitnessBuildCapacity
import InitECandidate.Solver.WitnessAllocationPlan

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual original constructor on zero records reads neither the record
pointer nor the hash buffers. The logical record arena has zero extent. -/
theorem execute_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : Nat)
    (tableLower : 2701131776≤table) (tableAligned : table%8=0) (room : table+307≤33806089496)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word 0#64)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (scratch : BitVec 64) (enough : 47≤source.clock) :
    ∃ target,
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 table)))),target) ∧
      Layout32.Built 2 target (Constructor.allocationPlan table table 0 4) scratch 0 [] (fun _=>none) ∧
      target.ffi=source.ffi ∧
      target.globals=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+304)))) ∧
      (∀ query,query.toNat<table→target.memory query=source.memory query) ∧
      source.clock-42≤target.clock ∧ target.clock≤source.clock := by
  classical
  obtain ⟨capped,paid,bits,capRun,paidBound,lower,upper,sufficient,capBound,capLocal,capFrame,capOther⟩:=
    capacity_entry source 0 (by decide) countLocal (by omega)
  have capFour : 2^bits=4 := by
    have atLeast : 4≤2^bits:=by have:=Nat.pow_le_pow_right (by decide : 0<2) lower; exact this
    omega
  let plan:=Constructor.allocationPlan table table 0 4
  have ready : AllocatedLayout.Ready plan:=Constructor.allocation_ready table table 0 4 tableLower (by omega)
    tableAligned tableAligned (by omega) (by omega) (by omega) (Or.inl rfl)
  have capClock : capped.clock=source.clock-paid:=congrArg (fun state=>state.clock) capFrame
  have capDomain : capped.memaddrs=source.memaddrs:=congrArg (fun state=>state.memaddrs) capFrame
  have capCode : capped.code=source.code:=congrArg (fun state=>state.code) capFrame
  have capGlobals : capped.globals=source.globals:=congrArg (fun state=>state.globals) capFrame
  have capLittle : capped.be=false := (congrArg (fun state=>state.be) capFrame).trans little
  have tablePrice : TableNew.price 4+1=12 := by simp [TableNew.price,TableNew.clearCost]
  have prepareRun:=prepare_execute capped plan ready (capDomain.trans domain) (Or.inl rfl)
    (by change capped.locals.lookup _=some (.val (.word (BitVec.ofNat 64 4))); rw [capFour] at capLocal;exact capLocal)
    (by rw [capGlobals];exact heapGlobal) (by rw [capCode];exact tableCode)
    (by rw [capCode];exact allocCode) (by rw [capCode];exact zeroCode)
    (by change TableNew.price 4+1≤capped.clock;rw [tablePrice];omega)
  change evaluateHOLFiniteState capped allocatedTail=_ at prepareRun
  let called:=TableNew.callState capped "t" plan
  let entered:=prepared capped plan
  have tableLocal : entered.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 table))) :=
    (bind_lookup_other called "i" "t" _ (by decide)).trans (bind_lookup_same _ _ _)
  have nLocal : entered.locals.lookup (ofString "n")=some (.val (.word 0#64)) :=
    (bind_lookup_other called "i" "n" _ (by decide)).trans
      ((bind_lookup_other _ "t" "n" _ (by decide)).trans ((capOther (ofString "n") (by decide)).trans countLocal))
  have iLocal : entered.locals.lookup (ofString "i")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have test : evalHOLFinite entered Constructor.condition=some (.val (.word 0#64)) := by
    simp [evalHOLFinite,Constructor.condition,localVar,evalHOLExact,toExact,iLocal,nLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have loopRun : evaluateHOLFiniteState entered recordLoop=(none,entered) := by
    unfold recordLoop
    rw [evaluateHOLFiniteState_while_total,test]
    simp
  have returnRun : evaluateHOLFiniteState entered (.return (localVar "t"))=
      (some (.returned (.val (.word (BitVec.ofNat 64 table)))),emptyLocalsHOLFinite entered) := by
    simp [evaluateHOLFiniteState_return,localVar,evalHOLExact,toExact,tableLocal,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have tailRun := (StateSteps.next_sequence entered entered recordLoop (.return (localVar "t")) loopRun (Nat.le_refl _)).trans returnRun
  let target:=restore source "cap" (finishScope capped plan (emptyLocalsHOLFinite entered))
  have initial:=Layout32.initial_built capped plan ready (capDomain.trans domain) (Or.inl rfl) capLittle 2 scratch
  have built:=Layout32.built_fields (TableNew.enteredState capped plan) target plan 2 scratch 0 [] (fun _=>none) rfl rfl rfl initial
  have capMemory : capped.memory=source.memory:=congrArg (fun state=>state.memory) capFrame
  have entryClock : entered.clock=capped.clock-12 := by
    change capped.clock-(TableNew.price 4+1)=capped.clock-12
    rw [tablePrice]
  refine ⟨target,?_,built,?_,?_,?_,?_,?_⟩
  · rw [capRun,prepareRun,tailRun]
  · exact congrArg (fun state=>state.ffi) capFrame
  · change capped.globals.update _=source.globals.update _
    rw [capGlobals]
    rfl
  · intro query earlier
    change TableNew.resultMemory capped.memory capped.be plan query=source.memory query
    rw [TableNew.result_earlier _ _ plan ready query earlier,capMemory]
  · change source.clock-42≤entered.clock
    omega
  · change entered.clock≤source.clock
    omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.execute_empty
