import InitECandidate.Solver.MutableTable.WitnessBuildEmptyControl
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

set_option maxRecDepth 100000

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Zero records require no readable record pointer or hash-input buffers. -/
structure EmptyReady (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : Nat) : Prop where
  lower : 2701131776≤table
  aligned : table%8=0
  room : table+307≤33806089496
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  count : source.locals.lookup (ofString "n")=some (.val (.word 0#64))
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table)))
  tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one)
  allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one)
  zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one)

theorem EmptyReady.with_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : Nat) (actual : EmptyReady source table) (clock : Nat) :
    EmptyReady {source with clock:=clock} table :=
  ⟨actual.lower,actual.aligned,actual.room,actual.domain,actual.little,actual.count,actual.heap,actual.tableCode,actual.allocCode,actual.zeroCode⟩

/-- All actual empty-constructor outcomes cost at most47 source ticks,
including clocks too small for the known complete execution. -/
theorem empty_body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table : Nat) (scratch : BitVec 64) (actual : EmptyReady source table)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) : source.clock-post.clock≤47 := by
  by_cases enough : 47≤source.clock
  · obtain ⟨target,known,built,ffi,globals,memory,spent,forward,control⟩ := execute_empty_controlled source table actual.lower actual.aligned actual.room actual.domain actual.little actual.count actual.heap actual.tableCode actual.allocCode actual.zeroCode scratch enough
    have endpoint : post=target := congrArg Prod.snd (run.symm.trans known)
    rw [endpoint]
    omega
  · exact (Nat.sub_le source.clock post.clock).trans (Nat.le_of_lt (Nat.lt_of_not_ge enough))

/-- Actual normal empty construction at any clock budget supplies its real
empty table, exact allocated heap and full earlier-memory/FFI frame. -/
theorem empty_normal_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table : Nat) (scratch : BitVec 64) (actual : EmptyReady source table)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word (BitVec.ofNat 64 table)) ∧ Layout32.Built 2 post (Constructor.allocationPlan table table 0 4) scratch 0 [] (fun _=>none) ∧
      post.ffi=source.ffi ∧ post.globals=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+304)))) ∧
      (∀ query,query.toNat<table → post.memory query=source.memory query) ∧
      post.clock≤source.clock ∧ source.clock-post.clock≤42 ∧
      KeccakAbsorb.hashControl post=KeccakAbsorb.hashControl {source with globals:=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+304))))} := by
  have paddedRun := panPropsEvaluateAddClockEq body source (some (.returned value)) post 47 ⟨run,by intro impossible; cases impossible⟩
  have ready := actual.with_clock source table (source.clock+47)
  obtain ⟨target,known,built,ffi,globals,memory,spent,forward,control⟩ := execute_empty_controlled {source with clock:=source.clock+47} table ready.lower ready.aligned ready.room ready.domain ready.little ready.count ready.heap ready.tableCode ready.allocCode ready.zeroCode scratch (Nat.le_add_left _ _)
  have resultEq := congrArg Prod.fst (known.symm.trans paddedRun)
  have answer : value=.val (.word (BitVec.ofNat 64 table)) := by cases resultEq; rfl
  have targetEq : target={post with clock:=post.clock+47} := congrArg Prod.snd (known.symm.trans paddedRun)
  rw [targetEq] at built ffi globals memory spent forward control
  have actualBuilt := Layout32.built_fields {post with clock:=post.clock+47} post (Constructor.allocationPlan table table 0 4) 2 scratch 0 [] (fun _=>none) rfl rfl rfl built
  have actualForward : post.clock≤source.clock := by change post.clock+47≤source.clock+47 at forward; omega
  have actualSpent : source.clock-post.clock≤42 := by change source.clock+47-42≤post.clock+47 at spent; omega
  exact ⟨answer,actualBuilt,ffi,globals,memory,actualForward,actualSpent,control⟩

end InitECandidate.Solver.MutableTable.WitnessBuild
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.EmptyReady.with_clock
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.empty_body_cost
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.empty_normal_any_clock
