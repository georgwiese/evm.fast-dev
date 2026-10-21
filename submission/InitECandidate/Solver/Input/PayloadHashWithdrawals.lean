import InitECandidate.Solver.Input.PayloadHashProgram
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.PayloadHash.Withdrawals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure RoundState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat) : Prop where
  workspace : SszHash.Workspace source stp accel chunk zeros
  pointer : source.locals.lookup (ofString "wd")=some (.val (.word p))
  count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 n)))
  rootsLocal : source.locals.lookup (ofString "roots")=some (.val (.word roots))
  position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))

structure Geometry (p roots cursor : BitVec 64) (n : Nat) : Prop where
  countBound : n≤134217728
  inputs : AllocatedBytes.Arena p (44*n)
  rootsArena : AllocatedBytes.Arena roots (32*n)
  rootsAligned : roots.toNat%8=0
  rootsBefore : roots.toNat+32*n≤cursor.toNat
  temporaryArena : AllocatedBytes.Arena cursor 1248
  aligned : cursor.toNat%8=0

theorem RoundState.dec_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (actual : RoundState source p roots cursor stp accel chunk zeros n index) : RoundState (decClockHOLFinite source) p roots cursor stp accel chunk zeros n index :=
  ⟨SszHash.Workspace.of_fields source _ stp accel chunk zeros actual.workspace rfl rfl (by intro key different; rfl),actual.pointer,actual.count,actual.rootsLocal,actual.position,actual.heap⟩

theorem call_geometry (p roots cursor : BitVec 64) (n index : Nat) (geometry : Geometry p roots cursor n) (active : index<n) :
    AllocatedBytes.Arena (p+BitVec.ofNat 64 (44*index)) 44 ∧ AllocatedBytes.Arena (roots+BitVec.ofNat 64 (32*index)) 32 :=
  ⟨AllocatedBytes.Arena.subrange p (44*n) (44*index) 44 geometry.inputs (by omega),
    AllocatedBytes.Arena.subrange roots (32*n) (32*index) 32 geometry.rootsArena (by omega)⟩

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (actual : RoundState source p roots cursor stp accel chunk zeros n index) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) withdrawalArguments=
      some (FixedHash.values (p+BitVec.ofNat 64 (44*index)) (roots+BitVec.ofNat 64 (32*index))) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,withdrawalArguments,localVar,actual.pointer,actual.rootsLocal,actual.position,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm,FixedHash.values]

/-- One actual original withdrawal call costs616source ticks; a genuine
normal return retains the current loop bindings and restores temporary heap. -/
theorem call_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (actual : RoundState source p roots cursor stp accel chunk zeros n index) (geometry : Geometry p roots cursor n) (active : index<n)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_withdrawal") withdrawalArguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤616 ∧ (result=none → RoundState post p roots cursor stp accel chunk zeros n index) := by
  obtain ⟨inputArena,outArena⟩ := call_geometry p roots cursor n index geometry active
  have args := arguments_read source p roots cursor stp accel chunk zeros n index actual
  have cost := FixedHash.call_cost .withdrawal source post (p+BitVec.ofNat 64 (44*index)) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros actual.workspace actual.heap
    inputArena geometry.temporaryArena geometry.aligned outArena (some none) withdrawalArguments args result run notTimeout
  rw [FixedHash.fixed_prices.1] at cost
  refine ⟨cost,?_⟩
  intro normal
  subst result
  have heap := FixedHash.ignored_return_heap .withdrawal source post (p+BitVec.ofNat 64 (44*index)) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros actual.workspace actual.heap
    inputArena geometry.temporaryArena geometry.aligned outArena withdrawalArguments args run
  have workspace := SszHash.Workspace.after source post stp accel chunk zeros actual.workspace _ none run
    (fun key different=>GlobalEffects.call_body key source.code (some none) (ofString "htr_withdrawal") withdrawalArguments FixedHash.Kind.withdrawal.formals FixedHash.Kind.withdrawal.body .one
      (FixedHash.original_code .withdrawal source.code actual.workspace.sha.installed) (FixedHash.globals .withdrawal key source.code actual.workspace.sha.installed different))
  have other (name : String) := CallNormal.ignored_lookup source post (ofString name) (ofString "htr_withdrawal") withdrawalArguments run
  exact ⟨workspace,(other "wd").trans actual.pointer,(other "nwd").trans actual.count,(other "roots").trans actual.rootsLocal,(other "i").trans actual.position,heap⟩

end InitECandidate.Solver.Input.PayloadHash.Withdrawals

#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.RoundState.dec_clock
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.call_geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.arguments_read
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.call_summary
