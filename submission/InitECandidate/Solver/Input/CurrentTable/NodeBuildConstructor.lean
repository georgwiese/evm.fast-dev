import InitECandidate.Solver.Input.CurrentTable.NodeBuildCapacity
import InitECandidate.Solver.Input.CurrentTable.NewCall
import InitECandidate.Solver.Input.CurrentTable.Workspace

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def tableArguments : List (ExpHOL 64) := [.const 32#64,localVar "cap"]
def tableTail : ProgHOL 64 := match allocatedTail with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem table_shape : allocatedTail=.decCall (ofString "t") .one (ofString "htab_new") tableArguments tableTail := by
  simp only [allocatedTail,afterCap,body,tableTail,tableArguments,Guest.Software.guestFn_nodedb_build,progToHOL,expToHOL,
    shapeToHOL,List.map_cons,List.map_nil,localVar]

/-- The same real initialized Patricia table and original insertion-loop
continuation reached by this database invocation. -/
def ReachesTable (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count lower : Nat) (stp pad : BitVec 64)
    (outcome : Option (PanSemResultExact 64)) : Prop :=
∃ selected target inner heap bits,
      2≤bits ∧ bits≤21 ∧ 2*count+2≤2^bits ∧ 2^bits≤4*count+4 ∧ count≤1048575 ∧
      New.Returned selected target heap (BitVec.ofNat 64 (2^bits)) stp pad ∧
      Workspace (CallNormal.continuationEntry selected target "t" (.val (.word heap))) lower stp pad ∧
      LocalEffects.erase selected=LocalEffects.erase source ∧
      (∀ query : BitVec 64,query.toNat<lower→
        (CallNormal.continuationEntry selected target "t" (.val (.word heap))).memory query=source.memory query) ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤36 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry selected target "t" (.val (.word heap))) tableTail=(outcome,inner) ∧
      post=restore source "cap" (restore selected "t" inner)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The real builder's capacity loop and current Patricia constructor cost
at most36source ticks before its actual insertion-loop continuation. Every
reached table has its real physical empty header/arrays and protects earlier
input; no independent successful constructor execution is substituted. -/
theorem constructor_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count lower : Nat) (stp pad : BitVec 64)
    (workspace : Workspace source lower stp pad) (small : count<2^31)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤36 ∨ ReachesTable source post count lower stp pad outcome := by
  rcases capacity_trace source post count small countLocal outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨selected,middle,paid,bits,budget,bitsLower,bitsUpper,sufficient,capBound,capLocal,clock,same,others,continued,endpoint⟩:=reached
    have ready:=workspace.of_frame same
    obtain ⟨heap,heapCell,heapLower,heapBound,heapAligned⟩:=ready.heap
    have number : (BitVec.ofNat 64 (2^bits)).toNat=2^bits := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
    have capLow : 2≤(BitVec.ofNat 64 (2^bits)).toNat := by
      rw [number]
      have bound:=Nat.pow_le_pow_right (by decide : 0<2) bitsLower
      change 4≤2^bits at bound
      omega
    have capSmall : (BitVec.ofNat 64 (2^bits)).toNat≤2^32 := by
      rw [number]
      exact Nat.pow_le_pow_right (by decide) bitsUpper
    have context : New.Context selected heap (BitVec.ofNat 64 (2^bits)) stp pad :=
      ⟨ready.arena,ready.environment,heapCell,by have h:=ready.lowerDomain; omega,heapBound,heapAligned,capLow,capSmall⟩
    have args : evalListHOLFinite selected (h:=fun query=>Classical.propDecidable (selected.memaddrs query)) tableArguments=
        some [.val (.word 32#64),.val (.word (BitVec.ofNat 64 (2^bits)))] := by
      simp [tableArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,capLocal]
    rw [table_shape] at continued
    rcases New.scoped_trace selected middle heap (BitVec.ofNat 64 (2^bits)) stp pad context "t" tableArguments tableTail args outcome continued with stopped|allocated
    · have postClock : post.clock=middle.clock := by rw [endpoint]; rfl
      exact Or.inl (by have price:=stopped.1; rw [postClock]; omega)
    · obtain ⟨target,inner,returned,forward,cost,rest,restored⟩:=allocated
      obtain ⟨powerBound,countBound⟩:=New.power_capacity heap (BitVec.ofNat 64 (2^bits)) returned.geometry bits count bitsUpper rfl sufficient
      have next:=returned.workspace heapLower ready.lowerDomain
      have finalWorkspace : Workspace (CallNormal.continuationEntry selected target "t" (.val (.word heap))) lower stp pad := next.of_frame rfl
      have memory:=LocalEffects.memory_of_erase source selected same
      have earlier (query : BitVec 64) (before : query.toNat<lower) :
          (CallNormal.continuationEntry selected target "t" (.val (.word heap))).memory query=source.memory query :=
        (returned.earlier query (by omega)).trans (congrFun memory query)
      exact Or.inr ⟨selected,target,inner,heap,bits,bitsLower,powerBound,sufficient,capBound,countBound,returned,finalWorkspace,same,earlier,
        by omega,by omega,rest,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.table_shape
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.constructor_trace
