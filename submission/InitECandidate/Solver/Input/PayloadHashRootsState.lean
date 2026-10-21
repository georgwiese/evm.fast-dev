import InitECandidate.Solver.Input.PayloadHashStatePrefix
import InitECandidate.Solver.Input.PayloadHashListState
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.AllocationTrace

namespace InitECandidate.Solver.Input.PayloadHash.RootsPhase
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def amount (kind : ListPhase.Kind) (data : Description) := BitVec.ofNat 64 (rootsBytes (kind.count data))
def arguments (kind : ListPhase.Kind) := rootsAllocationArguments kind.name
def localCall (kind : ListPhase.Kind) : ProgHOL 64 := .call (some (some (.local,ofString "roots"),none)) (ofString "alloc") (arguments kind)
def next (kind : ListPhase.Kind) (data : Description) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} (chunksCursor ch) (amount kind data)) "roots" (chunksCursor ch)

theorem geometry (kind : ListPhase.Kind) (data : Description) (lower upper budget : Nat) (ch : BitVec 64)
    (layout : data.Layout lower upper budget) (actual : data.RuntimeGeometry budget ch) :
    (chunksCursor ch).toNat+(amount kind data).toNat≤33806089496 ∧
    PersistentAlloc.rounded (chunksCursor ch) (amount kind data)=kind.cursor data ch := by
  obtain ⟨fixed,scratch,number⟩ := data.static_geometry lower upper budget ch layout actual
  have fits : rootsBytes (kind.count data)+max 0 (832+64*kind.count data)≤data.scratchBytes budget := by
    cases kind <;> simp only [ListPhase.Kind.count] <;> unfold rootsBytes Description.scratchBytes <;> omega
  have bounds := roots_geometry (chunksCursor ch) (kind.count data) (data.scratchBytes budget) 0 scratch fixed.aligned fits
  have natural : (amount kind data).toNat=rootsBytes (kind.count data) := by
    rw [amount,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=scratch.upper; omega)]
  exact ⟨by rw [natural]; have h:=scratch.upper; omega,bounds.2.2.2.2.2⟩

theorem arguments_read (kind : ListPhase.Kind) (data : Description) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (count : source.locals.lookup (ofString kind.name)=some (.val (.word (BitVec.ofNat 64 (kind.count data))))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (arguments kind)=some (PersistentAlloc.values (amount kind data)) := by
  simp [evalListHOLFinite,arguments,rootsAllocationArguments,evalHOLExact,evalListHOLExact,toExact,localVar,count,
    valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,PersistentAlloc.values,amount,rootsBytes,BitVec.ofNat_mul,BitVec.ofNat_add,BitVec.mul_comm]

/-- Conservative all-outcome caller cost includes the allocator's failure
trap; normal-state transport is tied to the same actual assigned call. -/
theorem local_cost (kind : ListPhase.Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (localCall kind)=(result,post)) : source.clock-post.clock≤2 := by
  have price := ClockCost.call_body source.code (some (some (ofString "roots"))) (ofString "alloc") (arguments kind)
    PersistentAlloc.formals PersistentAlloc.body .one 1 (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed) source rfl
  change source.clock-(evaluateHOLFiniteState source (localCall kind)).2.clock≤2 at price
  rw [run] at price
  exact price

theorem next_state (kind : ListPhase.Kind) (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (mapped : data.RuntimeGeometry budget ch) :
    StaticFields.State origin (next kind data source ch) lower upper data.payload data.raw ch out (kind.cursor data ch) mark stp accel chunk zeros := by
  have allocated := actual.allocator_post origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros (amount kind data)
  rw [(geometry kind data lower upper budget ch layout mapped).2] at allocated
  exact allocated.bind_current origin _ lower upper data.payload data.raw ch out (kind.cursor data ch) mark stp accel chunk zeros "roots" (chunksCursor ch)
    ⟨by decide,by decide,by decide,by decide,by decide⟩

theorem local_normal (kind : ListPhase.Kind) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros old : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (mapped : data.RuntimeGeometry budget ch)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word old)))
    (count : source.locals.lookup (ofString kind.name)=some (.val (.word (BitVec.ofNat 64 (kind.count data)))))
    (run : evaluateHOLFiniteState source (localCall kind)=(none,post)) : post=next kind data source ch := by
  have room := (geometry kind data lower upper budget ch layout mapped).1
  exact (PersistentAlloc.local_call_normal source post "roots" old (chunksCursor ch) (amount kind data) roots (arguments kind)
    (arguments_read kind data source count) (PersistentAlloc.original_code source.code actual.ready.workspace.sha.installed)
    (Trap.original_code source.code actual.ready.workspace.sha.installed) actual.ready.heap (by omega) run).2.2

end InitECandidate.Solver.Input.PayloadHash.RootsPhase
#print axioms InitECandidate.Solver.Input.PayloadHash.RootsPhase.geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.RootsPhase.arguments_read
#print axioms InitECandidate.Solver.Input.PayloadHash.RootsPhase.local_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.RootsPhase.next_state
#print axioms InitECandidate.Solver.Input.PayloadHash.RootsPhase.local_normal
