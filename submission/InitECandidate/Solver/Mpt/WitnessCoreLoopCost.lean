import InitECandidate.Solver.Mpt.WitnessCoreLoopStep
import InitECandidate.Solver.Input.CoreDecodeCost
import InitECandidate.Solver.Input.CoreResolveCost
import InitECandidate.Solver.Mpt.WitnessCoreReturnModeCost

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors
open Input.Main

def iterationCost (input : Guest.InputBlob) : Nat:=max 257454 (61492+6*WitnessConstructors.nodeCount input)

theorem record_bytes_le (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db : BitVec 64)
    (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data) : data.bytes≤1024 := by
  have small:=view.parentBound
  have first:=view.payloadLower
  have last:=view.payloadUpper
  omega

/-- Uniform price for every outcome of one actual original238 body.
Real source ticks are bounded even when a helper fails, traps or times
out; the full invariant supplies current parser/table and physical bounds. -/
theorem Invariant.body_cost (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (invariant : Invariant input frontier db limit source configuration) :
    source.clock-(evaluateHOLFiniteState source loopBody).2.clock≤iterationCost input := by
  rcases configuration with ⟨heap,cursor,stack,phase,running⟩
  rw [loop_body_choice source (modeWord phase) invariant.modeCell]
  cases phase with
  | decode=>
    simp only [modeWord,if_pos rfl]
    obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=invariant.phase
    have paid:=core_decode_cost input source db pointer length cursor limit (invariant.boundary input frontier db limit source _)
      invariant.dbCell pointerCell lengthCell invariant.scratch before small lower invariant.below invariant.installed
    have quarter : length.toNat/4≤256:=by omega
    exact paid.trans ((by omega : 251*length.toNat+length.toNat/4+174≤257454).trans (Nat.le_max_left _ _))
  | resolve=>
    simp only [modeWord,show (2#64 : BitVec 64)≠1#64 from by decide,↓reduceIte]
    obtain ⟨entry,rest,stackEq,waiting,slotCell⟩:=invariant.phase
    change stack=entry::rest at stackEq
    subst stack
    have head:=invariant.view.records entry List.mem_cons_self
    have small:=record_bytes_le source entry.record db entry.data head
    have paid:=core_resolve_cost input source entry.record db cursor limit entry.data head (invariant.boundary input frontier db limit source _)
      invariant.dbCell invariant.topCell slotCell invariant.scratch invariant.below invariant.installed
    exact paid.trans ((by omega : 60*entry.data.bytes+6*WitnessConstructors.nodeCount input+52≤61492+6*WitnessConstructors.nodeCount input).trans
      (Nat.le_max_right _ _))
  | returning=>
    simp only [modeWord,show (0#64 : BitVec 64)≠1#64 from by decide,show (0#64 : BitVec 64)≠2#64 from by decide,↓reduceIte]
    obtain ⟨waiting,child,resultCell,owned⟩:=invariant.phase
    cases stack with
    | nil=>
      rw [return_choice source 0#64 invariant.topCell,if_pos rfl,finish_return_execute source (goWord running) invariant.goCell]
      change source.clock-source.clock≤iterationCost input
      omega
    | cons entry rest=>
      have owned:=owned.weaken source child (max frontier (resultLower (entry::rest))) heap.toNat entry.mark heap.toNat (Nat.le_max_right _ _) (Nat.le_refl _)
      have head:=invariant.view.records entry List.mem_cons_self
      obtain ⟨hash,pendingEq⟩:=waiting entry List.mem_cons_self
      have pending:=invariant.view.pending entry List.mem_cons_self
      simp only [Pending,pendingEq] at pending
      have counts (node : BitVec 64) (index : Fin 16) (occupied : Fin 17) (payload : entry.data.payload=.branch node index occupied) : occupied.val≤index.val:=by
        simpa only [CounterBound,payload] using invariant.view.counters entry List.mem_cons_self
      have separated (notHash : hash≠0#64) (notChild : child≠0#64) : 2713731432≤child.toNat ∧ entry.data.BeforeHeap child.toNat:=by
        rcases owned with zero|allocated
        · exact False.elim (notChild zero)
        · have before:=invariant.view.before entry List.mem_cons_self
          have arrayBefore:=before.1
          change entry.data.array.toNat+16*entry.data.items.length≤entry.mark at arrayBefore
          have arrayFloor:=head.arrayFloor
          have fresh:=allocated.fresh
          change entry.mark≤child.toNat at fresh
          exact ⟨by omega,before.mono entry.data entry.mark child.toNat fresh⟩
      have paid:=return_mode_cost source entry.record db child hash cursor limit entry.data head counts invariant.topCell resultCell pending.1
        (owned.cache_geometry source child entry.mark heap.toNat) separated invariant.scratch invariant.installed
      have small:=record_bytes_le source entry.record db entry.data head
      exact paid.trans ((by omega : 60*entry.data.bytes+43≤257454).trans (Nat.le_max_left _ _))

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.record_bytes_le
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.body_cost
