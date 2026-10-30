import InitECandidate.Solver.Input.ScratchClear
import InitECandidate.Solver.Input.CurrentDomain
import InitECandidate.Solver.Input.LocalWord
import InitECandidate.Solver.Input.ScalarProgram
import InitECandidate.Solver.Arenas.Cost
import InitECandidate.Solver.Input.ClockCostScopedReached

/- The early-stop results in this module require a cursor at or below
sourceBase. This explicit unmapped-arena premise does not hold at current
main startup; mapped scratch paths need their own execution proofs. -/

namespace InitECandidate.Solver.Input.ScratchStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normally returned scratch allocation followed by an in-range
literal word store fails immediately below the current ordinary domain. -/
theorem after_normal_error {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (pointer limit : BitVec 64)
    (length offset : Nat) (name : String) (constant : BitVec 64) (rest : ProgHOL 64) (returned : ValueHOL 64)
    (small : length < 2^64) (inside : offset < length)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer) (aligned : limit.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit)))
    (amountCell : callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) (Arenas.body .down) = (some (.returned returned), target)) :
    let ready := CallNormal.continuationEntry source target name returned
    evaluateHOLFiniteState ready (.seq (.store (Scalar.plus (localVar name) offset) (.const constant)) rest) = (some .error, ready) := by
  let amount := BitVec.ofNat 64 length
  obtain ⟨room, returnedEq, frame⟩ := Arenas.post_of_normal (callEntryStateHOLFinite source callee) target .down pointer limit amount
    amountCell pointerGlobal limitGlobal ordered aligned (Trap.original_code source.code installed) returned normal
  let q := Arenas.resultWord .down pointer amount
  have guards := Arenas.downward_guards pointer limit amount aligned room
  have amountNat : amount.toNat = length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have fit : q.toNat + length ≤ pointer.toNat := by
    have bound := guards.2.2.2.1
    rw [amountNat] at bound
    exact bound
  have addressNat : (q + BitVec.ofNat 64 offset).toNat = q.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; dsimp [InitE.sourceBase] at pointerBound; omega), offsetNat]
  have below : (q + BitVec.ofNat 64 offset).toNat < InitE.sourceBase := by
    rw [addressNat]
    dsimp [InitE.sourceBase] at pointerBound ⊢
    omega
  let ready := CallNormal.continuationEntry source target name returned
  have readyEq : ready = bind (Arenas.post {source with clock := source.clock - 1} .down pointer amount) name q := by
    have reconstructed := congrArg (fun state : PanSemStateFiniteExact 64 F =>
      setVarHOLFinite (ofString name) returned {state with locals := source.locals}) frame
    have rebuilt : ready = setVarHOLFinite (ofString name) returned
        (Arenas.post {source with clock := source.clock - 1} .down pointer amount) := reconstructed
    rw [rebuilt, returnedEq]
    rfl
  have cell : ready.locals.lookup (ofString name) = some (.val (.word q)) := by
    rw [readyEq]
    exact bind_lookup_same _ _ _
  have readQ : eval ready (localVar name) = some (.val (.word q)) := by
    simpa [eval, localVar, evalHOLExact, toExact] using cell
  have address := Scalar.plus_read ready (localVar name) q offset readQ
  have readyDomain : ready.memaddrs = InitE.ordinaryDomain := by rw [readyEq]; exact domain
  have stopped := CurrentDomain.store_below_base_error ready (Scalar.plus (localVar name) offset) (.const constant)
    (q + BitVec.ofNat 64 offset) constant readyDomain below address rfl
  exact WitnessRadix.StateSteps.stopped_sequence ready ready _ rest .error stopped (Nat.le_refl _)

/-- All actual allocator outcomes and the failed first store cost at most two
source call/loop ticks, even when the unreachable suffix contains loops/calls. -/
theorem allocated_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer limit : BitVec 64)
    (length offset : Nat) (name : String) (constant : BitVec 64) (rest : ProgHOL 64)
    (small : length < 2^64) (inside : offset < length)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer) (aligned : limit.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    source.clock - (evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString "scratch_alloc") [.const (BitVec.ofNat 64 length)]
        (.seq (.store (Scalar.plus (localVar name) offset) (.const constant)) rest))).2.clock ≤ 2 := by
  obtain ⟨callee, called, amountCell⟩ := CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n"
    (Arenas.body .down) (BitVec.ofNat 64 length) (ScratchClear.allocator_installed source.code installed)
  have bodyCost := Arenas.body_price source.code installed .down (callEntryStateHOLFinite source callee) rfl
  apply ClockCost.scoped_reached_current source name .one (ofString "scratch_alloc") [.const (BitVec.ofNat 64 length)]
    [.val (.word (BitVec.ofNat 64 length))] (Arenas.body .down) _ callee .one 1 0 rfl called bodyCost
  intro target returned normal checked
  have stopped := after_normal_error source target callee pointer limit length offset name constant rest returned small inside
    pointerBound ordered aligned domain installed pointerGlobal limitGlobal amountCell normal
  rw [stopped]
  change target.clock - target.clock ≤ 0
  omega

/-- A whole scoped scratch allocation/store cannot return normally. No
successful allocation, room, clock or suffix execution is assumed. -/
theorem allocated_no_return {F : Type} (source post : PanSemStateFiniteExact 64 F) (pointer limit : BitVec 64)
    (length offset : Nat) (name : String) (constant : BitVec 64) (rest : ProgHOL 64) (value : ValueHOL 64)
    (small : length < 2^64) (inside : offset < length)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer) (aligned : limit.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString "scratch_alloc") [.const (BitVec.ofNat 64 length)]
        (.seq (.store (Scalar.plus (localVar name) offset) (.const constant)) rest)) ≠ (some (.returned value), post) := by
  intro normal
  let tail := ProgHOL.seq (.store (Scalar.plus (localVar name) offset) (.const constant)) rest
  have positive := CallNormal.normal_clock source post (ofString name) .one (ofString "scratch_alloc") [.const (BitVec.ofNat 64 length)] tail value normal
  obtain ⟨callee, called, amountCell⟩ := CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n"
    (Arenas.body .down) (BitVec.ofNat 64 length) (ScratchClear.allocator_installed source.code installed)
  obtain ⟨target, returned, actual⟩ := CallNormal.callee_return source post (ofString name) .one (ofString "scratch_alloc")
    [.const (BitVec.ofNat 64 length)] [.val (.word (BitVec.ofNat 64 length))] (Arenas.body .down) tail callee .one rfl called positive value normal
  have stopped := after_normal_error source target callee pointer limit length offset name constant rest returned small inside
    pointerBound ordered aligned domain installed pointerGlobal limitGlobal amountCell actual
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at normal
  simp only [show evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const (BitVec.ofNat 64 length)] =
    some [.val (.word (BitVec.ofNat 64 length))] from rfl, called, if_neg (show source.clock ≠ 0 by omega), actual] at normal
  split at normal
  · change (let out := evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) tail;
      (out.1, restore source name out.2)) = _ at normal
    rw [show evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) tail = _ from stopped] at normal
    cases normal
  · cases normal

end InitECandidate.Solver.Input.ScratchStore

#print axioms InitECandidate.Solver.Input.ScratchStore.after_normal_error
#print axioms InitECandidate.Solver.Input.ScratchStore.allocated_price
#print axioms InitECandidate.Solver.Input.ScratchStore.allocated_no_return
