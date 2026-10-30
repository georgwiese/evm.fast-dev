import InitECandidate.Solver.Input.ScratchClear
import InitECandidate.Solver.Input.ZeroUnmappedCost
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Arenas.Cost

/- The early-stop results in this module require a cursor at or below
sourceBase. This explicit unmapped-arena premise does not hold at current
main startup; mapped scratch paths need their own execution proofs. -/

namespace InitECandidate.Solver.Input.ScratchClear
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Price the real clear only at each actual returned allocation. It cannot
fall through to the supplied suffix, whose cost is consequently irrelevant. -/
theorem returned_clear_price (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (pointer limit : BitVec 64)
    (length : Nat) (name : String) (rest : ProgHOL 64) (returned : ValueHOL 64)
    (small : length + 32 < 2^64) (large : 32 ≤ length)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer) (aligned : limit.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit)))
    (amountCell : callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) (Arenas.body .down) = (some (.returned returned), target)) :
    let ready := CallNormal.continuationEntry source target name returned
    target.clock - (evaluateHOLFiniteState ready
      (.seq (.call (some (none, none)) (ofString "memzero") [localVar name, .const (BitVec.ofNat 64 length)]) rest)).2.clock ≤ 2 := by
  let amount := BitVec.ofNat 64 length
  obtain ⟨room, returnedEq, frame⟩ := Arenas.post_of_normal (callEntryStateHOLFinite source callee) target .down pointer limit amount
    amountCell pointerGlobal limitGlobal ordered aligned (Trap.original_code source.code installed) returned normal
  let q := Arenas.resultWord .down pointer amount
  have guards := Arenas.downward_guards pointer limit amount aligned room
  have qAligned : q.toNat % 8 = 0 := guards.2.2.2.2.2
  have qBelow : q.toNat < InitE.sourceBase := by
    have earlier := guards.2.2.2.1
    have amountNat : amount.toNat = length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : length < 2^64)]
    rw [amountNat] at earlier
    dsimp [InitE.sourceBase] at pointerBound ⊢
    change (Arenas.rounded .down pointer amount).toNat < 2701131776
    omega
  let ready := CallNormal.continuationEntry source target name returned
  have readyEq : ready = bind (Arenas.post {source with clock := source.clock - 1} .down pointer amount) name q := by
    have reconstructed := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      setVarHOLFinite (ofString name) returned {state with locals := source.locals}) frame
    have rebuilt : ready = setVarHOLFinite (ofString name) returned
        (Arenas.post {source with clock := source.clock - 1} .down pointer amount) := reconstructed
    rw [rebuilt, returnedEq]
    rfl
  have cell : ready.locals.lookup (ofString name) = some (.val (.word q)) := by
    rw [readyEq]
    exact bind_lookup_same _ _ _
  have readyDomain : ready.memaddrs = InitE.ordinaryDomain := by rw [readyEq]; exact domain
  have readyCode : OriginalCode.Installed ready.code := by rw [readyEq]; exact installed
  have args : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address))
      [localVar name, .const amount] = some (WitnessRadix.Zero.values q length) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, cell, WitnessRadix.Zero.values, amount]
  have priced := ZeroUnmapped.call_price ready (some none) [localVar name, .const amount] q length
    small large qAligned readyDomain qBelow readyCode args
  have result := ClockCost.sequence_reached_current ready
    (.call (some (none, none)) (ofString "memzero") [localVar name, .const amount]) rest 2 0 priced (by
      intro middle actual
      exact False.elim (ZeroUnmapped.call_not_normal ready middle [localVar name, .const amount] q length
        small large qAligned readyDomain qBelow readyCode args actual))
  exact result

/-- All outcomes of the actual scoped scratch allocation/clear, with any
later continuation, spend at most four source call/loop ticks. -/
theorem allocated_clear_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer limit : BitVec 64)
    (length : Nat) (name : String) (rest : ProgHOL 64)
    (small : length + 32 < 2^64) (large : 32 ≤ length)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer) (aligned : limit.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    source.clock - (evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString "scratch_alloc") [.const (BitVec.ofNat 64 length)]
        (.seq (.call (some (none, none)) (ofString "memzero") [localVar name, .const (BitVec.ofNat 64 length)]) rest))).2.clock ≤ 4 := by
  obtain ⟨callee, called, amountCell⟩ := CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n"
    (Arenas.body .down) (BitVec.ofNat 64 length) (allocator_installed source.code installed)
  have bodyCost := Arenas.body_price source.code installed .down (callEntryStateHOLFinite source callee) rfl
  apply ClockCost.scoped_reached_current source name .one (ofString "scratch_alloc") [.const (BitVec.ofNat 64 length)]
    [.val (.word (BitVec.ofNat 64 length))] (Arenas.body .down) _ callee .one 1 2 rfl called bodyCost
  intro target returned normal checked
  exact returned_clear_price source target callee pointer limit length name rest returned small large
    pointerBound ordered aligned domain installed pointerGlobal limitGlobal amountCell normal

end InitECandidate.Solver.Input.ScratchClear

#print axioms InitECandidate.Solver.Input.ScratchClear.returned_clear_price
#print axioms InitECandidate.Solver.Input.ScratchClear.allocated_clear_price
