import InitECandidate.Solver.Mpt.StorageKeyExecution
import InitECandidate.Solver.ClockPaddingFull

namespace InitECandidate.Solver.Mpt.StorageKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem result_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64) :
    (resultState source address key scratch).clock = source.clock - price address key scratch := by
  simp [resultState,CopyGeneral.callState,price,Nat.sub_sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega

theorem result_padding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64) (extra : Nat) :
    resultState {source with clock := source.clock + extra} address key scratch =
      {resultState source address key scratch with clock := source.clock + extra - price address key scratch} := by
  simp [resultState,CopyGeneral.callState,price,Nat.sub_sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32)
    (scratchArena : AllocatedBytes.Arena scratch 52) (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 12 := by
  have bound := price_bound address key scratch
  by_cases enough : price address key scratch ≤ source.clock
  · rw [execute source address key scratch addressLocal keyLocal scratchGlobal domain addressArena keyArena scratchArena installed enough]
    change source.clock - (resultState source address key scratch).clock ≤ 12
    rw [result_clock]
    omega
  · omega

theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32)
    (scratchArena : AllocatedBytes.Arena scratch 52) (installed : Input.OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    price address key scratch ≤ source.clock ∧ returned = .val (.word scratch) ∧
      post = emptyLocalsHOLFinite (resultState source address key scratch) := by
  let extra := price address key scratch
  let padded := {source with clock := source.clock + extra}
  let model := emptyLocalsHOLFinite (resultState source address key scratch)
  have actual := execute padded address key scratch addressLocal keyLocal scratchGlobal domain addressArena keyArena scratchArena installed
    (by change extra ≤ source.clock + extra; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned returned)) post extra
    ⟨normal,by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans actual)
  have postEq := congrArg Prod.snd (lifted.symm.trans actual)
  change {post with clock := post.clock + extra} = emptyLocalsHOLFinite (resultState padded address key scratch) at postEq
  have frame : {post with clock := post.clock + extra} = {model with clock := source.clock + extra - price address key scratch} := by
    rw [postEq]
    dsimp only [padded]
    rw [result_padding]
    rfl
  obtain ⟨funded,next⟩ := InitECandidate.Solver.strip_full_clock_padding source post model (price address key scratch) extra (by omega) frame
  have clock : model.clock = source.clock - price address key scratch := result_clock source address key scratch
  rw [← clock] at next
  exact ⟨funded,by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq,next⟩

end InitECandidate.Solver.Mpt.StorageKey

#print axioms InitECandidate.Solver.Mpt.StorageKey.result_clock
#print axioms InitECandidate.Solver.Mpt.StorageKey.result_padding
#print axioms InitECandidate.Solver.Mpt.StorageKey.body_cost
#print axioms InitECandidate.Solver.Mpt.StorageKey.body_normal
