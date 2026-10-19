import InitECandidate.Solver.Mpt.StorageKeyMemory
import InitECandidate.Solver.Mpt.StorageKeyEnvironment
import InitECandidate.Solver.Input.ScopedCallSuccess

namespace InitECandidate.Solver.Mpt.StorageKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

theorem scoped_registered {ι : Type}
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32)
    (scratchArena : AllocatedBytes.Arena scratch 52) (installed : Input.OriginalCode.Installed source.code)
    (cutoff cursor : Nat) (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff) (small : cutoff < 2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) expressions =
      some [.val (.word address),.val (.word key)])
    (result : Option (PanSemResultExact 64))
    (success : result = none ∨ ∃ value, result = some (.returned value))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "sk_make") expressions continuation) = (result,post)) :
    price address key scratch + 1 ≤ source.clock ∧ price address key scratch + 1 ≤ 13 ∧ ∃ ready inner,
      ready.locals.lookup (ofString name) = some (.val (.word scratch)) ∧
      ready.locals = source.locals.update (ofString name,.val (.word scratch)) ∧
      ready.clock = source.clock - (price address key scratch + 1) ∧
      ready.globals = source.globals ∧ ready.code = source.code ∧ ready.memaddrs = source.memaddrs ∧ ready.be = source.be ∧
      TableFamily.Model ready cursor objects ∧ TableFamily.ValuesHave ready objects property ∧
      AccountDecode.Registry ready cutoff cursor objects accounts ∧
      TableFamily.PersistentFrame cutoff cursor objects objects source ready ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → ready.memory query = source.memory query) ∧
      evaluateHOLFiniteState ready continuation = (result,inner) ∧ post = restore source name inner := by
  obtain ⟨callee,called,addressLocal,keyLocal⟩ := environment source.code.lookup address key (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,scope⟩ := Input.CallNormal.scoped_success source post name .one
    (ofString "sk_make") expressions _ body continuation callee .one args called result success normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryRegistry := registry.framed source entry cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source entry rfl) (Nat.le_refl _) rfl
  obtain ⟨funded,answerEq,clock,models,tableValues,nextRegistry,frame,words,postEq⟩ := body_registered entry target address key scratch
    addressLocal keyLocal scratchGlobal domain addressArena keyArena scratchArena installed cutoff cursor objects accounts
    entryFamily entryRegistry property values floors scratchBelow small answer bodyRun
  rw [answerEq] at tailRun
  let ready := Input.CallNormal.continuationEntry source target name (.val (.word scratch))
  have readyFamily : TableFamily.Model ready cursor objects := models.of_control rfl rfl rfl rfl
  have readyRegistry := nextRegistry.framed target ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects target ready rfl) (Nat.le_refl _) rfl
  have readyClock : ready.clock = source.clock - (price address key scratch + 1) := by
    change target.clock = _
    change target.clock = source.clock - 1 - price address key scratch at clock
    omega
  have readyGlobals : ready.globals = source.globals := by change target.globals = _; rw [postEq]; rfl
  have readyCode : ready.code = source.code := by change target.code = _; rw [postEq]; rfl
  have readyDomain : ready.memaddrs = source.memaddrs := by change target.memaddrs = _; rw [postEq]; rfl
  have readyEndian : ready.be = source.be := by change target.be = _; rw [postEq]; rfl
  change price address key scratch ≤ source.clock - 1 at funded
  have bound := price_bound address key scratch
  exact ⟨by omega,by omega,ready,inner,Input.CallNormal.continuation_lookup_same source target name (.val (.word scratch)),rfl,
    readyClock,readyGlobals,readyCode,readyDomain,readyEndian,readyFamily,tableValues,readyRegistry,⟨frame.words⟩,words,tailRun,scope⟩

end InitECandidate.Solver.Mpt.StorageKey

#print axioms InitECandidate.Solver.Mpt.StorageKey.scoped_registered
