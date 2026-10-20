import InitECandidate.Solver.Input.MainBnAccelStages

namespace InitECandidate.Solver.Input.Main.BnAccelInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

private theorem aliases_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List InitializerAliases.Action) :
    (InitializerAliases.template source pointer actions).memory = source.memory := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih => exact ih (InitializerAliases.reserve source pointer action)

private theorem allocations_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List InitializerAllocations.Action) :
    (InitializerAllocations.template source cursor actions).memory = source.memory := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih => exact ih (InitializerAllocations.reserve source action cursor) (cursor + action.bytes)

theorem template_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (template source cursor).memory = (seeded source cursor).memory := by
  unfold template
  rw [aliases_memory,allocations_memory]
  unfold fp2
  rw [aliases_memory,allocations_memory]

/-- The actual scalar arithmetic buffer bindings survive both later allocations. -/
theorem template_params_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : ParamsGlobals (template source cursor) cursor := by
  constructor
  all_goals
    simp only [template,fp2,seeded,params,InitializerAliases.template_globals,InitializerAllocations.template_globals,InitializerQuads.written_globals]
    simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,paramsAliases,fp2Aliases,g1Aliases,paramsAction,fp2Action,g1Action,
      InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString,BitVec.ofNat_add,BitVec.add_assoc]

theorem seeded_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (index : Fin 4) :
    (seeded source cursor).memory (BitVec.ofNat 64 (cursor + 64) + BitVec.ofNat 64 (8 * index.val)) = .word 0#64 := by
  obtain ⟨index,inside⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [seeded,InitializerQuads.written,InitializerQuads.writes,RlpWrite.U256Value.wordWrites,
      WordWrites.write,StoreWord.put,zeros,modulus,BitVec.ofNat_add,BitVec.add_assoc]

theorem seeded_modulus (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (index : Fin 4) :
    (seeded source cursor).memory (BitVec.ofNat 64 (cursor + 96) + BitVec.ofNat 64 (8 * index.val)) = .word (modulus index) := by
  obtain ⟨index,inside⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [seeded,InitializerQuads.written,InitializerQuads.writes,RlpWrite.U256Value.wordWrites,
      WordWrites.write,StoreWord.put,zeros,modulus,BitVec.ofNat_add,BitVec.add_assoc]

theorem template_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (index : Fin 4) :
    (template source cursor).memory (BitVec.ofNat 64 (cursor + 64) + BitVec.ofNat 64 (8 * index.val)) = .word 0#64 := by
  rw [template_memory]
  exact seeded_zero source cursor index

theorem template_modulus (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (index : Fin 4) :
    (template source cursor).memory (BitVec.ofNat 64 (cursor + 96) + BitVec.ofNat 64 (8 * index.val)) = .word (modulus index) := by
  rw [template_memory]
  exact seeded_modulus source cursor index

theorem arenas (cursor : Nat) (lower : 2701131776 ≤ cursor) (room : cursor + 416 ≤ 33806089496) (aligned : cursor % 8 = 0) :
    AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 160 ∧ (BitVec.ofNat 64 cursor).toNat % 8 = 0 ∧
    AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 160)) 128 ∧ (BitVec.ofNat 64 (cursor + 160)).toNat % 8 = 0 ∧
    AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 288)) 128 ∧ (BitVec.ofNat 64 (cursor + 288)).toNat % 8 = 0 := by
  have number (offset : Nat) (inside : offset ≤ 416) : (BitVec.ofNat 64 (cursor + offset)).toNat = cursor + offset := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have baseNumber : (BitVec.ofNat 64 cursor).toNat = cursor := by simpa using number 0 (by decide)
  exact ⟨⟨by rw [baseNumber]; exact lower,by rw [baseNumber]; omega⟩,by rw [baseNumber]; exact aligned,
    ⟨by rw [number 160 (by decide)]; omega,by rw [number 160 (by decide)]; omega⟩,by rw [number 160 (by decide)]; omega,
    ⟨by rw [number 288 (by decide)]; omega,by rw [number 288 (by decide)]; omega⟩,by rw [number 288 (by decide)]; omega⟩

end InitECandidate.Solver.Input.Main.BnAccelInitialization

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_memory
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_params_bindings
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.seeded_zero
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.seeded_modulus
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_zero
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_modulus
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.arenas
