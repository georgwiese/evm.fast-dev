import InitECandidate.Solver.Input.MainBnAccelStages
import InitECandidate.Solver.Input.InitializerAllocationAliases

namespace InitECandidate.Solver.Input.Main.BnAccelInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def tailBlocks : List InitializerAllocationAliases.Block := [⟨fp2Action,fp2Aliases⟩,⟨g1Action,g1Aliases⟩]

theorem tail_blocks_length : tailBlocks.length = 2 := rfl

theorem tail_blocks_valid : ∀ block,block ∈ tailBlocks → InitializerAllocationAliases.Valid block := by
  intro block member
  simp only [tailBlocks,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · refine ⟨fp2_valid,fp2_aliases_valid,?_⟩
    intro action member
    simp only [fp2Aliases,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · refine ⟨g1_valid,g1_aliases_valid,?_⟩
    intro action member
    simp only [g1Aliases,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide

theorem after_modulus_shape : afterModulus = InitializerAllocationAliases.withTail tailBlocks (.return (.const 0#64)) := by
  simp only [afterModulus,afterFp2Allocation,afterFp2Aliases,afterG1Allocation,InitializerAllocationAliases.withTail,tailBlocks]

theorem tail_template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocationAliases.template (seeded source cursor) (cursor + 160) tailBlocks = template source cursor := by
  simp only [tailBlocks,InitializerAllocationAliases.template,InitializerAllocationAliases.step,template,fp2,fp2Action,InitializerAllocations.constant,Nat.add_assoc]

/-- Both remaining real allocation/alias blocks, composed while their entry
state is symbolic. The enclosing initializer supplies that actual entry. -/
theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 160)))))
    (room : cursor + 416 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source afterModulus = (some (.returned (.val (.word 0#64))),
      emptyLocalsHOLFinite {InitializerAllocationAliases.template source (cursor + 160) tailBlocks with clock := source.clock - 2}) := by
  have actual := InitializerAllocationAliases.execute_prefix source (cursor + 160) tailBlocks (.return (.const 0#64)) installed scalars heap tail_blocks_valid
    (by change cursor + 160 + (128 + (128 + 0)) ≤ 33806089496; omega) (by omega) enough
  rw [tail_blocks_length] at actual
  rw [after_modulus_shape,actual]
  exact BuildEntry.zero_return _

end InitECandidate.Solver.Input.Main.BnAccelInitialization

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.tail_blocks_valid
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.tail_blocks_length
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.after_modulus_shape
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.tail_template
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.tail_execute
