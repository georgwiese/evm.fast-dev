import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.RlpWrite.U256Store
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input.Main.SecpBlock
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
abbrev Words := RlpWrite.U256Value.Words

def body : ProgHOL 64 := match Guest.guestFn_secp_accel_init_block with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "base",.one),(ofString "modulus",RlpWrite.U256Value.tupleShape)]
def zeros : Words := fun _ => 0#64
def zeroStore : ProgHOL 64 := .store (.op .add [.var .local (ofString "base"),.const 64#64]) (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
def modulusStore : ProgHOL 64 := .store (.op .add [.var .local (ofString "base"),.const 96#64]) (.var .local (ofString "modulus"))
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Words) :=
  {source with
    memory := WordWrites.write
      (WordWrites.write source.memory (RlpWrite.U256Value.wordWrites (pointer + 64#64) zeros))
      (RlpWrite.U256Value.wordWrites (pointer + 96#64) words)}

theorem body_shape : body = .seq zeroStore (.seq modulusStore (.return (.const 0#64))) := by
  simp only [body,zeroStore,modulusStore,Guest.guestFn_secp_accel_init_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "secp_accel_init_block") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 134 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_secp_accel_init_block) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,RlpWrite.U256Value.tupleShape,Guest.guestFn_secp_accel_init_block,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

private theorem quad_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 128)
    (aligned : pointer.toNat % 8 = 0) (offsetAligned : offset % 8 = 0) (inside : offset + 32 ≤ 128) :
    ∀ index : Fin 4,source.memaddrs (pointer + BitVec.ofNat 64 offset + BitVec.ofNat 64 (8 * index.val)) := by
  intro index
  have mapped := AllocatedBytes.word_mapped source pointer 128 (offset + 8 * index.val) domain arena (by omega) aligned (by omega)
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using mapped

/-- Both actual four-word stores execute in the allocated block. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Words)
    (base : source.locals.lookup (ofString "base") = some (.val (.word pointer)))
    (modulus : source.locals.lookup (ofString "modulus") = some (RlpWrite.U256Value.tuple words))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 128) (aligned : pointer.toNat % 8 = 0) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (template source pointer words)) := by
  have zeroDestination : eval source (.op .add [.var .local (ofString "base"),.const 64#64]) = some (.val (.word (pointer + 64#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,base,valueIsWord,valueWord,wordOpHOL,wordOp]
  have firstRun := RlpWrite.U256Value.store_execute source _ (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64]) (pointer + 64#64) zeros zeroDestination rfl
    (quad_mapped source pointer 64 domain arena aligned (by decide) (by decide))
  let middle := {source with memory := WordWrites.write source.memory (RlpWrite.U256Value.wordWrites (pointer + 64#64) zeros)}
  have modulusDestination : eval middle (.op .add [.var .local (ofString "base"),.const 96#64]) = some (.val (.word (pointer + 96#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,base,valueIsWord,valueWord,wordOpHOL,wordOp,middle]
  have modulusRead : eval middle (.var .local (ofString "modulus")) = some (RlpWrite.U256Value.tuple words) := modulus
  have secondRun := RlpWrite.U256Value.store_execute middle _ _ (pointer + 96#64) words modulusDestination modulusRead
    (quad_mapped middle pointer 96 domain arena aligned (by decide) (by decide))
  rw [body_shape,StateSteps.next_sequence source middle zeroStore _ firstRun (Nat.le_refl _),
    StateSteps.next_sequence middle (template source pointer words) modulusStore _ secondRun (Nat.le_refl _)]
  exact BuildEntry.zero_return (template source pointer words)

def values (pointer : BitVec 64) (words : Words) : List (ValueHOL 64) := [.val (.word pointer),RlpWrite.U256Value.tuple words]
def rawLocals (pointer : BitVec 64) (words : Words) (key : MlS) : Option (ValueHOL 64) :=
  if key = ofString "modulus" then some (RlpWrite.U256Value.tuple words) else if key = ofString "base" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (pointer : BitVec 64) (words : Words)
    (code : codeFn (ofString "secp_accel_init_block") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "secp_accel_init_block") (values pointer words) = some (body,callee,.one) ∧
      callee.lookup (ofString "base") = some (.val (.word pointer)) ∧ callee.lookup (ofString "modulus") = some (RlpWrite.U256Value.tuple words) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values pointer words).length ∧
      ((formals.zip (values pointer words)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,values,RlpWrite.U256Value.tupleShape,RlpWrite.U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true] <;> decide
  have raw : lookupCodeHOLExact codeFn (ofString "secp_accel_init_block") (values pointer words) = some (body,rawLocals pointer words,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,ofString]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (pointer : BitVec 64) (words : Words)
    (argumentsRead : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (values pointer words))
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs = InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena pointer 128) (aligned : pointer.toNat % 8 = 0) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "secp_accel_init_block") arguments) = (none,{template source pointer words with clock := source.clock - 1}) := by
  obtain ⟨callee,called,base,modulus⟩ := environment source.code.lookup pointer words (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry pointer words base modulus domain arena aligned
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "secp_accel_init_block") arguments (values pointer words) body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite (template entry pointer words)) argumentsRead called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  exact actual

end InitECandidate.Solver.Input.Main.SecpBlock

#print axioms InitECandidate.Solver.Input.Main.SecpBlock.body_shape
#print axioms InitECandidate.Solver.Input.Main.SecpBlock.original_code
#print axioms InitECandidate.Solver.Input.Main.SecpBlock.execute
#print axioms InitECandidate.Solver.Input.Main.SecpBlock.environment
#print axioms InitECandidate.Solver.Input.Main.SecpBlock.call_execute
