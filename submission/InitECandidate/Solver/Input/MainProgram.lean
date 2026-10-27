import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.WitnessRadix.StateSteps
import InitECandidate.Solver.PanDeclarations
import InitECandidate.Solver.Input.GlobalAssign

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.Software.guestFn_main with | .function fn => progToHOL fn.body | _ => .skip
def memoryBody : ProgHOL 64 := match Guest.Software.guestFn_mem_init with | .function fn => progToHOL fn.body | _ => .skip
def afterMemory : ProgHOL 64 := match body with | .seq _ rest => rest | _ => .skip

theorem body_shape : body = .seq (.call (some (none,none)) (ofString "mem_init") []) afterMemory := by
  simp only [body,afterMemory,Guest.Software.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "main") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 812 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_main) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.Software.guestFn_main,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem memory_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "mem_init") = some ([],memoryBody,.one) := by
  have checked := OriginalCode.indexed code installed 1 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_mem_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,memoryBody,Guest.Software.guestFn_mem_init,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def memoryReady (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word 2688618496#64))
    (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word 2701127680#64))
      (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word source.baseAddr)) source))

theorem memory_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap scratch frame : BitVec 64)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))) :
    evaluateHOLFiniteState source memoryBody = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (memoryReady source)) := by
  have first := global_assign_execute source "heap_ptr" heap source.baseAddr .baseAddr heapGlobal rfl
  let middle := putGlobal source "heap_ptr" source.baseAddr
  have second := global_assign_execute middle "scratch_ptr" scratch 2701127680#64 (.const 2701127680#64)
    ((putGlobal.lookup_other source "heap_ptr" source.baseAddr (ofString "scratch_ptr") (by decide)).trans scratchGlobal) rfl
  let later := putGlobal middle "scratch_ptr" 2701127680#64
  have third := global_assign_execute later "frame_mem_ptr" frame 2688618496#64 (.const 2688618496#64)
    ((putGlobal.lookup_other middle "scratch_ptr" 2701127680#64 (ofString "frame_mem_ptr") (by decide)).trans
      ((putGlobal.lookup_other source "heap_ptr" source.baseAddr (ofString "frame_mem_ptr") (by decide)).trans frameGlobal)) rfl
  simp only [memoryBody,Guest.Software.guestFn_mem_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  change evaluateHOLFiniteState source (.seq (.assign .global (ofString "heap_ptr") .baseAddr)
    (.seq (.assign .global (ofString "scratch_ptr") (.const 2701127680#64))
      (.seq (.assign .global (ofString "frame_mem_ptr") (.const 2688618496#64)) (.return (.const 0#64))))) = _
  rw [WitnessRadix.StateSteps.next_sequence source middle _ _ first (Nat.le_refl _)]
  rw [WitnessRadix.StateSteps.next_sequence middle later _ _ second (Nat.le_refl _)]
  rw [WitnessRadix.StateSteps.next_sequence later (memoryReady source) _ _ third (Nat.le_refl _)]
  exact WitnessRadix.BuildEntry.zero_return (memoryReady source)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.body_shape
#print axioms InitECandidate.Solver.Input.Main.original_code
#print axioms InitECandidate.Solver.Input.Main.memory_code
#print axioms InitECandidate.Solver.Input.Main.memory_execute
