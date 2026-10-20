import InitECandidate.Solver.Input.PackBytesCallCost
import InitECandidate.Solver.Input.PackBytesGlobals
import InitECandidate.Solver.Input.PListChunksCallCost
import InitECandidate.Solver.Input.ClockCostTerminatingScoped

namespace InitECandidate.Solver.Input.PBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htr_pbytes with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)]
def packArguments : List (ExpHOL 64) := [localVar "p",localVar "n"]
def listArguments : List (ExpHOL 64) := [.rfield 0 (localVar "pk"),.rfield 1 (localVar "pk"),localVar "n",localVar "out"]
def afterList : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))
def afterPack : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "htr_plist_chunks") listArguments) afterList
def afterMark : ProgHOL 64 := .decCall (ofString "pk") PackBytes.returnShape (ofString "pack_bytes") packArguments afterPack

theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,Guest.guestFn_htr_pbytes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterMark,afterPack,afterList,PackBytes.returnShape,packArguments,listArguments,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_pbytes")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 179 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htr_pbytes) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_htr_pbytes,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- The literal pk field reads and byte length are the actual returned
original packing tuple, not independent input-root/count assumptions. -/
theorem list_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out : BitVec 64) (n : Nat)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) listArguments=
      some (PListChunks.values cursor (PackBytes.chunks n) (BitVec.ofNat 64 n) out) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,listArguments,localVar,packed,count,output,PackBytes.packedValue,PListChunks.values]

/-- Packing and the subsequent original progressive hash share one physical
arena, sized from actual byte length via the real returned chunk count. -/
theorem packing_geometry (cursor : BitVec 64) (n : Nat) (small : n≤134217728)
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) :
    PackBytes.chunks n≤134217728 ∧ AllocatedBytes.Arena cursor (PackBytes.padded n) ∧
    AllocatedBytes.Arena (cursor+BitVec.ofNat 64 (PackBytes.padded n)) (832+64*PackBytes.chunks n) ∧
    (cursor+BitVec.ofNat 64 (PackBytes.padded n)).toNat%8=0 := by
  have bounds := PackBytes.padding_bounds n
  have countBound : PackBytes.chunks n≤134217728 := by unfold PackBytes.chunks; omega
  have paddedArena := AllocatedBytes.Arena.weaken cursor (832+96*PackBytes.chunks n) (PackBytes.padded n) arena (by unfold PackBytes.padded; omega)
  have tailArena := AllocatedBytes.Arena.subrange cursor (832+96*PackBytes.chunks n) (PackBytes.padded n) (832+64*PackBytes.chunks n) arena (by unfold PackBytes.padded; omega)
  have number : (cursor+BitVec.ofNat 64 (PackBytes.padded n)).toNat=cursor.toNat+PackBytes.padded n := byteAddress_toNat cursor (PackBytes.padded n) (by have upper:=arena.upper; unfold PackBytes.padded; omega)
  refine ⟨countBound,paddedArena,tailArena,?_⟩
  rw [number]
  have multiple := bounds.2.2.1
  omega

end InitECandidate.Solver.Input.PBytes

#print axioms InitECandidate.Solver.Input.PBytes.body_shape
#print axioms InitECandidate.Solver.Input.PBytes.original_code
#print axioms InitECandidate.Solver.Input.PBytes.list_arguments
#print axioms InitECandidate.Solver.Input.PBytes.packing_geometry
