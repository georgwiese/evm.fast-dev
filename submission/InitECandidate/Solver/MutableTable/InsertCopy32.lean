import InitECandidate.Solver.MutableTable.InsertStores
import InitECandidate.Solver.WitnessRadix.Copy32Environment

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- The literal raw-insertion memcpy call executes its actual aligned
32-byte body and ABI, restoring every caller local. -/
theorem copy_call32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters) (index : BitVec 64)
    (locals : Find.Locals source p index) (keyLength : p.keyLength=32#64) (words : Fin 4→BitVec 64)
    (code : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (mask : ((p.keys+index*p.stride) ||| p.key) &&& 7#64=0#64)
    (view : MemoryBytes.WordView source p.key words)
    (mapped : ∀ limb : Fin 4,source.memaddrs (p.keys+index*p.stride+BitVec.ofNat 64 (8*limb.val)))
    (separate : ∀ read write : Fin 4,p.key+BitVec.ofNat 64 (8*read.val)≠p.keys+index*p.stride+BitVec.ofNat 64 (8*write.val))
    (enough : 2≤source.clock) :
    evaluateHOLFiniteState source copyCall=
      (none,{source with memory:=Copy32.memory source.memory (p.keys+index*p.stride) words,clock:=source.clock-2}) := by
  have args:=Find.comparison_arguments source p index locals keyLength
  obtain ⟨callee,lookup,dstLocal,srcLocal,nLocal,unused⟩:=Copy32.environment source.code.lookup (p.keys+index*p.stride) p.key code
  exact Copy32.call_execute source callee _ p.key (p.keys+index*p.stride) words args lookup srcLocal dstLocal nLocal mask view mapped separate enough

/-- Compose the checked real copy call with its checked post-copy suffix.
The supplied run concerns only the suffix, not memcpy or the whole body. -/
theorem lift_copy32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters) (index : BitVec 64)
    (locals : Find.Locals source p index) (keyLength : p.keyLength=32#64) (words : Fin 4→BitVec 64)
    (code : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (mask : ((p.keys+index*p.stride) ||| p.key) &&& 7#64=0#64)
    (view : MemoryBytes.WordView source p.key words)
    (mapped : ∀ limb : Fin 4,source.memaddrs (p.keys+index*p.stride+BitVec.ofNat 64 (8*limb.val)))
    (separate : ∀ read write : Fin 4,p.key+BitVec.ofNat 64 (8*read.val)≠p.keys+index*p.stride+BitVec.ofNat 64 (8*write.val))
    (enough : 2≤source.clock) (target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (tailRun : evaluateHOLFiniteState
      {source with memory:=Copy32.memory source.memory (p.keys+index*p.stride) words,clock:=source.clock-2} afterCopy=
      (some (.returned (.val (.word 0#64))),target)) :
    evaluateHOLFiniteState source afterLoop=(some (.returned (.val (.word 0#64))),target) := by
  have copyRun:=copy_call32 source p index locals keyLength words code mask view mapped separate enough
  rw [afterLoop,StateSteps.next_sequence source _ copyCall afterCopy copyRun (by exact Nat.sub_le _ _)]
  exact tailRun

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.copy_call32
#print axioms InitECandidate.Solver.MutableTable.Insert.lift_copy32
