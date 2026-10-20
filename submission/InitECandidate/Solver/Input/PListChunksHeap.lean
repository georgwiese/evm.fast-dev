import InitECandidate.Solver.Input.PListChunksProgram
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Input.PListChunks
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Every actual normal original list-chunk hash restores its entry heap:
the real progressive caller derives its own normal return/restoration,
and the remaining length mix preserves every global on all outcomes. -/
theorem body_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena roots (32*n)) (temporaryArena : AllocatedBytes.Arena cursor (832+64*n)) (aligned : cursor.toNat%8=0)
    (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) progressiveArguments=some (Progressive.values roots (BitVec.ofNat 64 n) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,progressiveArguments,QueryBranch.localVar,root,count,output,Progressive.values]
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterRoot value (safe.summary_full source).2.1 run
  have nextHeap := Progressive.ignored_return_heap source middle roots cursor out zeros stp accel n bounded workspace.sha heap workspace.zerosLocal
    inputArena temporaryArena aligned outArena workspace.zeroArena progressiveArguments args normal
  have fields := evaluation_fields source middle _ none normal
  have nextInstalled : OriginalCode.Installed middle.code := fields.2.2.2.symm ▸ workspace.sha.installed
  have pure : GlobalEffects.Preserves (ofString "heap_ptr") middle.code afterRoot :=
    GlobalEffects.sequence (ofString "heap_ptr") middle.code _ _
      (GlobalEffects.call_body (ofString "heap_ptr") middle.code (some none) (ofString "mix_in_length") mixArguments MixLength.formals MixLength.body .one
        (MixLength.original_code middle.code nextInstalled) (MixLength.globals (ofString "heap_ptr") middle.code nextInstalled))
      (GlobalEffects.returned (ofString "heap_ptr") middle.code _)
  have frame := pure middle rfl
  rw [remaining] at frame
  exact (congrArg Prod.snd frame).trans nextHeap

end InitECandidate.Solver.Input.PListChunks

#print axioms InitECandidate.Solver.Input.PListChunks.body_return_heap
