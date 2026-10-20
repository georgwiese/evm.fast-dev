import InitECandidate.Solver.Input.PContainerSuffixCost
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Cost after the real temporary64 allocation: actual progressive root
followed by the bounded activity-mask/SHA suffix, on every non-timeout path. -/
theorem after_tmp_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n<32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (tmp+64#64))))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (tmpArena : AllocatedBytes.Arena tmp 64)
    (arena : AllocatedBytes.Arena (tmp+64#64) (832+64*n)) (aligned : tmp.toNat%8=0) (cursorAligned : (tmp+64#64).toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTmp=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤116*n+24203 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) progressiveArguments=some (Progressive.values ch (BitVec.ofNat 64 n) tmp) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,progressiveArguments,localVar,chunks,count,temporary,Progressive.values]
  rw [body_shape.2.2.1] at run
  have price := ClockCost.sequence_terminating source post _ afterProgressive (115*n+24147) (n+56)
    (by intro actual target evaluated notTimeout
        exact Progressive.call_cost source target ch (tmp+64#64) tmp zeros stp accel n (by omega) workspace.sha heap workspace.zerosLocal
          inputArena arena cursorAligned (AllocatedBytes.Arena.weaken tmp 64 32 tmpArena (by omega)) workspace.zeroArena (some none) progressiveArguments args actual evaluated notTimeout)
    (by intro middle normal actual target evaluated notTimeout
        have nextWorkspace := SszHash.Workspace.after source middle stp accel chunk zeros workspace _ none normal
          (fun key different=>GlobalEffects.call_body key source.code (some none) (ofString "merkleize_progressive") progressiveArguments Progressive.formals Progressive.body .one
            (Progressive.original_code source.code workspace.sha.installed) (Progressive.globals key source.code workspace.sha.installed different))
        have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
          CallNormal.ignored_lookup source middle (ofString name) (ofString "merkleize_progressive") progressiveArguments normal
        have suffix := after_progressive_cost middle tmp out stp accel n short nextWorkspace.sha ((other "tmp").trans temporary)
          ((other "out").trans output) ((other "n").trans count) tmpArena aligned
        rw [evaluated] at suffix
        exact suffix)
    result run notTimeout
  omega

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.after_tmp_cost
