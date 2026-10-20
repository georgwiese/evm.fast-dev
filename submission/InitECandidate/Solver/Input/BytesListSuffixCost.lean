import InitECandidate.Solver.Input.BytesListProgram
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_release_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out stp accel chunk zeros : BitVec 64) (n : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (outArena : AllocatedBytes.Arena out 32) : source.clock-(evaluateHOLFiniteState source afterRelease).2.clock≤59 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) mixArguments=some (MixLength.values out (BitVec.ofNat 64 n) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,mixArguments,localVar,output,count,MixLength.values]
  have price := MixLength.call_cost source out (BitVec.ofNat 64 n) out chunk stp accel workspace.sha workspace.chunkLocal outArena workspace.chunkArena workspace.chunkAligned (some none) mixArguments args
  rw [body_shape.2.2.2.2]
  exact ClockCost.sequence_current source _ _ 59 0 price (ClockCost.returned source.code _)

theorem after_merkle_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out stp accel chunk zeros : BitVec 64) (n : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (outArena : AllocatedBytes.Arena out 32) : source.clock-(evaluateHOLFiniteState source afterMerkle).2.clock≤60 := by
  have releasePrice := HeapScope.release_call_cost source.code workspace.sha.installed (some none) [localVar "mark"] source rfl
  rw [body_shape.2.2.2.1]
  apply ClockCost.sequence_reached_current source _ afterRelease 1 59 releasePrice
  intro middle normal
  have next := SszHash.Workspace.after source middle stp accel chunk zeros workspace _ none normal (fun key different=>
    GlobalEffects.call_body key source.code (some none) (ofString "heap_release") [localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one
      (HeapScope.release_original_code source.code workspace.sha.installed) (Merkle.release_globals key source.code different))
  exact after_release_cost middle out stp accel chunk zeros n next
    ((CallNormal.ignored_lookup source middle (ofString "out") (ofString "heap_release") [localVar "mark"] normal).trans output)
    ((CallNormal.ignored_lookup source middle (ofString "n") (ofString "heap_release") [localVar "mark"] normal).trans count) outArena

/-- Main's actual extra-data hash uses <=32bytes and literal limit1; only
its real packed chunk count is charged in the original Merkle call. -/
theorem after_pack_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n≤32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterPack=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*PackBytes.chunks n+74 := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n (by omega) arena aligned
  have chunksBound := extra_chunks n short
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat=PackBytes.chunks n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have merkleArena := AllocatedBytes.Arena.weaken _ (832+64*PackBytes.chunks n) (32*max 1 (2*PackBytes.chunks n)) temporaryArena (by omega)
  have args := merkle_arguments source cursor out n packed limitLocal output
  have front : ∀ result target,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") merkleArguments)=(result,target) →
      result≠some .timeOut → source.clock-target.clock≤115*PackBytes.chunks n+14 := by
    intro result target actual notTimeout
    have price := Merkle.call_cost source target cursor (BitVec.ofNat 64 (PackBytes.chunks n)) 1#64 (cursor+BitVec.ofNat 64 (PackBytes.padded n)) out zeros stp accel 0 (by decide)
      (by rw [number]; change PackBytes.chunks n≤1; exact chunksBound) (by decide) workspace.sha heap workspace.zerosLocal
      (by rw [number]; exact packedArena) (by rw [number]; exact merkleArena) temporaryAligned outArena workspace.zeroArena (some none) merkleArguments args result actual notTimeout
    simpa only [number,Nat.mul_zero,Nat.add_zero] using price
  rw [body_shape.2.2.1] at run
  have price := ClockCost.sequence_terminating source post _ afterMerkle (115*PackBytes.chunks n+14) 60 front (by
    intro middle normal result target continued notTimeout
    have next := SszHash.Workspace.after source middle stp accel chunk zeros workspace _ none normal (fun key different=>
      GlobalEffects.call_body key source.code (some none) (ofString "merkleize") merkleArguments Merkle.formals Merkle.body .one
        (Merkle.original_code source.code workspace.sha.installed) (Merkle.globals key source.code workspace.sha.installed different))
    have bound := after_merkle_cost middle out stp accel chunk zeros n next
      ((CallNormal.ignored_lookup source middle (ofString "out") (ofString "merkleize") merkleArguments normal).trans output)
      ((CallNormal.ignored_lookup source middle (ofString "n") (ofString "merkleize") merkleArguments normal).trans count) outArena
    rw [continued] at bound
    exact bound) result run notTimeout
  exact price

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.after_release_cost
#print axioms InitECandidate.Solver.Input.BytesList.after_merkle_cost
#print axioms InitECandidate.Solver.Input.BytesList.after_pack_cost
