import InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost
import InitECandidate.Solver.Input.CurrentHash.MemoryContextTransport
import InitECandidate.Solver.Input.CopyAwaySubrange

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryStep
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive ProgressiveRound

theorem updates_frozen (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (off size k : BitVec 64)
    (position : source.locals.lookup (ofString "off")=some (.val (.word off)))
    (sizeLocal : source.locals.lookup (ofString "size")=some (.val (.word size)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word k)))
    (actual : evaluateHOLFiniteState source updates=(none,post)) : CeilLog2.frozen post=CeilLog2.frozen source := by
  have executed := updates_execute source off size k position sizeLocal round
  rw [actual] at executed
  have endpoint : post=advanced source off size k := congrArg Prod.snd executed
  rw [endpoint]
  rfl

theorem after_cap_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros query : BitVec 64) (n k : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Round source p roots n k)
    (bounded : n≤134217728) (active : offset k<n)
    (count : source.locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 (min (4^k) (n-offset k))))))
    (inputArena : AllocatedBytes.Arena p (32*n)) (rootsArena : AllocatedBytes.Arena roots 768) (rootsAway : CopyGeneral.Away roots query 768)
    (actual : evaluateHOLFiniteState source afterCap=(none,post)) : post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  have countBound := Nat.min_le_left (4^k) (n-offset k)
  have countNumber : (BitVec.ofNat 64 (min (4^k) (n-offset k))).toNat=min (4^k) (n-offset k) := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sizeNumber : (BitVec.ofNat 64 (4^k)).toNat=4^k := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args := merkle_arguments source p roots (offset k) (min (4^k) (n-offset k)) (4^k) k
    data.pointer data.rootsLocal data.position count data.sizeLocal data.round
  have input := AllocatedBytes.Arena.subrange p (32*n) (32*offset k) (32*min (4^k) (n-offset k)) inputArena
    (by have h:=Nat.min_le_right (4^k) (n-offset k); omega)
  have output := AllocatedBytes.Arena.subrange roots 768 (32*k) 32 rootsArena (by omega)
  have away := CopyGeneral.Away.subrange roots query 768 (32*k) 32 rootsAway (by omega)
  unfold afterCap at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_none source post _ updates actual
  have image := MerkleMemory.call_frame source middle (p+BitVec.ofNat 64 (32*offset k)) (BitVec.ofNat 64 (min (4^k) (n-offset k)))
    (BitVec.ofNat 64 (4^k)) (roots+BitVec.ofNat 64 (32*k)) cursor zeros query (2*k) context (by omega)
    (by rw [countNumber,←power]; exact countBound) (by rw [sizeNumber,←power])
    (by rw [countNumber]; exact input) output away arguments args normal
  have next := context.after_call .merkleize arguments image.2 normal
  have current := data.after_call _ _ normal
  have frame := updates_frozen middle post (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k)
    current.position current.sizeLocal current.round remaining
  have memory := congrArg PanSemStateFiniteExact.memory frame
  change post.memory=middle.memory at memory
  exact ⟨(congrArg (fun memory=>memory query) memory).trans image.1,next.of_frozen frame⟩

/-- Same actual capped Merkle round and counter updates retain protected
metadata and the real current heap, including both lexical cnt scopes. -/
theorem frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros query : BitVec 64) (n k : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Round source p roots n k)
    (bounded : n≤134217728) (active : offset k<n)
    (inputArena : AllocatedBytes.Arena p (32*n)) (rootsArena : AllocatedBytes.Arena roots 768) (rootsAway : CopyGeneral.Away roots query 768)
    (actual : evaluateHOLFiniteState source step=(none,post)) : post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  rw [step_prefix source n (offset k) (4^k) (by omega) (by omega) (by omega) data.count data.position data.sizeLocal] at actual
  let entry := pairEntry source n (offset k) (4^k)
  let final := (evaluateHOLFiniteState entry afterCap).2
  have observed := congrArg Prod.fst actual
  have remaining : evaluateHOLFiniteState entry afterCap=(none,final) := Prod.ext observed rfl
  have endpoint : post=restore source "cnt" final := (congrArg Prod.snd actual).symm
  have prefixFrame := (pair_entry_frame source n (offset k) (4^k)).1
  have image := after_cap_frame entry final p roots cursor zeros query n k (context.of_frozen prefixFrame) data.pair bounded active
    (pair_entry_count source n (offset k) (4^k)) inputArena rootsArena rootsAway remaining
  have restored : CeilLog2.frozen post=CeilLog2.frozen final := by rw [endpoint]; rfl
  have prefixMemory := congrArg PanSemStateFiniteExact.memory prefixFrame
  change entry.memory=source.memory at prefixMemory
  refine ⟨?_,image.2.of_frozen restored⟩
  rw [endpoint]
  exact image.1.trans (congrArg (fun memory=>memory query) prefixMemory)

end InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryStep

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryStep.updates_frozen
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryStep.after_cap_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryStep.frame
