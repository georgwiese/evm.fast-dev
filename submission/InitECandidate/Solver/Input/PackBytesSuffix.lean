import InitECandidate.Solver.Input.PackBytesAllocation
import InitECandidate.Solver.Input.ZeroShortCost
import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem zero_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat) (small : n≤134217728)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (chunksLocal : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n))))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=
      some (Zero.values (cursor+BitVec.ofNat 64 n) (padded n-n)) := by
  have difference := BitVec.ofNat_sub_ofNat_of_le (w:=64) (padded n) n (by omega) (padding_bounds n).1
  have amount : BitVec.ofNat 64 (chunks n)*32#64=BitVec.ofNat 64 (padded n) := by simp [padded,BitVec.ofNat_mul,BitVec.mul_comm]
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,amountExpression,localVar,buffer,count,chunksLocal,Zero.values,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,amount,difference]

private theorem ignored_local (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key function : MlS) (arguments : List (ExpHOL 64))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : post.locals.lookup key=source.locals.lookup key := by
  have safe : LocalPrefix key (.call (some (none,none)) function arguments) := .call none _ _ (by intro name impossible; cases impossible)
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [run] at summary
  exact summary.1 rfl

theorem after_copy_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat) (small : n≤134217728)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (chunksLocal : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))))
    (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source afterCopy).2.clock≤63 := by
  have args := zero_arguments source cursor n small buffer count chunksLocal
  have geometry := padding_geometry cursor n arena aligned
  have price := ZeroShort.call_cost source zeroArguments (cursor+BitVec.ofNat 64 n) (padded n-n) (by have bounds:=padding_bounds n; omega)
    args installed domain geometry.1 geometry.2.2
  rw [body_shape.2.2.2]
  exact ClockCost.sequence_current source _ _ 63 0 price (ClockCost.returned source.code _)

/-- The actual copy plus at-most31byte padding and tuple return have an
alignment-independent linear source-clock bound, including every outcome. -/
theorem buffer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n : Nat) (small : n≤134217728)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (chunksLocal : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source afterBuffer).2.clock≤n/8+71 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) copyArguments=some (CopyGeneral.values cursor p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,copyArguments,localVar,pointer,buffer,count,CopyGeneral.values]
  have dstArena := AllocatedBytes.Arena.weaken cursor (padded n) n arena (padding_bounds n).1
  have copyCost := CopyGeneral.call_cost_blocks source copyArguments p cursor n args (CopyGeneral.original_code source.code installed)
    (AllocatedBytes.copy_mapped source p cursor n domain inputArena dstArena) (by omega)
  rw [body_shape.2.2.1]
  have price := ClockCost.sequence_reached_current source _ afterCopy (n/8+8) 63 copyCost (by
    intro middle normal
    have fields := evaluation_fields source middle _ none normal
    exact after_copy_cost middle cursor n small (fields.2.2.2.symm ▸ installed) (fields.1.trans domain)
      ((ignored_local source middle (ofString "buf") (ofString "memcpy") copyArguments normal).trans buffer)
      ((ignored_local source middle (ofString "n") (ofString "memcpy") copyArguments normal).trans count)
      ((ignored_local source middle (ofString "count") (ofString "memcpy") copyArguments normal).trans chunksLocal) arena aligned)
  omega

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.zero_arguments
#print axioms InitECandidate.Solver.Input.PackBytes.after_copy_cost
#print axioms InitECandidate.Solver.Input.PackBytes.buffer_cost
