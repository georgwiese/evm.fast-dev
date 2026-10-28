import InitECandidate.Solver.Input.CurrentVerify.DatabaseContext
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.CappedCost

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A nonempty actual record array lies beyond all copied input, and before
the real persistent frontier. Empty witness slices have length zero. -/
theorem database_length_bound {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {start length boundary offset limit countLimit : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (image : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary offset limit countLimit) :
    length≤251655184 := by
  by_cases empty : length=0
  · omega
  · have geometry := image.records.array_geometry source input pointer array start length empty
    have afterInput := geometry.2.2.2.2
    have before := image.before
    have inside := image.inside
    have lower := image.inputLower
    obtain ⟨heap,cell,heapLower,heapUpper,aligned⟩ := data.heap
    omega

/-- A uniform source-clock bound for either real node/code database body.
This includes allocation failure before the count cap and every later stop. -/
theorem database_uniform_body_cost {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {start length boundary offset limit countLimit : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (image : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary offset limit countLimit)
    (limitBound : limit≤65536) (small : VarList.decodedCount input start length<2^31)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "slice_arr")=some (.val (.word (VarList.decodedArray array length))))
    (countCell : callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) CurrentTable.NodeBuild.body=(outcome,post)) :
    (callEntryStateHOLFinite source callee).clock-post.clock≤1661620381 := by
  have entry := database_entry data image limitBound small callee arrayCell countCell
  have budget := image.records.size_bounds source input pointer array start length
  have cost := CurrentTable.NodeBuild.body_capped_byte_cost _ _ _ entry length budget.1 outcome run
  have lengthBound := database_length_bound data image
  have blockBound : length/136≤1850405 := Nat.le_trans (Nat.div_le_div_right lengthBound) (by decide)
  have countBound := Nat.min_le_right (VarList.decodedCount input start length) 1048575
  change (callEntryStateHOLFinite source callee).clock-post.clock≤44*(length/136)+1507*(min (VarList.decodedCount input start length) 1048575)+36 at cost
  omega

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.database_length_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.database_uniform_body_cost
