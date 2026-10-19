import InitECandidate.Solver.Mpt.WsAccountLeafProgram

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current physical account-root and separate lookup scratch facts. This
is an entry model; startup/constructor reachability is proved separately. -/
structure Data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root h nibs : BitVec 64) where
  graph : TrieWalk.Graph source.memory source.memaddrs
  member : graph.valid root
  protectedGraph : graph.Protected nibs
  worldState : source.globals.lookup (ofString "ws")=some (.val (.word ws))
  rootMapped : source.memaddrs (ws+24#64)
  rootStored : source.memory (ws+24#64)=.word root
  scratch : source.globals.lookup (ofString "mpt_nib_scratch")=some (.val (.word nibs))
  little : source.be=false
  fits : nibs.toNat+64<2^64
  inputMapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width := 64) (byteAddress h offset))
  outputMapped : ∀ offset<64,source.memaddrs (panByteAlignHOL (width := 64) (byteAddress nibs offset))
  separate : ∀ left<32,∀ right<64,byteAddress h left≠byteAddress nibs right

/-- Transport unchanged current root/scratch memory through allocation or
local setup, allowing unrelated globals such as the heap cursor to change. -/
def Data.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root h nibs : BitVec 64)
    (data : Data source ws root h nibs) (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs)
    (endian : target.be=source.be)
    (world : target.globals.lookup (ofString "ws")=source.globals.lookup (ofString "ws"))
    (scratch : target.globals.lookup (ofString "mpt_nib_scratch")=source.globals.lookup (ofString "mpt_nib_scratch")) :
    Data target ws root h nibs := by
  let next := TrieWalk.Graph.rebase source.memory target.memory source.memaddrs target.memaddrs data.graph memory domain
  have validEq : next.valid=data.graph.valid := TrieWalk.Graph.rebase_valid _ _ _ _ _ memory domain
  refine {
    graph := next
    member := by rw [validEq]; exact data.member
    protectedGraph := ?_
    worldState := world.trans data.worldState
    rootMapped := by rw [domain]; exact data.rootMapped
    rootStored := by rw [memory]; exact data.rootStored
    scratch := scratch.trans data.scratch
    little := endian.trans data.little
    fits := data.fits
    inputMapped := by simpa only [domain] using data.inputMapped
    outputMapped := by simpa only [domain] using data.outputMapped
    separate := data.separate }
  intro query required
  exact data.protectedGraph query (TrieWalk.Graph.footprint_transport _ _ _ _ data.graph next validEq
    (by intro node member active; rw [memory]) query required)

theorem Data.after_hash (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (control : KeccakAbsorb.hashControl post=KeccakAbsorb.hashControl source)
    (memory : ∀ query,Keccak256.Protected stp pad h query → post.memory query=source.memory query) :
    Nonempty (Data post ws root h nibs) := by
  obtain ⟨next,validEq,nextProtection⟩ := TrieWalk.Graph.after_hash source post data.graph stp pad h nibs data.protectedGraph graphProtection control memory
  have globals := congrArg PanSemStateFiniteExact.globals control
  have domain := congrArg PanSemStateFiniteExact.memaddrs control
  have endian := congrArg PanSemStateFiniteExact.be control
  change post.globals=source.globals at globals
  change post.memaddrs=source.memaddrs at domain
  change post.be=source.be at endian
  exact ⟨{
    graph := next
    member := by rw [validEq]; exact data.member
    protectedGraph := nextProtection
    worldState := by rw [globals]; exact data.worldState
    rootMapped := by rw [domain]; exact data.rootMapped
    rootStored := (memory _ rootProtection).trans data.rootStored
    scratch := by rw [globals]; exact data.scratch
    little := endian.trans data.little
    fits := data.fits
    inputMapped := by simpa only [domain] using data.inputMapped
    outputMapped := by simpa only [domain] using data.outputMapped
    separate := data.separate }⟩

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.Data.of_fields
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.Data.after_hash
