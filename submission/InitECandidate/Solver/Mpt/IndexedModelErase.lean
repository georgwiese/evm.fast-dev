import InitECandidate.Solver.Mpt.IndexedLoopModel
import InitECandidate.Solver.Mpt.TrieGraphPathErase

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual local restoration, counter assignment and clock decrement
transport the complete live model. The real caller bindings and bounded
new counter are supplied from those executed local operations. -/
theorem LoopModel.of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (m array index : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property)
    (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source)
    (indexCell : target.locals.lookup (ofString "i")=some (.val (.word index))) (bounded : index.toNat≤count)
    (countCell : target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (mCell : target.locals.lookup (ofString "m")=some (.val (.word m)))
    (arrayCell : target.locals.lookup (ofString "slice_arr")=some (.val (.word array))) :
    ∃ next : LoopModel target m array count cutoff limit slices property,next.index=index ∧ next.heap=model.heap := by
  have memory:=Input.LocalEffects.memory_of_erase source target frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  have codes:=congrArg PanSemStateFiniteExact.code frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  have oracle:=congrArg (fun state=>state.ffi.oracle) frame
  change target.memaddrs=source.memaddrs at domain
  change target.be=source.be at endian
  change target.code=source.code at codes
  change target.ffi.oracle=source.ffi.oracle at oracle
  change target.globals=source.globals at globals
  obtain ⟨next,same,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=model.graph.after_erase source target limit cutoff model.heap.toNat cutoff model.heap.toNat property
    model.values model.regions model.disjoint model.paths model.pathRegions model.separated frame
  let output : LoopModel target m array count cutoff limit slices property:={ model with
    index:=index
    indexCell:=indexCell
    countCell:=countCell
    mCell:=mCell
    arrayCell:=arrayCell
    bounded:=bounded
    domain:=domain.trans model.domain
    little:=endian.trans model.little
    installed:=by rw [codes]; exact model.installed
    bindings:=model.bindings.of_heap_globals source target (by intro name other; rw [globals])
    hash:=model.hash.of_fields source target 2713714976#64 2713715176#64 domain codes oracle (by intro name other; rw [globals])
    scratch:=model.scratch.of_fields source target 2713714688#64 2701135872#64 domain globals
    heapCell:=by rw [globals]; exact model.heapCell
    rows:=model.rows.of_band source target array count cutoff limit slices property domain (by intro query above before; rw [memory])
    graph:=next
    values:=nextValues
    regions:=nextRegions
    disjoint:=nextDisjoint
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated
    header:=model.header.of_erase source target model.graph next m model.root 0#64 same frame }
  exact ⟨output,rfl,rfl⟩

theorem LoopModel.dec_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property) :
    ∃ next : LoopModel (decClockHOLFinite source) m array count cutoff limit slices property,
      next.index=model.index ∧ next.heap=model.heap :=
  model.of_erase source (decClockHOLFinite source) m array model.index count cutoff limit slices property rfl
    model.indexCell model.bounded model.countCell model.mCell model.arrayCell

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.LoopModel.of_erase
#print axioms InitECandidate.Solver.Mpt.Indexed.LoopModel.dec_clock
