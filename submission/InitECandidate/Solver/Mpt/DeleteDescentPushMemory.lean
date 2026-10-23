import InitECandidate.Solver.Mpt.DeleteDescentModel
import InitECandidate.Solver.Mpt.DeleteFramePaths

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- At the real initialized-record state, actual allocation room locates
the forty scratch bytes. The complete old trie/query and physical PREV
chain survive, while the genuine saved parent extends that chain. Room
is derived from push_entry by callers; no future graph is presumed. -/
theorem descent_push_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (kind : DeleteFrame.Kind) (words : String→BitVec 64)
    (topEq : words "top"=model.pending.top)
    (room : Arenas.Room .down model.pending.cursor model.pending.frame 40#64)
    (owned : DeleteFrame.Saved.Owned ⟨Arenas.resultWord .down model.pending.cursor 40#64,kind,words⟩ model.pending.graph) :
    let record:=Arenas.resultWord .down model.pending.cursor 40#64
    let current:=DeleteFrame.stored kind source model.pending.cursor words
    let saved : DeleteFrame.Saved:=⟨record,kind,words⟩
    ∃ next : TrieWalk.Graph current.memory current.memaddrs,next.valid=model.pending.graph.valid ∧
      next.Regions nodeLower model.pending.heap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
      next.PathBytes current.be ∧ next.PathRegions pathLower model.pending.heap.toNat ∧ next.PathSeparated ∧
      next.PathBuffer current.be pathLower model.pending.heap.toNat key length.toNat ∧ model.pending.graph.PathFields current.memory ∧
      DeleteFrame.Stack current record.toNat record (saved::model.pending.frames) ∧ DeleteFrame.Parents next (saved::model.pending.frames) ∧
      Rlp.Validation.Arena current record model.pending.frame ∧ record.toNat+40≤model.pending.cursor.toNat ∧
      (∀ query : BitVec 64,query.toNat<model.pending.frame.toNat→current.memory query=source.memory query) ∧
      (∀ query : BitVec 64,model.pending.cursor.toNat≤query.toNat→current.memory query=source.memory query) ∧
      (∀ name,name≠ofString "scratch_ptr"→current.globals.lookup name=source.globals.lookup name) := by
  let record:=Arenas.resultWord .down model.pending.cursor 40#64
  let current:=DeleteFrame.stored kind source model.pending.cursor words
  let saved : DeleteFrame.Saved:=⟨record,kind,words⟩
  have nodesAbove : DeleteFrame.ceiling≤nodeLower:=model.pending.floor.trans model.pending.pathFloor
  obtain ⟨next,same,regions,disjoint,values,paths,pathRegions,separated⟩:=DeleteFrame.stored_paths kind source model.pending.cursor model.pending.frame words
    model.pending.scratch model.pending.scratchBefore room model.pending.graph limit nodeLower pathLower model.pending.heap.toNat property model.pending.values model.pending.regions model.pending.disjoint
      model.pending.paths model.pending.pathRegions model.pending.separated nodesAbove model.pending.floor
  have buffer:=DeleteFrame.stored_buffer kind source model.pending.cursor model.pending.frame words model.pending.scratch model.pending.scratchBefore room
    model.pending.graph next nodeLower pathLower model.pending.heap.toNat key length.toNat model.pending.regions nodesAbove model.query model.pending.floor same
  have high (query : BitVec 64) (above : model.pending.cursor.toNat≤query.toNat) : current.memory query=source.memory query:=
    DeleteFrame.allocated_writes_above kind source.memory model.pending.cursor model.pending.frame words model.pending.scratch.lower model.pending.scratchBefore model.pending.scratch.aligned room query above
  have fields : model.pending.graph.PathFields current.memory:=by
    apply TrieWalk.Graph.PathFields.of_agreement
    intro query required
    have above:=(model.pending.graph.footprint_bounds nodeLower model.pending.heap.toNat model.pending.regions query required).1
    exact high query (model.pending.scratchBefore.trans (nodesAbove.trans above))
  have members (node : BitVec 64) (member : model.pending.graph.valid node) : next.valid node:=by rw [same]; exact member
  have currentOwned : saved.Owned next:=owned.of_fields saved model.pending.graph next members fields
  have parents : DeleteFrame.Parents next (saved::model.pending.frames):=
    (model.pending.parents.of_fields model.pending.graph next model.pending.frames members fields).push next model.pending.frames saved currentOwned
  have previous : DeleteFrame.Stack source model.pending.cursor.toNat (words "top") model.pending.frames:=by rw [topEq]; exact model.pending.stack
  have stack:=DeleteFrame.stored_stack kind source model.pending.cursor model.pending.frame words model.pending.scratch model.pending.scratchBefore room model.pending.frames previous
  obtain ⟨recordArena,recordAligned,recordFloor,recordBefore,_active,_valid⟩:=DeleteFrame.allocated_bounds model.pending.cursor model.pending.frame
    model.pending.scratch.lower model.pending.scratchBefore model.pending.scratch.aligned room
  have globals (name : MlS) (other : name≠ofString "scratch_ptr") : current.globals.lookup name=source.globals.lookup name:=by
    simp [current,DeleteFrame.stored,DeleteFrame.allocated,Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
  have scratch : Rlp.Validation.Arena current record model.pending.frame:={
    domain:=model.pending.scratch.domain
    cursorGlobal:=by
      simp [current,record,DeleteFrame.stored,DeleteFrame.allocated,Arenas.post,Arenas.pointerName,Arenas.resultWord,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    limitGlobal:=(globals (ofString "frame_mem_ptr") (by decide)).trans model.pending.scratch.limitGlobal
    ordered:=recordFloor
    aligned:=model.pending.scratch.aligned
    lower:=model.pending.scratch.lower
    upper:=by have upper:=model.pending.scratch.upper; change record.toNat+40≤model.pending.cursor.toNat at recordBefore; omega }
  have low (query : BitVec 64) (before : query.toNat<model.pending.frame.toNat) : current.memory query=source.memory query:=by
    apply DeleteFrame.written_outside kind source.memory record words recordArena recordAligned query
    exact Or.inl (before.trans_le recordFloor)
  exact ⟨next,same,regions,disjoint,values,paths,pathRegions,separated,buffer,fields,stack,parents,scratch,recordBefore,low,high,globals⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_push_memory
