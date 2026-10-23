import InitECandidate.Solver.Mpt.InsertEmptyFinish
import InitECandidate.Solver.Mpt.TrieParentSlot
import InitECandidate.Solver.Mpt.TrieGraphChildStore
import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Mpt.TrieProtectedMutation

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual loop footer updates either its local root or its genuine
saved parent slot. Its complete closed graph and all current path buffers
survive either original operation. -/
theorem choose_result_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (slot root : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower nodeUpper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower nodeUpper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (selected : graph.ParentSlot slot) (member : graph.valid root)
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word slot)))
    (rootCell : source.locals.lookup (ofString "r")=some (.val (.word root)))
    (normal : evaluateHOLFiniteState source chooseResult=(none,target)) :
    target.locals=(if slot=0#64 then source.locals.update (ofString "result",.val (.word root)) else source.locals) ∧
      target.globals=source.globals ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ target.clock=source.clock ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ node,graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower nodeUpper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated ∧
        (∀ key length,graph.PathBuffer source.be pathLower pathUpper key length → next.PathBuffer target.be pathLower pathUpper key length) ∧
        graph.PathFields target.memory ∧ (∀ address : BitVec 64,(slot≠0#64 → address≠slot) → target.memory address=source.memory address) := by
  have read : eval source (localVar "r")=some (.val (.word root)):=by simp [eval,evalHOLExact,toExact,localVar,rootCell]
  by_cases zero : slot=0#64
  · have chosen : evaluateHOLFiniteState source chooseResult=evaluateHOLFiniteState source (.assign .local (ofString "result") (localVar "r")):=by
      rw [chooseResult,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,slotCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have endpoint:=Input.assign_none source target "result" (localVar "r") root read (chosen.symm.trans normal)
    rw [endpoint,if_pos zero]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,(by intro query before; rfl),(by intro node live active; rfl),
      graph,rfl,regions,disjoint,⟨values⟩,paths,pathRegions,separated,(by intro key length buffer; exact buffer),
      ⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩,(by intro address _different; rfl)⟩
  · rcases selected with empty|⟨owner,offset,ownerMember,ownerActive,location,address⟩
    · exact (zero empty).elim
    have chosen : evaluateHOLFiniteState source chooseResult=evaluateHOLFiniteState source (.store (localVar "slot") (localVar "r")):=by
      rw [chooseResult,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,slotCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have destination : eval source (localVar "slot")=some (.val (.word (owner+BitVec.ofNat 64 offset))):=by
      simp [eval,evalHOLExact,toExact,localVar,slotCell,address]
    obtain ⟨mapped,endpoint⟩:=Input.word_store_normal source target (localVar "slot") (localVar "r") (owner+BitVec.ofNat 64 offset) root destination read (chosen.symm.trans normal)
    subst target
    let post:={source with memory:=StoreWord.put source.memory (owner+BitVec.ofNat 64 offset) root}
    obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
      graph.after_child_store source limit nodeLower nodeUpper pathLower pathUpper property values regions disjoint paths pathRegions separated owner root offset location ownerMember ownerActive member
    have tags : ∀ node,graph.valid node → node≠0#64 → wordAt post.memory node=wordAt source.memory node:=by
      intro node live active
      apply congrArg MemoryBytes.wordBits
      exact if_neg (graph.child_store_header_away nodeLower nodeUpper regions disjoint owner offset location ownerMember ownerActive node live active)
    have olderMemory (query : BitVec 64) (before : query.toNat<nodeLower) : post.memory query=source.memory query:=by
      have bounds:=regions owner ownerMember ownerActive
      have within:=(location.bounds source.memory owner offset).2.2.1
      have away : query≠owner+BitVec.ofNat 64 offset:=by
        intro equal
        have number:=congrArg BitVec.toNat equal
        change query.toNat=(byteAddress owner offset).toNat at number
        rw [byteAddress_toNat owner offset (by have upper:=bounds.2.1.upper; omega)] at number
        omega
      exact if_neg away
    rw [if_neg zero]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,olderMemory,tags,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
      (by intro key length buffer; exact buffer.after_child_store source graph pathLower pathUpper key length owner root offset location ownerMember ownerActive next same tags),
      TrieWalk.Graph.PathFields.of_child_store graph nodeLower nodeUpper regions disjoint owner root offset location ownerMember ownerActive,
      (by intro query different; exact if_neg (fun equal=>different zero (equal.trans address.symm)))⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.choose_result_normal
