import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.ExtensionAssignedPathGraph
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Mpt.NodeConstructorProtected
import InitECandidate.Solver.Mpt.TrieCacheMutation

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- After a genuine split, original251 either takes the fresh branch or
constructs a positive extension over the actual protected old prefix. -/
theorem extension_result_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap segment prefixLength branch : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat segment prefixLength.toNat)
    (member : graph.valid branch) (floor : nodeLower≤heap.toNat)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source extensionSplitChoice=(none,target)) :
    ∃ root : BitVec 64,target.locals=source.locals.update (ofString "r",.val (.word root)) ∧
      target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤2 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      (∀ current,graph.valid current → current≠0#64 → wordAt target.memory current=wordAt source.memory current) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway segment prefixLength.toNat address → next.ProtectedWord address) ∧
          (TrieWalk.Uncached source.memory branch→TrieWalk.Uncached target.memory root) ∧ (branch≠0#64 → root≠0#64) ∧
          (wordAt source.memory branch≠0#64 → wordAt target.memory root≠0#64) := by
  by_cases zero : prefixLength=0#64
  · have selected : evaluateHOLFiniteState source extensionSplitChoice=evaluateHOLFiniteState source extensionBranchAssign:=by
      rw [extension_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,prefixCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have read : eval source (localVar "br")=some (.val (.word branch)):=by simp [eval,evalHOLExact,toExact,localVar,branchCell]
    rw [extension_shapes.2.2.2.2.2.2.2] at selected
    have endpoint:=Input.assign_none source target "r" (localVar "br") branch read (selected.symm.trans normal)
    rw [endpoint]
    exact ⟨branch,rfl,rfl,rfl,rfl,(by change source.clock-source.clock≤2; omega),(by intro query before; rfl),(by intro node live active; rfl),
      heap,heapCell,frontier,aligned,Nat.le_refl _,graph,(fun node live=>live),member,regions,disjoint,⟨values⟩,paths,pathRegions,separated,(by intro current live; exact Or.inl live),(by intro address safe _before _away; exact safe),(by intro clean; exact clean),(by intro live; exact live),(by intro nonhash; exact nonhash)⟩
  · have positive : 0<prefixLength.toNat:=by
      by_contra bad
      have number : prefixLength.toNat=(0#64).toNat:=by change prefixLength.toNat=0; omega
      exact zero (BitVec.toNat_inj.mp number)
    have wordPositive : (0#64 : BitVec 64)<prefixLength:=by rw [BitVec.lt_def]; exact positive
    have selected : evaluateHOLFiniteState source extensionSplitChoice=evaluateHOLFiniteState source extensionMakeCall:=by
      rw [extension_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,prefixCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,wordPositive]
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) extensionArguments=
        some [.val (.word segment),.val (.word prefixLength),.val (.word branch)]:=by
      simp [extensionArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,segmentCell,prefixCell,branchCell]
    have run:=selected.symm.trans normal
    rw [extension_shapes.2.2.2.2.2.2.1] at run
    obtain ⟨localsEq,codeEq,price,physical,next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
      NodeConstructor.extension_assigned_paths source target heap segment prefixLength branch (ofString "r") extensionArguments graph limit nodeLower pathLower property
        values regions disjoint paths pathRegions separated buffer member positive floor args domain heapCell frontier aligned installed run
    have grows : heap.toNat≤(PersistentAlloc.rounded heap 56#64).toNat:=by have before : heap.toNat+56≤(PersistentAlloc.rounded heap 56#64).toNat:=physical.before; omega
    have memory (query : BitVec 64) (before : query.toNat<heap.toNat) : target.memory query=source.memory query:=physical.memory query (Or.inl before)
    have tags (current : BitVec 64) (live : graph.valid current) (active : current≠0#64) : wordAt target.memory current=wordAt source.memory current:=by
      have before : current.toNat<heap.toNat:=by
        have bounds:=(regions current live active).2.2.2
        have size:=(TrieWalk.nodeBytes_bounds (wordAt source.memory current)).1
        omega
      unfold wordAt
      rw [memory current before]
    exact ⟨heap,localsEq,physical.domain,physical.endian,codeEq,price,memory,tags,PersistentAlloc.rounded heap 56#64,physical.heapCell,
      physical.nextArena,physical.nextAligned,grows,next,(fun node live=>(members node).mpr (Or.inl live)),rootMember,
      nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
      (by
        intro current live
        rcases (members current).mp live with old|new
        · exact Or.inl old
        · exact Or.inr (by rw [new])),
      (by
        intro address safe before away
        exact (physical.path_protected .extension (Or.inr rfl) source target heap _ graph next nodeLower regions members address safe before
          (by simpa [NodeConstructor.extensionWords] using away)).2),
      (fun _=>physical.uncached (Or.inr rfl)),(fun _=>physical.nonzero),(fun _=>physical.nonhash (Or.inr rfl))⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.extension_result_normal
