import InitECandidate.Solver.Mpt.LeafInsertSplitProgram
import InitECandidate.Solver.Mpt.ExtensionConstructorTail
import InitECandidate.Solver.Mpt.ExtensionConstructorPathGraph
import InitECandidate.Solver.Input.TailCallNoFallthrough
import InitECandidate.Solver.Mpt.NodeConstructorProtected

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original final split choice returns its actual branch or creates
a real positive-length extension around it. All older graph/path data and
memory below the current heap survive this true returning execution. -/
theorem after_branch_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key prefixLength branch : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat key prefixLength.toNat) (member : graph.valid branch) (floor : nodeLower≤heap.toNat)
    (keyCell : source.locals.lookup (ofString "ek")=some (.val (.word key)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterBranch=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤3 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap root : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ node,graph.valid node → next.valid node) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ node,next.valid node → graph.valid node ∨ heap.toNat≤node.toNat) ∧
          (∀ query : BitVec 64,graph.ProtectedWord query → query.toNat<heap.toNat →
            TrieWalk.PathWordAway key prefixLength.toNat query → next.ProtectedWord query) := by
  by_cases zero : prefixLength=0#64
  · have read : eval source prefixPositive=some (.val (.word 0#64)):=by
      simp [eval,prefixPositive,localVar,evalHOLExact,toExact,prefixCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at read
    have selected : evaluateHOLFiniteState source (.ite prefixPositive extensionCall .skip)=(none,source):=by
      rw [evaluateHOLFiniteState_ite,read]
      simp [evaluateHOLFiniteState_skip]
    have footerRun : evaluateHOLFiniteState source branchFooter=(some (.returned value),target):=by
      simpa only [split_shapes.2,evaluateHOLFiniteState_seq_line780,selected] using normal
    rw [branchFooter] at footerRun
    obtain ⟨observed,endpoint⟩:=Input.return_normal source target (localVar "br") value footerRun
    have expected : eval source (localVar "br")=some (.val (.word branch)):=by simp [eval,localVar,evalHOLExact,toExact,branchCell]
    have answer : value=.val (.word branch):=Option.some.inj (observed.symm.trans expected)
    rw [endpoint]
    exact ⟨rfl,rfl,rfl,(by change source.clock-source.clock≤3; omega),(by intro query before; rfl),heap,branch,answer,heapCell,frontier,aligned,Nat.le_refl _,
      graph,(fun _ live=>live),member,regions,disjoint,⟨values⟩,paths,pathRegions,separated,(by intro node live; exact Or.inl live),(by intro query safe _before _away; exact safe)⟩
  · have positive : 0<prefixLength.toNat:=by
      by_contra bad
      have number : prefixLength.toNat=(0#64).toNat:=by change prefixLength.toNat=0; omega
      exact zero (BitVec.toNat_inj.mp number)
    have wordPositive : (0#64 : BitVec 64)<prefixLength:=by rw [BitVec.lt_def]; exact positive
    have read : eval source prefixPositive=some (.val (.word 1#64)):=by
      simp [eval,prefixPositive,localVar,evalHOLExact,toExact,prefixCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,wordPositive]
    simp only [eval] at read
    have selected : evaluateHOLFiniteState source (.ite prefixPositive extensionCall .skip)=evaluateHOLFiniteState source extensionCall:=by
      rw [evaluateHOLFiniteState_ite,read]
      simp
    have sequenceRun : evaluateHOLFiniteState source (.seq extensionCall branchFooter)=(some (.returned value),target):=by
      simpa only [split_shapes.2,evaluateHOLFiniteState_seq_line780,selected] using normal
    have direct:=Input.NoFallthrough.sequence_eq source extensionCall branchFooter (Input.NoFallthrough.tail_call _ _)
    have tailRun : evaluateHOLFiniteState source extensionCall=(some (.returned value),target):=direct.symm.trans sequenceRun
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) extensionArguments=
        some [.val (.word key),.val (.word prefixLength),.val (.word branch)]:=by
      simp [extensionArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,keyCell,prefixCell,branchCell]
    obtain ⟨answer,physical,codeEq,price⟩:=NodeConstructor.extension_tail_physical source target heap key prefixLength branch extensionArguments args domain heapCell frontier aligned installed value tailRun
    obtain ⟨next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
      physical.extension_path_graph source target heap (NodeConstructor.extensionWords key prefixLength branch) domain aligned graph limit nodeLower pathLower property
        values regions disjoint paths pathRegions separated floor (by simpa [NodeConstructor.extensionWords] using buffer)
        (by simpa [NodeConstructor.extensionWords] using member) (by simpa [NodeConstructor.extensionWords] using positive)
    have grows : heap.toNat≤(PersistentAlloc.rounded heap 56#64).toNat:=by
      have before : heap.toNat+56≤(PersistentAlloc.rounded heap 56#64).toNat:=physical.before
      omega
    exact ⟨physical.domain,physical.endian,codeEq,price,(fun query before=>physical.memory query (Or.inl before)),PersistentAlloc.rounded heap 56#64,heap,answer,
      physical.heapCell,physical.nextArena,physical.nextAligned,grows,next,(fun node live=>(members node).mpr (Or.inl live)),rootMember,
      nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
      (by
        intro node live
        rcases (members node).mp live with old|new
        · exact Or.inl old
        · exact Or.inr (by rw [new])),
      (by
        intro query safe before away
        exact (physical.path_protected .extension (Or.inr rfl) source target heap _ graph next nodeLower regions members query safe before
          (by simpa [NodeConstructor.extensionWords] using away)).2)⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.after_branch_normal
