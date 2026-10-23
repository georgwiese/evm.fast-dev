import InitECandidate.Solver.Mpt.SplitExtensionProgram
import InitECandidate.Solver.Mpt.TrieGraphChildStore

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both original old-side stores select a genuine nibble from the full
stored suffix, even when that suffix starts beyond a64-nibble query. -/
theorem old_store_paths (source : PanSemStateFiniteExact 64 Guest.HostMemory) (branch child segment prefixLength : BitVec 64)
    (name : String) (length : Nat) (span : TrieWalk.NibbleSpan source.memory source.memaddrs source.be (segment+prefixLength) length) (positive : 0<length)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (childCell : source.locals.lookup (ofString name)=some (.val (.word child)))
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (branchMember : graph.valid branch) (active : branch≠0#64) (tag : wordAt source.memory branch=3#64) (childMember : graph.valid child) :
    ∃ index : Nat,index<16 ∧
      (let post:={source with memory:=StoreWord.put source.memory (branch+BitVec.ofNat 64 (32+index*8)) child}
       evaluateHOLFiniteState source (.store oldChildAddress (localVar name))=(none,post) ∧
         (∀ node,graph.valid node → node≠0#64 → wordAt post.memory node=wordAt source.memory node) ∧
         ∃ next : TrieWalk.Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
           Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated) := by
  obtain ⟨nibble,small,byteRead⟩:=span.nibble 0 positive
  have first : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (segment+prefixLength)=some nibble:=by
    simpa only [byteAddress,BitVec.add_zero] using byteRead
  have product : BitVec.ofNat 64 nibble.toNat*8#64=BitVec.ofNat 64 (nibble.toNat*8):=by rw [BitVec.ofNat_mul]
  have addressRead : eval source oldChildAddress=some (.val (.word (branch+BitVec.ofNat 64 (32+nibble.toNat*8)))):=by
    simp [oldChildAddress,oldAtPrefix,eval,localVar,evalHOLExact,evalListHOLExact,toExact,branchCell,segmentCell,prefixCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,first,product,BitVec.ofNat_add,←BitVec.add_assoc]
  have valueRead : eval source (localVar name)=some (.val (.word child)):=by simp [eval,localVar,evalHOLExact,toExact,childCell]
  have notHash : wordAt source.memory branch≠0#64:=by rw [tag]; decide
  have notLeaf : wordAt source.memory branch≠1#64:=by rw [tag]; decide
  have notExtension : wordAt source.memory branch≠2#64:=by rw [tag]; decide
  let old:=graph.branch branch branchMember active notHash notLeaf notExtension nibble.toNat small
  have mapped : source.memaddrs (branch+BitVec.ofNat 64 (32+nibble.toNat*8)):=by simpa only [BitVec.ofNat_add,←BitVec.add_assoc] using old.mapped
  have slot : TrieWalk.ChildSlot source.memory branch (32+nibble.toNat*8):=.branch notHash notLeaf notExtension nibble.toNat small
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt (StoreWord.put source.memory (branch+BitVec.ofNat 64 (32+nibble.toNat*8)) child) node=wordAt source.memory node:=by
    intro node member nodeActive
    apply congrArg MemoryBytes.wordBits
    exact if_neg (graph.child_store_header_away lower upper regions disjoint branch (32+nibble.toNat*8) slot branchMember active node member nodeActive)
  exact ⟨nibble.toNat,small,StoreWord.execute source oldChildAddress (localVar name) _ child addressRead valueRead mapped,tags,
    graph.after_child_store source limit lower upper pathLower pathUpper property values regions disjoint paths pathRegions separated branch child (32+nibble.toNat*8) slot branchMember active childMember⟩

/-- The actual new-side store uses the saved current nibble index. -/
theorem new_store_paths (source : PanSemStateFiniteExact 64 Guest.HostMemory) (branch child : BitVec 64) (index : Nat) (small : index<16)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word (BitVec.ofNat 64 index))))
    (childCell : source.locals.lookup (ofString "lf")=some (.val (.word child)))
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (branchMember : graph.valid branch) (active : branch≠0#64) (tag : wordAt source.memory branch=3#64) (childMember : graph.valid child) :
    let post:={source with memory:=StoreWord.put source.memory (branch+BitVec.ofNat 64 (32+index*8)) child}
    evaluateHOLFiniteState source newLeafStore=(none,post) ∧
      (∀ node,graph.valid node → node≠0#64 → wordAt post.memory node=wordAt source.memory node) ∧
      ∃ next : TrieWalk.Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  have product : BitVec.ofNat 64 index*8#64=BitVec.ofNat 64 (index*8):=by rw [BitVec.ofNat_mul]
  have addressRead : eval source newChildAddress=some (.val (.word (branch+BitVec.ofNat 64 (32+index*8)))):=by
    simp [newChildAddress,eval,localVar,evalHOLExact,evalListHOLExact,toExact,branchCell,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,product,BitVec.ofNat_add,←BitVec.add_assoc]
  have valueRead : eval source (localVar "lf")=some (.val (.word child)):=by simp [eval,localVar,evalHOLExact,toExact,childCell]
  have notHash : wordAt source.memory branch≠0#64:=by rw [tag]; decide
  have notLeaf : wordAt source.memory branch≠1#64:=by rw [tag]; decide
  have notExtension : wordAt source.memory branch≠2#64:=by rw [tag]; decide
  let old:=graph.branch branch branchMember active notHash notLeaf notExtension index small
  have mapped : source.memaddrs (branch+BitVec.ofNat 64 (32+index*8)):=by simpa only [BitVec.ofNat_add,←BitVec.add_assoc] using old.mapped
  have slot : TrieWalk.ChildSlot source.memory branch (32+index*8):=.branch notHash notLeaf notExtension index small
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt (StoreWord.put source.memory (branch+BitVec.ofNat 64 (32+index*8)) child) node=wordAt source.memory node:=by
    intro node member nodeActive
    apply congrArg MemoryBytes.wordBits
    exact if_neg (graph.child_store_header_away lower upper regions disjoint branch (32+index*8) slot branchMember active node member nodeActive)
  exact ⟨StoreWord.execute source newChildAddress (localVar "lf") _ child addressRead valueRead mapped,tags,
    graph.after_child_store source limit lower upper pathLower pathUpper property values regions disjoint paths pathRegions separated branch child (32+index*8) slot branchMember active childMember⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.old_store_paths
#print axioms InitECandidate.Solver.Mpt.SplitExtension.new_store_paths
