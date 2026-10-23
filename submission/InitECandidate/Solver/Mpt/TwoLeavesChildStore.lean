import InitECandidate.Solver.Mpt.TwoLeavesProgram
import InitECandidate.Solver.Mpt.TrieGraphChildStore

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual child destination uses a genuine current nibble, so it is
one of the sixteen mapped branch slots. The original store then preserves
the complete registered graph, values and full protected path buffers. -/
theorem leaf_store_paths (second : Bool) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (branch leaf key : BitVec 64) (length : Nat) (span : TrieWalk.NibbleSpan source.memory source.memaddrs source.be key length) (positive : 0<length)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (keyCell : source.locals.lookup (ofString (label second "k1" "k2"))=some (.val (.word key)))
    (leafCell : source.locals.lookup (ofString (label second "lf1" "lf2"))=some (.val (.word leaf)))
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64) (leafMember : graph.valid leaf) :
    ∃ index : Nat,index<16 ∧
      (let post:={source with memory:=StoreWord.put source.memory (branch+BitVec.ofNat 64 (32+index*8)) leaf}
       evaluateHOLFiniteState source (leafStore second)=(none,post) ∧
        ∃ next : TrieWalk.Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated) := by
  obtain ⟨nibble,small,byteRead⟩:=span.nibble 0 positive
  have first : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be key=some nibble:=by
    simpa only [byteAddress,BitVec.add_zero] using byteRead
  have product : BitVec.ofNat 64 nibble.toNat*8#64=BitVec.ofNat 64 (nibble.toNat*8):=by rw [BitVec.ofNat_mul]
  have addressRead : eval source (childAddress second)=some (.val (.word (branch+BitVec.ofNat 64 (32+nibble.toNat*8)))):=by
    simp [childAddress,eval,localVar,evalHOLExact,evalListHOLExact,toExact,branchCell,keyCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,first,product,BitVec.ofNat_add,←BitVec.add_assoc]
  have valueRead : eval source (localVar (label second "lf1" "lf2"))=some (.val (.word leaf)):=by
    simp [eval,localVar,evalHOLExact,toExact,leafCell]
  have notHash : wordAt source.memory branch≠0#64:=by rw [tag]; decide
  have notLeaf : wordAt source.memory branch≠1#64:=by rw [tag]; decide
  have notExtension : wordAt source.memory branch≠2#64:=by rw [tag]; decide
  let old:=graph.branch branch branchMember branchActive notHash notLeaf notExtension nibble.toNat small
  have mapped : source.memaddrs (branch+BitVec.ofNat 64 (32+nibble.toNat*8)):=by
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc] using old.mapped
  have run:=StoreWord.execute source (childAddress second) (localVar (label second "lf1" "lf2"))
    (branch+BitVec.ofNat 64 (32+nibble.toNat*8)) leaf addressRead valueRead mapped
  rw [←(side_shapes second).2.2] at run
  exact ⟨nibble.toNat,small,run,
    graph.after_child_store source limit lower upper pathLower pathUpper property values regions disjoint paths pathRegions separated branch leaf (32+nibble.toNat*8)
      (.branch notHash notLeaf notExtension nibble.toNat small) branchMember branchActive leafMember⟩

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.leaf_store_paths
