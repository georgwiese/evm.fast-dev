import InitECandidate.Solver.Mpt.DeleteUnwindProgram
import InitECandidate.Solver.Mpt.TrieGraphChildStore
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : DeleteFrame.Saved) (result : BitVec 64) :=
  {source with memory:=StoreWord.put source.memory (saved.node+BitVec.ofNat 64 (32+(saved.words "idx").toNat*8)) result}

/-- The original branch unwind stores the current registered result in
the true saved bounded child slot. Every saved parent and full path model
survives the real word store, including when nodes are shared. -/
theorem branch_child_store (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (saved : DeleteFrame.Saved) (result : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower upper pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (view : saved.View source) (owned : saved.Owned graph) (branchKind : saved.kind=.branch) (resultMember : graph.valid result)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)))
    (nodeCell : source.locals.lookup (ofString "fnode")=some (.val (.word saved.node)))
    (resultCell : source.locals.lookup (ofString "res")=some (.val (.word result)))
    (domain : source.memaddrs=InitE.ordinaryDomain) :
    let post:=branchPost source saved result
    evaluateHOLFiniteState source replaceChild=(none,post) ∧
      (∀ query : BitVec 64,query.toNat<nodeLower→post.memory query=source.memory query) ∧ graph.PathFields post.memory ∧
      ∃ next : TrieWalk.Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower upper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower upper ∧ next.PathSeparated := by
  classical
  obtain ⟨member,active,tag,data⟩:=owned
  have actualTag : wordAt source.memory saved.node=3#64:=by simpa only [branchKind,DeleteFrame.Kind.tag] using tag
  have small : (saved.words "idx").toNat<16:=by simpa only [branchKind] using data
  have notHash : wordAt source.memory saved.node≠0#64:=by rw [actualTag]; decide
  have notLeaf : wordAt source.memory saved.node≠1#64:=by rw [actualTag]; decide
  have notExtension : wordAt source.memory saved.node≠2#64:=by rw [actualTag]; decide
  let index:=(saved.words "idx").toNat
  let offset:=32+index*8
  let slot : TrieWalk.ChildSlot source.memory saved.node offset:=.branch notHash notLeaf notExtension index small
  let child:=graph.branch saved.node member active notHash notLeaf notExtension index small
  have indexRead:=branch_index_read source saved view branchKind domain topCell
  simp only [eval] at indexRead
  have nodeRead : evalHOLExact source.toExact (localVar "fnode")=some (.val (.word saved.node)):=by simp [localVar,evalHOLExact,toExact,nodeCell]
  have product : saved.words "idx"*8#64=BitVec.ofNat 64 (index*8):=by simp only [index,BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have addressEq : saved.node+32#64+saved.words "idx"*8#64=saved.node+BitVec.ofNat 64 offset:=by
    rw [product]
    simp only [offset,BitVec.ofNat_add,BitVec.add_assoc]
  have addressRead : eval source (childAddress "fnode" (field "top" 32#64))=some (.val (.word (saved.node+BitVec.ofNat 64 offset))):=by
    simp only [eval,childAddress,evalHOLExact,evalListHOLExact,nodeRead,indexRead,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
    simp [valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,←BitVec.add_assoc,addressEq]
  have resultRead : eval source (localVar "res")=some (.val (.word result)):=by simp [eval,localVar,evalHOLExact,toExact,resultCell]
  have mapped : source.memaddrs (saved.node+BitVec.ofNat 64 offset):=by
    simpa only [offset,BitVec.ofNat_add,←BitVec.add_assoc] using child.mapped
  have executed:=StoreWord.execute source _ _ _ result addressRead resultRead mapped
  have fields:=TrieWalk.Graph.PathFields.of_child_store graph nodeLower upper regions disjoint saved.node result offset slot member active
  have older (query : BitVec 64) (before : query.toNat<nodeLower) : (branchPost source saved result).memory query=source.memory query:=by
    apply if_neg
    intro same
    have number:=congrArg BitVec.toNat same
    have geometry:=regions saved.node member active
    have inside:=(slot.bounds source.memory saved.node offset).2.2.1
    change query.toNat=(byteAddress saved.node offset).toNat at number
    rw [byteAddress_toNat saved.node offset (by have upper:=geometry.2.1.upper; omega)] at number
    omega
  exact ⟨executed,older,fields,graph.after_child_store source limit nodeLower upper pathLower upper property values regions disjoint paths pathRegions separated
    saved.node result offset slot member active resultMember⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_child_store
