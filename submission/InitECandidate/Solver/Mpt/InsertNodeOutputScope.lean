import InitECandidate.Solver.Mpt.InsertNodeOutput
import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Join a real read-only scalar entry and lexical restoration to an
already derived dispatch output. Original graph membership is transported
through the actual pure frame, while all loop updates remain visible. -/
theorem NodeOutput.restore_scope (source ready inner : PanSemStateFiniteExact 64 Guest.HostMemory)
    (old : TrieWalk.Graph source.memory source.memaddrs) (base : TrieWalk.Graph ready.memory ready.memaddrs)
    (incoming key length level : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (name : String) (word : BitVec 64)
    (notRoot : ofString "r"≠ofString name) (notNode : ofString "next_node"≠ofString name)
    (notSlot : ofString "next_slot"≠ofString name) (notLevel : ofString "next_level"≠ofString name) (notGo : ofString "go"≠ofString name)
    (localsEq : ready.locals=source.locals.update (ofString name,.val (.word word)))
    (frame : Input.LocalEffects.erase ready=Input.LocalEffects.erase source) (same : base.valid=old.valid)
    (output : NodeOutput ready inner base incoming key length level limit nodeLower pathLower property) :
    Nonempty (NodeOutput source (restore source name inner) old incoming key length level limit nodeLower pathLower property) := by
  have memoryEq:=Input.LocalEffects.memory_of_erase source ready frame
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endianEq:=congrArg PanSemStateFiniteExact.be frame
  change ready.memaddrs=source.memaddrs at domainEq
  change ready.be=source.be at endianEq
  have restoredStable (query : MlS) (different : query≠ofString name) : (restore source name inner).locals.lookup query=inner.locals.lookup query:=by
    change (HolFiniteMapExact.resVarEq inner.locals (ofString name,source.locals.lookup (ofString name))).lookup query=_
    rw [lookup_resVarEq_toExact]
    cases source.locals.lookup (ofString name) with
    | none=>simp [resVarHOLExact,different]
    | some value=>simp [resVarHOLExact,different]
  have restoredSame : (restore source name inner).locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    change (HolFiniteMapExact.resVarEq inner.locals (ofString name,source.locals.lookup (ofString name))).lookup (ofString name)=_
    rw [lookup_resVarEq_toExact]
    cases source.locals.lookup (ofString name) with
    | none=>simp [resVarHOLExact]
    | some value=>simp [resVarHOLExact]
  have originalMember (node : BitVec 64) (live : old.valid node) : base.valid node:=by rw [same]; exact live
  have tags (node : BitVec 64) (live : old.valid node) (active : node≠0#64) : wordAt inner.memory node=wordAt source.memory node:=by
    rw [output.tags node (originalMember node live) active,memoryEq]
  have olderMemory (query : BitVec 64) (before : query.toNat<nodeLower) : inner.memory query=source.memory query:=
    (output.olderPrefix query before).trans (congrFun memoryEq query)
  have fields : old.PathFields ready.memory:=by
    rw [memoryEq]
    exact ⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩
  exact ⟨{ output with
    rootCell:=(restore_lookup_other source inner name "r" notRoot).trans output.rootCell
    nodeCell:=(restore_lookup_other source inner name "next_node" notNode).trans output.nodeCell
    slotCell:=(restore_lookup_other source inner name "next_slot" notSlot).trans output.slotCell
    levelCell:=(restore_lookup_other source inner name "next_level" notLevel).trans output.levelCell
    goCell:=(restore_lookup_other source inner name "go" notGo).trans output.goCell
    stable:=by
      intro query rootDifferent nodeDifferent slotDifferent levelDifferent goDifferent
      by_cases selected : query=ofString name
      · subst query
        exact restoredSame
      · rw [restoredStable query selected,output.stable query rootDifferent nodeDifferent slotDifferent levelDifferent goDifferent,localsEq]
        simp [HolFiniteMapExact.update,FUPDATE,Ne.symm selected]
    domain:=output.domain.trans domainEq
    endian:=output.endian.trans endianEq
    code:=output.code.trans (Input.LocalEffects.code_of_erase source ready frame)
    olderPrefix:=olderMemory
    oldPathFields:=fields.trans old base output.oldPathFields originalMember
    protectedMemory:=by
      intro address safe before
      have currentSafe:=safe.of_fields old base address same fields
      exact (output.protectedMemory address currentSafe before).trans (congrFun memoryEq address)
    freshMembers:=by
      intro node live
      rcases output.freshMembers node live with old|fresh
      · exact Or.inl (by rwa [same] at old)
      · exact Or.inr fresh
    protectedGraph:=by
      intro address safe before away
      exact output.protectedGraph address (safe.of_fields old base address same fields) before away
    activeRegistry:=by intro active; exact (output.activeRegistry active).trans same
    tags:=tags
    oldMember:=fun node live=>output.oldMember node (originalMember node live) }⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.NodeOutput.restore_scope
