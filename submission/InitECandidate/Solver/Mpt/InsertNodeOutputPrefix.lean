import InitECandidate.Solver.Mpt.InsertNodeOutput

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Compose a derived actual prefix frame with a real dispatch output.
Cache invalidation may change metadata; the genuine old tags, members and
older persistent memory suffice to retain the caller's complete result. -/
theorem NodeOutput.prepend (source ready target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (old : TrieWalk.Graph source.memory source.memaddrs) (base : TrieWalk.Graph ready.memory ready.memaddrs)
    (incoming current key length level : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (localsEq : ready.locals=source.locals) (domain : ready.memaddrs=source.memaddrs) (endian : ready.be=source.be) (code : ready.code=source.code)
    (grows : incoming.toNat≤current.toNat)
    (olderMemory : ∀ query : BitVec 64,query.toNat<nodeLower → ready.memory query=source.memory query)
    (tags : ∀ node,old.valid node → node≠0#64 → wordAt ready.memory node=wordAt source.memory node)
    (members : ∀ node,old.valid node → base.valid node)
    (same : base.valid=old.valid) (fields : old.PathFields ready.memory)
    (protectedWords : ∀ address : BitVec 64,old.ProtectedWord address → address.toNat<incoming.toNat → ready.memory address=source.memory address)
    (output : NodeOutput ready target base current key length level limit nodeLower pathLower property) :
    Nonempty (NodeOutput source target old incoming key length level limit nodeLower pathLower property) := by
  exact ⟨{ output with
    stable:=by intro name notRoot notNode notSlot notLevel notGo; rw [output.stable name notRoot notNode notSlot notLevel notGo,localsEq]
    domain:=output.domain.trans domain
    endian:=output.endian.trans endian
    code:=output.code.trans code
    heapGrows:=Nat.le_trans grows output.heapGrows
    olderPrefix:=fun query before=>(output.olderPrefix query before).trans (olderMemory query before)
    oldPathFields:=fields.trans old base output.oldPathFields members
    protectedMemory:=by
      intro address safe before
      have currentSafe:=safe.of_fields old base address same fields
      exact (output.protectedMemory address currentSafe (Nat.lt_of_lt_of_le before grows)).trans (protectedWords address safe before)
    freshMembers:=by
      intro node live
      rcases output.freshMembers node live with old|fresh
      · exact Or.inl (by rwa [same] at old)
      · exact Or.inr (Nat.le_trans grows fresh)
    protectedGraph:=by
      intro address safe before away
      exact output.protectedGraph address (safe.of_fields old base address same fields) (Nat.lt_of_lt_of_le before grows) away
    activeRegistry:=by intro active; exact (output.activeRegistry active).trans same
    tags:=fun node live active=>(output.tags node (members node live) active).trans (tags node live active)
    oldMember:=fun node live=>output.oldMember node (members node live) }⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.NodeOutput.prepend
