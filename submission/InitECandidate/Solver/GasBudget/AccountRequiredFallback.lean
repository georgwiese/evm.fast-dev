import InitECandidate.Solver.GasBudget.AccountRequiredProgram
import InitECandidate.Solver.Mpt.AccountEmptyAssignedRegistered
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.MutableTable.FamilyControl

namespace InitECandidate.Solver.GasBudget.AccountRequired
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout Mpt

/-- The actual common nonoptional getter suffix returns a current registered
account or executes the original assigned empty-account fallback. Its real
price is at most3; every earlier word and live table/value is retained. -/
theorem fallback_normal {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value root hash : BitVec 64) (cutoff cursor : Nat) (objects : ι → TableFamily.Object) (anchor : ι)
    (accounts : List (BitVec 64)) (family : TableFamily.Model source cursor objects)
    (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property)
    (known : AccountDecode.Registry.Known accounts value) (above : cutoff≤cursor)
    (cell : source.locals.lookup (ofString "a")=some (.val (.word value)))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word hash)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterGet=(some (.returned returned),post)) :
    ∃ paid nextCursor nextAccounts word,paid≤3 ∧ paid≤source.clock ∧ post.clock=source.clock-paid ∧ cursor≤nextCursor ∧
      (nextCursor=cursor ∨ nextCursor=cursor+56) ∧ TableFamily.Model post nextCursor objects ∧
      AccountDecode.Registry post cutoff nextCursor objects nextAccounts ∧ TableFamily.ValuesHave post objects property ∧
      AccountDecode.Registry.Extension accounts nextAccounts cursor ∧
      word∈nextAccounts ∧ returned=.val (.word word) ∧ Nonempty (AccountDecode.Image post word) ∧ HeapGlobals source post ∧
      post.code=source.code ∧ post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.ffi.oracle=source.ffi.oracle ∧
      (∀ query : BitVec 64,query.toNat<cursor → post.memory query=source.memory query) := by
  rw [fallback_dispatch source value cell] at normal
  by_cases absent : value=1#64
  · rw [if_pos absent] at normal
    have safe : Input.LocalPrefix (ofString "addr") emptyCall := .call (some (ofString "a")) _ _ (by
      intro name equal
      have same := Option.some.inj equal
      rw [←same]
      decide)
    obtain ⟨assigned,assignRun,returnRun,saved⟩ := safe.normal_continue source post (.return (localVar "a")) returned normal
    have table := family.tables anchor
    let heap := BitVec.ofNat 64 cursor
    have heapNumber : heap.toNat=cursor := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := table.bounded; omega)]
    have heapLower : 2701131776≤heap.toNat := by
      rw [heapNumber]
      have lower := table.valid.lower .header
      have before := table.earlier .header
      change (objects anchor).plan.base .header+72≤cursor at before
      omega
    have currentFamily : TableFamily.Model source heap.toNat objects := by rw [heapNumber]; exact family
    have currentRegistry : AccountDecode.Registry source cutoff heap.toNat objects accounts := by rw [heapNumber]; exact registry
    obtain ⟨funded,room,canonical,assignedCell,clock,rounded,image,window,globals,heapAfter,nextFamily,nextRegistry,nextValues,weakening,freshKnown⟩ :=
      AccountEmpty.assigned_registered source assigned heap root hash cutoff objects accounts currentFamily currentRegistry property tableValues
        (by rw [heapNumber]; exact above) rootGlobal hashGlobal table.heap heapLower (by rw [heapNumber]; exact table.bounded)
        (by rw [heapNumber]; exact table.aligned) domain rootArena hashArena installed (ofString "a") [] rfl assignRun
    rw [heapNumber] at nextFamily nextRegistry weakening
    have actual := Input.return_normal assigned post (localVar "a") returned returnRun
    have read : eval assigned (localVar "a")=some (.val (.word heap)) := by simp [eval,localVar,evalHOLExact,toExact,assignedCell]
    have returnedEq : returned=.val (.word heap) := Option.some.inj (actual.1.symm.trans read)
    have postEq := actual.2
    have postFamily : TableFamily.Model post (cursor+56) objects := by rw [postEq]; exact nextFamily.of_control rfl rfl rfl rfl
    have postRegistry := nextRegistry.framed assigned post cutoff (cursor+56) (cursor+56) objects objects (accounts++[heap])
      (TableFamily.PersistentFrame.of_memory cutoff (cursor+56) objects assigned post (by rw [postEq] <;> rfl)) (Nat.le_refl _) (by rw [postEq] <;> rfl)
    have postValues := nextValues.of_memory assigned post objects property (by rw [postEq] <;> rfl)
    have member : heap∈accounts++[heap] := by simp
    refine ⟨3,cursor+56,accounts++[heap],heap,Nat.le_refl _,funded,?_,by omega,Or.inr rfl,postFamily,postRegistry,postValues,weakening,member,returnedEq,
      postRegistry.images heap member,?_,?_,?_,?_,?_,?_⟩
    · rw [postEq]; exact clock
    · rw [postEq]; exact globals
    · rw [postEq,canonical]; rfl
    · rw [postEq,canonical]; rfl
    · rw [postEq,canonical]; rfl
    · rw [postEq,canonical]; rfl
    · intro query earlier
      rw [postEq]
      apply window query
      left
      rw [heapNumber]
      exact earlier
  · rw [if_neg absent] at normal
    have returnedEq : returned=.val (.word value) := by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst normal).symm
    have postEq : post=emptyLocalsHOLFinite source := (congrArg Prod.snd normal).symm
    have member : value∈accounts := by
      rcases known with sentinel | member
      · exact (absent sentinel).elim
      · exact member
    have postFamily : TableFamily.Model post cursor objects := by rw [postEq]; exact family.of_control rfl rfl rfl rfl
    have postRegistry := registry.framed source post cutoff cursor cursor objects objects accounts
      (TableFamily.PersistentFrame.of_memory cutoff cursor objects source post (by rw [postEq] <;> rfl)) (Nat.le_refl _) (by rw [postEq] <;> rfl)
    have postValues := tableValues.of_memory source post objects property (by rw [postEq] <;> rfl)
    refine ⟨0,cursor,accounts,value,by decide,Nat.zero_le _,?_,Nat.le_refl _,Or.inl rfl,postFamily,postRegistry,postValues,AccountDecode.Registry.Extension.refl accounts cursor,member,returnedEq,
      postRegistry.images value member,?_,?_,?_,?_,?_,?_⟩
    · rw [postEq]; simp only [Nat.sub_zero]; rfl
    · rw [postEq]; exact HeapGlobals.refl source
    · rw [postEq]; rfl
    · rw [postEq]; rfl
    · rw [postEq]; rfl
    · rw [postEq]; rfl
    · intro query earlier; rw [postEq]; rfl

end InitECandidate.Solver.GasBudget.AccountRequired

#print axioms InitECandidate.Solver.GasBudget.AccountRequired.fallback_normal
