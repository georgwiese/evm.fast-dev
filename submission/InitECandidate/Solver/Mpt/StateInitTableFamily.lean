import InitECandidate.Solver.Mpt.StateInitBlockModels

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable MutableTable.NaturalLayout
open Flapjack.Basis.Pure.MlString GasBudget.Journal

def allObjects (heap : BitVec 64) (old : TableFamily.Object) : Option (Fin (entries (PersistentAlloc.rounded heap 80#64).toNat actions).length) → TableFamily.Object
  | none=>old
  | some index=>objects (PersistentAlloc.rounded heap 80#64).toNat index

/-- The earlier workspace cache and seven actual block tables form one
family at the same real heap; the complete journal remains outside it. -/
theorem Initialized.add_older_table (post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64)
    (initialized : Initialized post heap workspace) (old : TableFamily.Object) (cursor : Nat)
    (table : TableState post old.kind old.plan old.slots cursor old.floor)
    (before : ∀ pool,old.plan.base pool+size old.kind old.plan pool≤heap.toNat) :
    TableFamily.Model post cursor (allObjects heap old) ∧
      Zone (allObjects heap old) ((PersistentAlloc.rounded heap 80#64).toNat+70840+64) Initialization.capacity cursor:=by
  obtain ⟨bs,ws,head,count,family,pointers,zone,image,cap,journal,counter,transaction⟩:=initialized
  let start:=(PersistentAlloc.rounded heap 80#64).toNat
  let first : Fin (entries start actions).length:=⟨0,by rewrite [table_count]; decide⟩
  have current:=(family.tables first)
  have number : cursor=heap.toNat+16848200:=by
    have words:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (table.heap.symm.trans current.heap)))
    have numeric:=congrArg BitVec.toNat words
    have oldBound:=table.bounded
    have newBound:=current.bounded
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show cursor<2^64 by omega),
      Nat.mod_eq_of_lt (show heap.toNat+16848200<2^64 by omega)] at numeric
    exact numeric
  have startBefore : heap.toNat≤start:=by
    have bound:=current.bounded
    have rounded:=PersistentAlloc.rounded_nat heap 80#64 (by change heap.toNat+80+7<2^64; omega)
    change start=(heap.toNat+80+7)/8*8 at rounded
    omega
  have lower (index : Fin (entries start actions).length) (pool : Pool) : heap.toNat≤(objects start index).plan.base pool:=by
    have entryBefore:=entries_lower start actions ((entries start actions)[index]) (List.getElem_mem index.isLt)
    exact startBefore.trans (entryBefore.trans (fresh_bounds ((entries start actions)[index]).kind ((entries start actions)[index]).start
      (2^((entries start actions)[index]).bits) pool).1)
  have whole : TableFamily.Model post cursor (allObjects heap old):=by
    constructor
    · intro index
      cases index with
      | none=>exact table
      | some index=>rewrite [number]; exact family.tables index
    · intro first second different
      cases first with
      | none=>
        cases second with
        | none=>exact (different rfl).elim
        | some second=>intro left right; left; exact (before left).trans (lower second right)
      | some first=>
        cases second with
        | none=>intro left right; right; exact (before right).trans (lower first left)
        | some second=>exact family.apart first second (fun same=>different (congrArg Option.some same))
  have wholeZone : Zone (allObjects heap old) (start+70840+64) Initialization.capacity cursor:=by
    refine ⟨zone.valid,?_,?_⟩
    · rewrite [number]; exact zone.earlier
    · intro index inside field which
      cases which with
      | some which=>exact zone.separate index inside field which
      | none=>
        apply TableFootprint.Outside.of_regions old.kind old.plan table.valid
        intro pool
        right
        rewrite [entry_number (start+70840+64) Initialization.capacity index field zone.valid inside]
        have earlier:=before pool
        omega
  exact ⟨whole,wholeZone⟩

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.Initialized.add_older_table
