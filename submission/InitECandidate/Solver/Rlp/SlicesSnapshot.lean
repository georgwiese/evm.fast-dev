import InitECandidate.Solver.Rlp.SlicesNormal
import InitECandidate.Solver.Rlp.SlicesGlobals
import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.EvaluationOracle

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Current physical result of the actual original list converter. The
origin erases only caller locals/clock so real callee entries share it. -/
structure Snapshot (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit count : BitVec 64) (items : List ListItem) : Prop where
  itemModel : ListItems target pointer length.toNat items
  countExact : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  records : Records target.memory heap pointer items
  arrayArena : AllocatedBytes.Arena heap (16*count.toNat)
  arrayAligned : heap.toNat%8=0
  arena : Validation.Arena target cursor limit
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64))))
  nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (count*16#64)) 0
  nextAligned : (PersistentAlloc.rounded heap (count*16#64)).toNat%8=0
  grows : heap.toNat+16*count.toNat≤(PersistentAlloc.rounded heap (count*16#64)).toNat
  domain : target.memaddrs=origin.memaddrs
  endian : target.be=origin.be
  code : target.code=origin.code
  exceptions : target.eshapes=origin.eshapes
  oracle : target.ffi.oracle=origin.ffi.oracle
  globals : ∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=origin.globals.lookup key
  memory : ∀ query : BitVec 64,cursor.toNat≤query.toNat→query.toNat<heap.toNat ∨ heap.toNat+16*count.toNat≤query.toNat→target.memory query=origin.memory query

/-- Derive the complete physical snapshot from the same genuine normal
original body. Heap room, row count, cursor restoration and metadata frames
are conclusions; no successful later conversion is assumed. -/
theorem body_snapshot (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ items : List ListItem,∃ count : BitVec 64,value=result heap count ∧ Snapshot (Input.LocalEffects.erase source) target pointer length heap cursor limit count items := by
  obtain ⟨items,count,itemModel,countExact,countBound,valueEq,records,room,nextArena,nextHeap,memory,price⟩:=
    body_normal source target pointer length heap cursor limit cutoff pointerCell lengthCell arena heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove installed value normal
  have fields:=Input.evaluation_fields source target body (some (.returned value)) normal
  have oracle:=Input.evaluation_oracle source target body (some (.returned value)) normal
  have amountNumber : (count*16#64).toNat=16*count.toNat:=by
    rw [BitVec.toNat_mul]
    change (count.toNat*16)%2^64=16*count.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have checked:=PersistentAlloc.guards heap (count*16#64) (by rw [amountNumber]; exact room)
  have grows:=checked.2.2.1
  rw [amountNumber] at grows
  have heapLower : 2701131776≤heap.toNat:=by
    have lower:=arena.lower
    have ordered:=arena.ordered
    omega
  have allocated : AllocatedBytes.Arena heap (16*count.toNat):=⟨heapLower,room⟩
  have afterHeap : AllocatedBytes.Arena (PersistentAlloc.rounded heap (count*16#64)) 0:=
    ⟨by omega,by have upper:=checked.2.2.2.1; omega⟩
  have globalCells (key : MlS) (notHeap : key≠ofString "heap_ptr") : target.globals.lookup key=source.globals.lookup key:=by
    by_cases scratch : key=ofString "scratch_ptr"
    · subst key
      exact nextArena.cursorGlobal.trans arena.cursorGlobal.symm
    · have frame:=globals key source.code installed notHeap scratch source rfl
      rw [normal] at frame
      exact congrArg Prod.snd frame
  exact ⟨items,count,valueEq,⟨itemModel,countExact,countBound,records,allocated,heapAligned,nextArena,nextHeap,afterHeap,checked.2.2.2.2,grows,
    fields.1,fields.2.1,fields.2.2.2,fields.2.2.1,oracle,globalCells,memory⟩⟩

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.body_snapshot
