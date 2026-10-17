import InitECandidate.Solver.Input.CopyLoop

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem walk_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    (walk source pointer index rounds).clock=source.clock-rounds := by
  induction rounds generalizing source index with
  | zero => simp [walk]
  | succ rounds ih =>
    rw [walk,ih]
    change source.clock-1-rounds=source.clock-(rounds+1)
    omega

theorem walk_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat)
    (name : MlS) (notIndex : ofString "i"≠name) (notWord : ofString "w"≠name) :
    (walk source pointer index rounds).locals.lookup name=source.locals.lookup name := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih => rw [walk,ih,wordPost_other _ _ _ _ notIndex notWord]; rfl

theorem walk_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat)
    (initial : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    (walk source pointer index rounds).locals.lookup (ofString "i")=
      some (.val (.word (BitVec.ofNat 64 (index+8*rounds)))) := by
  induction rounds generalizing source index with
  | zero => simpa [walk] using initial
  | succ rounds ih =>
    rw [walk]
    have next:=wordPost_index (decClockHOLFinite source) pointer (BitVec.ofNat 64 index)
    rw [←BitVec.ofNat_add] at next
    rw [ih _ _ next]
    have arithmetic : index+8+8*rounds=index+8*(rounds+1) := by omega
    rw [arithmetic]

theorem walk_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    (walk source pointer index rounds).globals=source.globals ∧
    (walk source pointer index rounds).code=source.code ∧
    (walk source pointer index rounds).memaddrs=source.memaddrs ∧
    (walk source pointer index rounds).shMemaddrs=source.shMemaddrs ∧
    (walk source pointer index rounds).ffi.ffiState=source.ffi.ffiState ∧
    (walk source pointer index rounds).ffi.oracle=source.ffi.oracle := by
  induction rounds generalizing source index with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ rounds ih => exact ih _ _

def copyRounds (length : Nat) : Nat := (length+7)/8

theorem copyRounds_bounds (length : Nat) :
    length≤8*copyRounds length ∧ 8*copyRounds length<length+8 ∧ copyRounds length≤16777214 ∨ Guest.maxInputBytes<length := by
  dsimp [copyRounds]
  change length≤8*((length+7)/8) ∧ 8*((length+7)/8)<length+8 ∧ (length+7)/8≤16777214 ∨ 134217712<length
  omega

theorem copyRounds_fit (length : Nat) (bounded : length≤Guest.maxInputBytes) :
    length≤8*copyRounds length ∧ 8*copyRounds length<length+8 ∧ copyRounds length≤16777214 := by
  have h:=copyRounds_bounds length
  omega

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.walk_clock
#print axioms InitECandidate.Solver.Input.Blob.walk_other
#print axioms InitECandidate.Solver.Input.Blob.walk_index
#print axioms InitECandidate.Solver.Input.Blob.walk_frame
#print axioms InitECandidate.Solver.Input.Blob.copyRounds_bounds
#print axioms InitECandidate.Solver.Input.Blob.copyRounds_fit
