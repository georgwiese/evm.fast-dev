import InitECandidate.Solver.Input.PayloadHashStaticPipeline
import InitECandidate.Solver.Input.PayloadHashTransactionMemory
import InitECandidate.Solver.Input.PayloadHashWithdrawalMemory

namespace InitECandidate.Solver.Input.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Mathematical description of the actual decoded payload. These are
input/record values used by the original hasher, not replacement bytes. -/
structure Description where
  payload : BitVec 64
  raw : BitVec 64
  extra : BitVec 64
  extraLength : Nat
  transactions : BitVec 64
  transactionCount : Nat
  transactionPointer : Nat→BitVec 64
  transactionLength : Nat→Nat
  withdrawals : BitVec 64
  withdrawalCount : Nat
  balance : BitVec 64
  balanceLength : Nat

def Description.cells (data : Description) : List (Nat×BitVec 64) := [
  (0,data.raw),(16,data.extra),(24,BitVec.ofNat 64 data.extraLength),(32,data.transactions),(40,BitVec.ofNat 64 data.transactionCount),
  (48,data.withdrawals),(56,BitVec.ofNat 64 data.withdrawalCount),(64,data.balance),(72,BitVec.ofNat 64 data.balanceLength)]

structure Description.Image (data : Description) (origin : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  fields : ∀ cell∈data.cells,origin.memory (data.payload+BitVec.ofNat 64 cell.1)=.word cell.2
  rows : Transactions.Image origin data.transactions data.transactionPointer data.transactionLength data.transactionCount

/-- Physical decoded input and metadata extents at the fixed prehash input
frontier. All capacities are actual byte/count bounds; no hash outcomes. -/
structure Description.Layout (data : Description) (lower upper budget : Nat) : Prop where
  budgetBound : budget≤134217728
  payloadArena : AllocatedBytes.Arena data.payload 136
  payloadAligned : data.payload.toNat%8=0
  payloadLower : lower≤data.payload.toNat
  payloadBefore : data.payload.toNat+136≤upper
  rawArena : AllocatedBytes.Arena data.raw 540
  extraShort : data.extraLength≤32
  extraArena : AllocatedBytes.Arena data.extra data.extraLength
  transactionCountBound : data.transactionCount≤budget/4
  transactionArena : 0<data.transactionCount→AllocatedBytes.Arena data.transactions (16*data.transactionCount)
  transactionAligned : data.transactions.toNat%8=0
  transactionLower : 0<data.transactionCount→lower≤data.transactions.toNat
  transactionBefore : 0<data.transactionCount→data.transactions.toNat+16*data.transactionCount≤upper
  transactionLengths : ∀ index<data.transactionCount,data.transactionLength index≤budget
  transactionInputs : ∀ index<data.transactionCount,AllocatedBytes.Arena (data.transactionPointer index) (data.transactionLength index)
  transactionBytes : VarList.sumPrefix data.transactionLength data.transactionCount≤budget
  withdrawalCountBound : data.withdrawalCount≤budget/44
  withdrawalArena : AllocatedBytes.Arena data.withdrawals (44*data.withdrawalCount)
  balanceBound : data.balanceLength≤budget
  balanceArena : AllocatedBytes.Arena data.balance data.balanceLength

theorem Description.cells_valid (data : Description) : ∀ cell∈data.cells,cell.1<136 ∧ cell.1%8=0 := by
  intro cell member
  simp only [Description.cells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide

/-- Read an actual original payload field from the preserved decoded
region, with mapping derived from its current physical payload record. -/
theorem Description.field_read (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (image : data.Image origin) (layout : data.Layout lower upper budget)
    (current : HashInput.Frame origin source lower upper) (domain : source.memaddrs=InitE.ordinaryDomain)
    (payload : source.locals.lookup (ofString "pl")=some (.val (.word data.payload)))
    (cell : Nat×BitVec 64) (member : cell∈data.cells) : eval source (fieldExpression cell.1)=some (.val (.word cell.2)) := by
  have valid := data.cells_valid cell member
  have number : (data.payload+BitVec.ofNat 64 cell.1).toNat=data.payload.toNat+cell.1 := byteAddress_toNat data.payload cell.1 (by have h:=layout.payloadArena.upper; omega)
  have mapped : source.memaddrs (data.payload+BitVec.ofNat 64 cell.1) := AllocatedBytes.word_mapped source data.payload 136 cell.1 domain layout.payloadArena valid.1 layout.payloadAligned valid.2
  have stored := current.cell origin source lower upper (data.payload+BitVec.ofNat 64 cell.1) cell.2
    (by rw [number]; have h:=layout.payloadLower; omega) (by rw [number]; have h:=layout.payloadBefore; omega) (image.fields cell member)
  simp [eval,evalHOLExact,evalListHOLExact,toExact,fieldExpression,localVar,payload,valueIsWord,valueWord,wordOpHOL,wordOp,isWfShapeExactHOL,memLoadHOLExact,mapped,stored]

/-- Every actual decoded transaction row is still readable after earlier
field hashes, using the same fixed-region agreement. -/
theorem Description.current_rows (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (image : data.Image origin) (layout : data.Layout lower upper budget) (current : HashInput.Frame origin source lower upper) :
    Transactions.Image source data.transactions data.transactionPointer data.transactionLength data.transactionCount := by
  constructor
  intro index inside
  have positive : 0<data.transactionCount := by omega
  have arena := layout.transactionArena positive
  have pointerNumber : (data.transactions+BitVec.ofNat 64 (16*index)).toNat=data.transactions.toNat+16*index := byteAddress_toNat data.transactions (16*index) (by have h:=arena.upper; omega)
  have lengthNumber : (data.transactions+BitVec.ofNat 64 (16*index+8)).toNat=data.transactions.toNat+(16*index+8) := byteAddress_toNat data.transactions (16*index+8) (by have h:=arena.upper; omega)
  have pFrame := current.words (data.transactions+BitVec.ofNat 64 (16*index)) (by rw [pointerNumber]; have h:=layout.transactionLower positive; omega)
    (by rw [pointerNumber]; have h:=layout.transactionBefore positive; omega)
  have nFrame := current.words (data.transactions+BitVec.ofNat 64 (16*index+8)) (by rw [lengthNumber]; have h:=layout.transactionLower positive; omega)
    (by rw [lengthNumber]; have h:=layout.transactionBefore positive; omega)
  exact ⟨pFrame.trans (image.rows.fields index inside).1,nFrame.trans (image.rows.fields index inside).2⟩

end InitECandidate.Solver.Input.PayloadHash

#print axioms InitECandidate.Solver.Input.PayloadHash.Description.cells_valid
#print axioms InitECandidate.Solver.Input.PayloadHash.Description.field_read
#print axioms InitECandidate.Solver.Input.PayloadHash.Description.current_rows
