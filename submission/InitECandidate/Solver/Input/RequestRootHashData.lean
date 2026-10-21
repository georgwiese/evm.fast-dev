import InitECandidate.Solver.Input.RequestRootHashPhases

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Values of the actual original decoded SI and nested payload/request
metadata; no digest outputs or future helper outcomes occur here. -/
structure Description where
  si : BitVec 64
  payload : PayloadHash.Description
  blobs : BitVec 64
  blobCount : Nat
  parent : BitVec 64
  requests : BitVec 64
  requestPointer : RequestsHash.Kind→BitVec 64
  requestCount : RequestsHash.Kind→Nat

def Description.cells (data : Description) : List (Nat×BitVec 64) := [
  (0,data.payload.payload),(8,data.blobs),(16,BitVec.ofNat 64 data.blobCount),(24,data.parent),(32,data.requests)]

structure Description.Image (data : Description) (origin : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  fields : ∀ cell∈data.cells,origin.memory (data.si+BitVec.ofNat 64 cell.1)=.word cell.2
  payload : data.payload.Image origin
  requests : RequestsHash.Image origin data.requests data.requestPointer data.requestCount

structure Description.Layout (data : Description) (lower upper budget : Nat) : Prop where
  payload : data.payload.Layout lower upper budget
  siArena : AllocatedBytes.Arena data.si 40
  siAligned : data.si.toNat%8=0
  siLower : lower≤data.si.toNat
  siBefore : data.si.toNat+40≤upper
  blobsBound : data.blobCount≤budget/32
  blobsArena : AllocatedBytes.Arena data.blobs (32*data.blobCount)
  parentArena : AllocatedBytes.Arena data.parent 32
  requestsArena : AllocatedBytes.Arena data.requests 80
  requestsAligned : data.requests.toNat%8=0
  requestsLower : lower≤data.requests.toNat
  requestsBefore : data.requests.toNat+80≤upper
  requestCounts : ∀ kind,data.requestCount kind≤budget
  requestInputs : ∀ kind,AllocatedBytes.Arena (data.requestPointer kind) (data.requestCount kind*kind.record.length)

theorem Description.cells_valid (data : Description) : ∀ cell∈data.cells,cell.1<40 ∧ cell.1%8=0 := by
  intro cell member
  simp only [Description.cells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide

theorem Description.field_read (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (image : data.Image origin) (layout : data.Layout lower upper budget)
    (current : HashInput.Frame origin source lower upper) (domain : source.memaddrs=InitE.ordinaryDomain)
    (si : source.locals.lookup (ofString "si")=some (.val (.word data.si)))
    (cell : Nat×BitVec 64) (member : cell∈data.cells) : eval source (fieldExpression cell.1)=some (.val (.word cell.2)) := by
  have valid := data.cells_valid cell member
  have number : (data.si+BitVec.ofNat 64 cell.1).toNat=data.si.toNat+cell.1 := byteAddress_toNat data.si cell.1 (by have h:=layout.siArena.upper; omega)
  have mapped : source.memaddrs (data.si+BitVec.ofNat 64 cell.1) := AllocatedBytes.word_mapped source data.si 40 cell.1 domain layout.siArena valid.1 layout.siAligned valid.2
  have stored := current.cell origin source lower upper (data.si+BitVec.ofNat 64 cell.1) cell.2
    (by rw [number]; have h:=layout.siLower; omega) (by rw [number]; have h:=layout.siBefore; omega) (image.fields cell member)
  simp [eval,evalHOLExact,evalListHOLExact,toExact,fieldExpression,localVar,si,valueIsWord,valueWord,wordOpHOL,wordOp,isWfShapeExactHOL,memLoadHOLExact,mapped,stored]

theorem Description.current_requests (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (image : data.Image origin) (layout : data.Layout lower upper budget) (current : HashInput.Frame origin source lower upper) :
    RequestsHash.Image source data.requests data.requestPointer data.requestCount := by
  constructor
  intro kind
  have tag := RequestsHash.tag_bound kind
  have pNumber : (data.requests+BitVec.ofNat 64 (16*kind.tag)).toNat=data.requests.toNat+16*kind.tag := byteAddress_toNat data.requests (16*kind.tag) (by have h:=layout.requestsArena.upper; omega)
  have nNumber : (data.requests+BitVec.ofNat 64 (16*kind.tag+8)).toNat=data.requests.toNat+(16*kind.tag+8) := byteAddress_toNat data.requests (16*kind.tag+8) (by have h:=layout.requestsArena.upper; omega)
  have pFrame := current.words (data.requests+BitVec.ofNat 64 (16*kind.tag)) (by rw [pNumber]; have h:=layout.requestsLower; omega) (by rw [pNumber]; have h:=layout.requestsBefore; omega)
  have nFrame := current.words (data.requests+BitVec.ofNat 64 (16*kind.tag+8)) (by rw [nNumber]; have h:=layout.requestsLower; omega) (by rw [nNumber]; have h:=layout.requestsBefore; omega)
  exact ⟨pFrame.trans (image.requests.fields kind).1,nFrame.trans (image.requests.fields kind).2⟩

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.Description.cells_valid
#print axioms InitECandidate.Solver.Input.RequestRootHash.Description.field_read
#print axioms InitECandidate.Solver.Input.RequestRootHash.Description.current_requests
