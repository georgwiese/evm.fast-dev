import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.ScalarDeclaration
import InitECandidate.Solver.WitnessRadix.AllocatedArena

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_pack_bytes with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "n",.one)]
def returnShape : ShapeHOL := .comb [.one,.one]
def afterCount : ProgHOL 64 := match body with | .dec _ _ _ tail=>tail | _=>.skip
def afterBuffer : ProgHOL 64 := match afterCount with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterCopy : ProgHOL 64 := match afterBuffer with | .seq _ tail=>tail | _=>.skip

def countExpression : ExpHOL 64 := .shift .lsr (.op .add [localVar "n",.const 31#64]) (.const 5#64)
def amountExpression : ExpHOL 64 := .panop .mul [localVar "count",.const 32#64]
def copyArguments : List (ExpHOL 64) := [localVar "buf",localVar "p",localVar "n"]
def zeroArguments : List (ExpHOL 64) := [.op .add [localVar "buf",localVar "n"],.op .sub [amountExpression,localVar "n"]]

def chunks (n : Nat) := (n+31)/32
def padded (n : Nat) := 32*chunks n

theorem padding_bounds (n : Nat) : n≤padded n ∧ padded n<n+32 ∧ padded n%32=0 ∧ padded n-n≤31 := by
  unfold padded chunks
  omega

set_option maxRecDepth 100000 in
theorem body_shape : body=.dec (ofString "count") .one countExpression afterCount ∧
    afterCount=.decCall (ofString "buf") .one (ofString "alloc") [amountExpression] afterBuffer ∧
    afterBuffer=.seq (.call (some (none,none)) (ofString "memcpy") copyArguments) afterCopy ∧
    afterCopy=.seq (.call (some (none,none)) (ofString "memzero") zeroArguments) (.return (.rstruct [localVar "buf",localVar "count"])) := by
  simp only [body,afterCount,afterBuffer,afterCopy,Guest.Software.guestFn_pack_bytes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    countExpression,amountExpression,copyArguments,zeroArguments,localVar,Option.map_none]
  exact ⟨True.intro,True.intro,True.intro,True.intro⟩

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "pack_bytes")=some (formals,body,returnShape) := by
  have checked := CurrentHash.Code.installed code installed .pack_bytes
  simpa only [CurrentHash.Code.name, CurrentHash.Code.formals, CurrentHash.Code.body, CurrentHash.Code.shape,
    CurrentHash.Code.entry, CurrentHash.Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,returnShape,Guest.Software.guestFn_pack_bytes,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem count_read_bounded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat) (small : n+31<2^64)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
    eval source countExpression=some (.val (.word (BitVec.ofNat 64 (chunks n)))) := by
  have number : (BitVec.ofNat 64 (n+31)).toNat=n+31 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have shift : (BitVec.ofNat 64 (n+31) >>> (5:Nat))=BitVec.ofNat 64 (chunks n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,number,chunks,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
    omega
  simp [eval,countExpression,localVar,evalHOLExact,evalListHOLExact,toExact,count,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,←BitVec.ofNat_add,shift]

/-- Historical small-input API is a projection of the actual word bound. -/
theorem count_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat) (small : n≤134217728)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
    eval source countExpression=some (.val (.word (BitVec.ofNat 64 (chunks n)))) :=
  count_read_bounded source n (by omega) count

/-- The actual padding tail is inside the allocated count*32 arena; an
aligned tail has word-multiple length, while every tail is at most31bytes. -/
theorem padding_geometry (cursor : BitVec 64) (n : Nat) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0) :
    AllocatedBytes.Arena (cursor+BitVec.ofNat 64 n) (padded n-n) ∧
    (cursor+BitVec.ofNat 64 n).toNat=cursor.toNat+n ∧
    ((cursor+BitVec.ofNat 64 n).toNat%8=0 → (padded n-n)%8=0) := by
  have bounds := padding_bounds n
  have upper := arena.upper
  have address : (cursor+BitVec.ofNat 64 n).toNat=cursor.toNat+n := byteAddress_toNat cursor n (by omega)
  refine ⟨AllocatedBytes.Arena.subrange cursor (padded n) n (padded n-n) arena (by omega),address,?_⟩
  intro tailAligned
  have multiple : padded n%8=0 := by have h:=bounds.2.2.1; omega
  rw [address] at tailAligned
  omega

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.padding_bounds
#print axioms InitECandidate.Solver.Input.PackBytes.body_shape
#print axioms InitECandidate.Solver.Input.PackBytes.original_code
#print axioms InitECandidate.Solver.Input.PackBytes.count_read
#print axioms InitECandidate.Solver.Input.PackBytes.padding_geometry

#print axioms InitECandidate.Solver.Input.PackBytes.count_read_bounded
