import InitECandidate.Solver.Input.RlpWrite.BytesWriteGeneral
import InitECandidate.Solver.Input.ScalarProgram

namespace InitECandidate.Solver.Input.RlpWrite.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_encode_bytes with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)]
def oneTest : ExpHOL 64 := .cmp .equal (localVar "n") (.const 1#64)
def byteTest : ExpHOL 64 := .cmp .lower (localVar "b") (.const 128#64)
def byteBranch : ProgHOL 64 := .ite byteTest (shortForm (localVar "b")) .skip
def oneBranch : ProgHOL 64 := .dec (ofString "b") .one (.loadByte (localVar "src")) byteBranch
def firstGuard : ProgHOL 64 := .ite oneTest oneBranch .skip

theorem body_shape : body=.seq firstGuard generalTail := by
  simp only [body,Guest.guestFn_rlp_encode_bytes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    firstGuard,oneTest,oneBranch,byteBranch,byteTest,shortForm,generalTail,generalAfterHeader,localVar]

/-- The actual single-byte special case: read the source only when n=1,
write/return on a small byte, otherwise restore b and continue unchanged. -/
theorem first_guard_one (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (byte : UInt8)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be src=some byte)
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) dst)) :
    ∃ target,evaluateHOLFiniteState source firstGuard=
        (if byte.toNat<128 then (some (.returned (.val (.word 1#64))),target) else (none,source)) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory} ∧
      (∀ query,query≠panByteAlignHOL (width:=64) dst→target.memory query=source.memory query) := by
  classical
  have srcRead : eval source (localVar "src")=some (.val (.word src)) := by simp [eval,localVar,evalHOLExact,toExact,s]
  have byteRead:=Scalar.byte_read source (localVar "src") src byte srcRead loaded
  let entry:=bind source "b" (BitVec.ofNat 64 byte.toNat)
  have dEntry : entry.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other _ "b" "dst" _ (by decide)).trans d
  have bEntry : entry.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 byte.toNat))):=bind_lookup_same _ _ _
  have byteBound : byte.toNat<256:=byte.toNat_lt_size
  have byteNumber : (BitVec.ofNat 64 byte.toNat).toNat=byte.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have testRead : eval entry byteTest=some (.val (.word (if byte.toNat<128 then 1#64 else 0#64))) := by
    simp [eval,byteTest,localVar,evalHOLExact,toExact,bEntry,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,byteNumber]
  have oneRead : eval source oneTest=some (.val (.word 1#64)) := by
    simp [eval,oneTest,localVar,evalHOLExact,toExact,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at testRead oneRead
  by_cases small : byte.toNat<128
  · have read : eval entry (localVar "b")=some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by simp [eval,localVar,evalHOLExact,toExact,bEntry]
    obtain ⟨target,shortRun,frame,memory⟩:=short_form_execute entry dst (BitVec.ofNat 64 byte.toNat) (localVar "b") dEntry read mapped
    have branchRun : evaluateHOLFiniteState entry byteBranch=(some (.returned (.val (.word 1#64))),target) := by
      rw [byteBranch,evaluateHOLFiniteState_ite,testRead]
      simpa [small] using shortRun
    have declared:=ScalarScope.declare_execute source target "b" (.loadByte (localVar "src")) (BitVec.ofNat 64 byte.toNat) byteBranch _ byteRead branchRun
    change evaluateHOLFiniteState source oneBranch=(some (.returned (.val (.word 1#64))),restore source "b" target) at declared
    refine ⟨restore source "b" target,?_,?_,memory⟩
    · rw [firstGuard,evaluateHOLFiniteState_ite,oneRead]
      simpa [small] using declared
    · change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory}
      exact frame
  · have branchRun : evaluateHOLFiniteState entry byteBranch=(none,entry) := by
      rw [byteBranch,evaluateHOLFiniteState_ite,testRead]
      simp [small]
    have declared:=ScalarScope.declare_execute source entry "b" (.loadByte (localVar "src")) (BitVec.ofNat 64 byte.toNat) byteBranch none byteRead branchRun
    have normal : evaluateHOLFiniteState source oneBranch=(none,source) := by
      rw [oneBranch,declared,restore_bound]
    refine ⟨source,?_,rfl,by intros; rfl⟩
    rw [firstGuard,evaluateHOLFiniteState_ite,oneRead]
    simpa [small] using normal

end InitECandidate.Solver.Input.RlpWrite.BytesWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.body_shape
#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.first_guard_one
