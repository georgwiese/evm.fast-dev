import InitECandidate.Solver.Input.MainDecoderProgram
import InitECandidate.Solver.Input.HeaderEntry

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def program : ProgHOL 64 := match DecoderSetup.decoder with | .seq first _ => first | _ => .skip
def continuation : ProgHOL 64 := match DecoderSetup.decoder with | .seq _ rest => rest | _ => .skip
def handler : ProgHOL 64 := match program with | .call (some (_,some (_,_,body))) _ _ => body | _ => .skip
def arguments : List (ExpHOL 64) := [.rfield 0 (.var .local (ofString "inp")),.rfield 1 (.var .local (ofString "inp"))]
def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "len",.one)]
def values (pointer : BitVec 64) (length : Nat) : List (ValueHOL 64) := [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))]
def rawLocals (pointer : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "len" then some (.val (.word (BitVec.ofNat 64 length))) else if name = ofString "p" then some (.val (.word pointer)) else none

theorem original_shape : DecoderSetup.decoder = .seq
    (.call (some (some (.local,ofString "si"),some (ofString "SszErr",ofString "err_code",handler))) (ofString "decode_stateless_input") arguments) continuation := by
  simp only [program,continuation,handler,arguments,DecoderSetup.decoder,DecoderSetup.afterZeroAllocation,DecoderSetup.afterOutAllocation,
    afterInput,afterFork,afterEvm,afterHeader,afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,Main.body,
    Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (binding : source.locals.lookup (ofString "inp") = some (Blob.pair pointer length)) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values pointer length) := by
  simp [arguments,values,evalListHOLFinite,evalListHOLExact,evalHOLExact,binding,Blob.pair]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_stateless_input") = some (formals,Header.body,.one) := by
  have checked := OriginalCode.indexed code installed 192 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_decode_stateless_input) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,Header.body,Guest.guestFn_decode_stateless_input,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem original_fail_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one) := by
  have checked := OriginalCode.indexed code installed 185 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_ssz_fail) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,SszFail.formals,SszFail.body,Guest.guestFn_ssz_fail,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem original_offsets_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ssz_check_offsets") = some (Offsets.formals,Offsets.body,.one) := by
  have checked := OriginalCode.indexed code installed 186 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_ssz_check_offsets) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Offsets.formals,Offsets.body,Guest.guestFn_ssz_check_offsets,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (pointer : BitVec 64) (length : Nat)
    (known : codeFn (ofString "decode_stateless_input") = some (formals,Header.body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "decode_stateless_input") (values pointer length) = some (Header.body,callee,.one) ∧
      callee.lookup (ofString "p") = some (.val (.word pointer)) ∧ callee.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values pointer length).length ∧
      ((formals.zip (values pointer length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "decode_stateless_input") (values pointer length) = some (Header.body,rawLocals pointer length,.one) := by
    simp only [lookupCodeHOLExact,known,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ Header.body _ .one raw
  refine ⟨callee,called,?_,?_⟩
  · rw [locals]
    simp [rawLocals,show ofString "p" ≠ ofString "len" from by decide]
  · rw [locals]
    simp [rawLocals]

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.original_shape
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.arguments_read
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.original_code
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.original_fail_code
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.original_offsets_code
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.environment
