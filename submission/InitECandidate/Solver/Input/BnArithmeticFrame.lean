import InitECandidate.Solver.Input.BnModmulProgram
import InitECandidate.Solver.Input.WordArrayWriteFrame

namespace InitECandidate.Solver.Input.BnArithmetic
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real arithmetic reply preserves every input byte before its result. -/
theorem prefix_byte (words : List Guest.Word) (length : words.length = 20) (offset : Nat) (inside : offset < 128) :
    (WordArrayCodec.bits (output words))[offset]'(by rw [WordArrayCodec.length,output_length words length]; omega) =
      (WordArrayCodec.bits words)[offset]'(by rw [WordArrayCodec.length,length]; omega) := by
  rw [WordArrayRead.packed_byte (output words) offset (by rw [output_length words length]; omega),
    WordArrayRead.packed_byte words offset (by rw [length]; omega)]
  have early : offset / 8 < (words.take 16).length := by simp only [List.length_take,length]; omega
  have same : (output words)[offset / 8]'(by rw [output_length words length]; omega) = words[offset / 8]'(by rw [length]; omega) := by
    simp only [output,List.getElem_append_left early,List.getElem_take]
  rw [same]

noncomputable def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : List Guest.Word) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {source with
    memory := @panWriteBytearrayWord8HOL 64 _ pointer (WordArrayCodec.bits (output words)) source.memory source.memaddrs
      (fun query => Classical.propDecidable (source.memaddrs query)) source.be
    ffi := nextFfi source.ffi words}

/-- The literal original external call uses its real byte-array read and the
fixed oracle, retaining the resulting memory and actual event append. -/
theorem external_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : List Guest.Word)
    (binding : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word pointer)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle) (length : words.length = 20) (nonzero : modulusOf words ≠ 0)
    (read : readBytearrayWordHOL (byteWidth := 8) pointer 160
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun query => Classical.propDecidable (source.memaddrs query)) source.be) = some (WordArrayCodec.bits words)) :
    evaluateHOLFiniteState source BnModmul.external = (none,post source pointer words) := by
  have ffiRun := call_ffi source.ffi words oracleEq length nonzero
  have emptyRead : readBytearrayWordHOL (byteWidth := 8) pointer 0
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun query => Classical.propDecidable (source.memaddrs query)) source.be) = some [] := rfl
  rw [BnModmul.external,evaluateHOLFiniteState_extCall_source]
  simp only [evalHOLFinite,evalHOLExact,toExact,binding]
  simp only [show (0#64 : BitVec 64).toNat = 0 from rfl,show (160#64 : BitVec 64).toNat = 160 from rfl,emptyRead,read,ffiRun]
  change (none,ofExact (post source pointer words).toExact (post source pointer words).toExact_finiteSupport) = _
  rw [ofExact_toExact]

/-- The zero and modulus words lie before the result. Their preservation is
derived from the actual packed input and reply bytes, not supplied afterward. -/
theorem prefix_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : List Guest.Word)
    (length : words.length = 20) (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 160 < 2 ^ 64) (little : source.be = false)
    (mapped : ∀ index : Fin words.length,source.memaddrs (byteAddress pointer (8 * index.val)))
    (stored : ∀ index : Fin words.length,source.memory (byteAddress pointer (8 * index.val)) = .word (words[index.val]))
    (offset : Nat) (inside : offset < 128) :
    (post source pointer words).memory (byteAddress pointer offset) = source.memory (byteAddress pointer offset) := by
  apply WordArrayWriteFrame.same_word source pointer (byteAddress pointer offset) (WordArrayCodec.bits (output words))
  intro byte byteInside hit
  have bound : byte < 160 := by rw [WordArrayCodec.length,output_length words length] at byteInside; exact byteInside
  have cell := ByteArray.aligned_cell pointer byte 160 bound aligned fits
  have numbers := congrArg BitVec.toNat (cell.symm.trans hit)
  rw [byteAddress_toNat pointer (8 * (byte / 8)) (by omega),byteAddress_toNat pointer offset (by omega)] at numbers
  have early : byte < 128 := by omega
  have actual := WordArrayRead.read_byte source pointer words aligned (by rw [length]; exact fits) little mapped stored byte (by rw [length]; omega)
  exact actual.trans (congrArg some (prefix_byte words length byte early).symm)

theorem post_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (words : List Guest.Word)
    (length : words.length = 20)
    (away : ∀ offset < 160,query ≠ panByteAlignHOL (width := 64) (byteAddress pointer offset)) :
    (post source pointer words).memory query = source.memory query := by
  apply ByteArray.write_away source pointer query (WordArrayCodec.bits (output words))
  intro offset inside
  apply away offset
  rw [WordArrayCodec.length,output_length words length] at inside
  exact inside

end InitECandidate.Solver.Input.BnArithmetic

#print axioms InitECandidate.Solver.Input.BnArithmetic.prefix_byte
#print axioms InitECandidate.Solver.Input.BnArithmetic.external_execute
#print axioms InitECandidate.Solver.Input.BnArithmetic.prefix_memory
#print axioms InitECandidate.Solver.Input.BnArithmetic.post_away
