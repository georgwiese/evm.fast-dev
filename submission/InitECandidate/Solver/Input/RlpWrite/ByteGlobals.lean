import InitECandidate.Solver.Input.OriginalRlpCodes
import InitECandidate.Solver.Input.BufferGlobals

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem RlpLength.Be.globals (key : MlS) (code) : GlobalEffects.Preserves key code RlpLength.Be.body := by
  simp only [RlpLength.Be.body,Guest.guestFn_rlp_be_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat' first
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.returned key code _

theorem RlpWrite.PutBe.globals (key : MlS) (code) : GlobalEffects.Preserves key code RlpWrite.PutBe.body := by
  simp only [RlpWrite.PutBe.body,Guest.guestFn_rlp_put_be,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat' first
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.store_byte key code _ _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.returned key code _

theorem RlpWrite.HeaderWrite.globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code RlpWrite.HeaderWrite.body := by
  simp only [RlpWrite.HeaderWrite.body,Guest.guestFn_rlp_write_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | exact GlobalEffects.store_byte key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | apply GlobalEffects.scoped_body key code _ _ (ofString "rlp_be_len") _ _ RlpLength.Be.formals RlpLength.Be.body .one
        (OriginalRlp.rlp_be_len code installed) (RlpLength.Be.globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "rlp_put_be") _ RlpWrite.PutBe.formals RlpWrite.PutBe.body .one
        (OriginalRlp.rlp_put_be code installed) (RlpWrite.PutBe.globals key code)

theorem RlpWrite.BytesWrite.globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code RlpWrite.BytesWrite.body := by
  simp only [RlpWrite.BytesWrite.body,Guest.guestFn_rlp_encode_bytes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | exact GlobalEffects.store_byte key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | apply GlobalEffects.scoped_body key code _ _ (ofString "rlp_write_header") _ _ RlpWrite.HeaderWrite.formals RlpWrite.HeaderWrite.body .one
        (OriginalRlp.rlp_write_header code installed) (RlpWrite.HeaderWrite.globals key code installed)
    | exact GlobalEffects.call_body key code (some none) (ofString "memcpy") _ WitnessRadix.CopyGeneral.formals WitnessRadix.Copy32.body .one
        (WitnessRadix.CopyGeneral.original_code code installed) (WitnessRadix.Copy32.globals key code)

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.RlpLength.Be.globals
#print axioms InitECandidate.Solver.Input.RlpWrite.PutBe.globals
#print axioms InitECandidate.Solver.Input.RlpWrite.HeaderWrite.globals
#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.globals
