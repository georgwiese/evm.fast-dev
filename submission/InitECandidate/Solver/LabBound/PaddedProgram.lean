import InitECandidate.Solver.LabBound.Padded.Chunk0
import InitECandidate.Solver.LabBound.Padded.Chunk1
import InitECandidate.Solver.LabBound.Padded.Chunk2
import InitECandidate.Solver.LabBound.Padded.Chunk3
import InitECandidate.Solver.LabBound.Padded.Chunk4
import InitECandidate.Solver.LabBound.Padded.Chunk5
import InitECandidate.Solver.LabBound.Padded.Chunk6
import InitECandidate.Solver.LabBound.Padded.Chunk7
import InitECandidate.Solver.LabBound.Padded.Chunk8
import InitECandidate.Solver.LabBound.Padded.Chunk9
import InitECandidate.Solver.LabBound.Padded.Chunk10
import InitECandidate.Solver.LabBound.Padded.Chunk11
import InitECandidate.Solver.LabBound.Padded.Chunk12
import InitECandidate.Solver.LabBound.Padded.Chunk13
import InitECandidate.Solver.LabBound.Padded.Chunk14
import InitECandidate.Solver.LabBound.Padded.Chunk15
import InitECandidate.Solver.LabBound.Padded.Chunk16
import InitECandidate.Solver.LabBound.Padded.Chunk17
import InitECandidate.Solver.LabBound.Padded.Chunk18
import InitECandidate.Solver.LabBound.Padded.Chunk19
import InitECandidate.Solver.LabBound.Padded.Chunk20
import InitECandidate.Solver.LabBound.Padded.Chunk21
import InitECandidate.Solver.LabBound.Padded.Chunk22
import InitECandidate.Solver.LabBound.Padded.Chunk23
import InitECandidate.Solver.LabBound.Padded.Chunk24
import InitECandidate.Solver.LabBound.Padded.Chunk25
import InitECandidate.Solver.LabBound.Padded.Chunk26
import InitECandidate.Solver.LabBound.Padded.Chunk27
import InitECandidate.Solver.LabBound.Padded.Chunk28
import InitECandidate.Solver.LabBound.Padded.Chunk29
import InitECandidate.Solver.LabBound.Padded.Chunk30
import InitECandidate.Solver.LabBound.Padded.Chunk31
import InitECandidate.Solver.LabBound.Padded.Chunk32
import InitECandidate.Solver.LabBound.Padded.Chunk33
import InitECandidate.Solver.LabBound.Padded.Chunk34
import InitECandidate.Solver.LabBound.Padded.Chunk35
import InitECandidate.Solver.LabBound.Padded.Chunk36
import InitECandidate.Solver.LabBound.Padded.Chunk37
import InitECandidate.Solver.LabBound.Padded.Chunk38
import InitECandidate.Solver.LabBound.Padded.Chunk39
import InitECandidate.Solver.LabBound.Padded.Chunk40
import InitECandidate.Solver.LabBound.Padded.Chunk41
import InitECandidate.Solver.LabBound.Padded.Chunk42
import InitECandidate.Solver.LabBound.Padded.Chunk43
import InitECandidate.Solver.LabBound.Padded.Chunk44
import InitECandidate.Solver.LabBound.Padded.Chunk45
import InitECandidate.Solver.LabBound.Padded.Chunk46
import InitECandidate.Solver.LabBound.Padded.Chunk47
import InitECandidate.Solver.LabBound.Padded.Chunk48
import InitECandidate.Solver.LabBound.Padded.Chunk49
import InitECandidate.Solver.LabBound.Padded.Chunk50
import InitECandidate.Solver.LabBound.Padded.Chunk51
import InitECandidate.Solver.LabBound.Padded.Chunk52
import InitECandidate.Solver.LabBound.Padded.Chunk53

/-! Layout facts for the fixed padded sections, in exactly the metadata's order.
This list avoids the unrelated FFI/shmem proofs imported by Metadata.LiteralFacts.
The generator copies its append tree; equality to that named metadata declaration
is left to the later artifact integration, not assumed by this theorem. -/
namespace InitECandidate.Solver.LabBound
open Flapjack.Compiler.Backend
set_option maxRecDepth 10000

def fixedPaddedProgram : LabSem.LabProgHOL 64 := paddedChunk0 ++ (paddedChunk1 ++ (paddedChunk2 ++ (paddedChunk3 ++ (paddedChunk4 ++ (paddedChunk5 ++ (paddedChunk6 ++ (paddedChunk7 ++ (paddedChunk8 ++ (paddedChunk9 ++ (paddedChunk10 ++ (paddedChunk11 ++ (paddedChunk12 ++ (paddedChunk13 ++ (paddedChunk14 ++ (paddedChunk15 ++ (paddedChunk16 ++ (paddedChunk17 ++ (paddedChunk18 ++ (paddedChunk19 ++ (paddedChunk20 ++ (paddedChunk21 ++ (paddedChunk22 ++ (paddedChunk23 ++ (paddedChunk24 ++ (paddedChunk25 ++ (paddedChunk26 ++ (paddedChunk27 ++ (paddedChunk28 ++ (paddedChunk29 ++ (paddedChunk30 ++ (paddedChunk31 ++ (paddedChunk32 ++ (paddedChunk33 ++ (paddedChunk34 ++ (paddedChunk35 ++ (paddedChunk36 ++ (paddedChunk37 ++ (paddedChunk38 ++ (paddedChunk39 ++ (paddedChunk40 ++ (paddedChunk41 ++ (paddedChunk42 ++ (paddedChunk43 ++ (paddedChunk44 ++ (paddedChunk45 ++ (paddedChunk46 ++ (paddedChunk47 ++ (paddedChunk48 ++ (paddedChunk49 ++ (paddedChunk50 ++ (paddedChunk51 ++ (paddedChunk52 ++ paddedChunk53))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem fixedPaddedProgram_fits : fixedPaddedProgram.all (sectionFits 24) = true := by
  simp only [fixedPaddedProgram, List.all_append, paddedChunk0_fits,
    paddedChunk1_fits,
    paddedChunk2_fits,
    paddedChunk3_fits,
    paddedChunk4_fits,
    paddedChunk5_fits,
    paddedChunk6_fits,
    paddedChunk7_fits,
    paddedChunk8_fits,
    paddedChunk9_fits,
    paddedChunk10_fits,
    paddedChunk11_fits,
    paddedChunk12_fits,
    paddedChunk13_fits,
    paddedChunk14_fits,
    paddedChunk15_fits,
    paddedChunk16_fits,
    paddedChunk17_fits,
    paddedChunk18_fits,
    paddedChunk19_fits,
    paddedChunk20_fits,
    paddedChunk21_fits,
    paddedChunk22_fits,
    paddedChunk23_fits,
    paddedChunk24_fits,
    paddedChunk25_fits,
    paddedChunk26_fits,
    paddedChunk27_fits,
    paddedChunk28_fits,
    paddedChunk29_fits,
    paddedChunk30_fits,
    paddedChunk31_fits,
    paddedChunk32_fits,
    paddedChunk33_fits,
    paddedChunk34_fits,
    paddedChunk35_fits,
    paddedChunk36_fits,
    paddedChunk37_fits,
    paddedChunk38_fits,
    paddedChunk39_fits,
    paddedChunk40_fits,
    paddedChunk41_fits,
    paddedChunk42_fits,
    paddedChunk43_fits,
    paddedChunk44_fits,
    paddedChunk45_fits,
    paddedChunk46_fits,
    paddedChunk47_fits,
    paddedChunk48_fits,
    paddedChunk49_fits,
    paddedChunk50_fits,
    paddedChunk51_fits,
    paddedChunk52_fits,
    paddedChunk53_fits, Bool.and_self]

theorem fixedPaddedProgram_layout :
    LineBound fixedPaddedProgram 24 ∧ NoInstall fixedPaddedProgram :=
  programFits_spec 24 fixedPaddedProgram fixedPaddedProgram_fits

end InitECandidate.Solver.LabBound
#print axioms InitECandidate.Solver.LabBound.fixedPaddedProgram_fits
#print axioms InitECandidate.Solver.LabBound.fixedPaddedProgram_layout
