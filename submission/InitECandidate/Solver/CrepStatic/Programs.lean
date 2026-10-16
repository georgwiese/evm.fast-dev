import InitECandidate.Solver.CrepStatic.Chunk0
import InitECandidate.Solver.CrepStatic.Chunk1
import InitECandidate.Solver.CrepStatic.Chunk2
import InitECandidate.Solver.CrepStatic.Chunk3
import InitECandidate.Solver.CrepStatic.Chunk4
import InitECandidate.Solver.CrepStatic.Chunk5
import InitECandidate.Solver.CrepStatic.Chunk6
import InitECandidate.Solver.CrepStatic.Chunk7
import InitECandidate.Solver.CrepStatic.Chunk8
import InitECandidate.Solver.CrepStatic.Chunk9
import InitECandidate.Solver.CrepStatic.Chunk10
import InitECandidate.Solver.CrepStatic.Chunk11
import InitECandidate.Solver.CrepStatic.Chunk12
import InitECandidate.Solver.CrepStatic.Chunk13
import InitECandidate.Solver.CrepStatic.Chunk14
import InitECandidate.Solver.CrepStatic.Chunk15
import InitECandidate.Solver.CrepStatic.Chunk16
import InitECandidate.Solver.CrepStatic.Chunk17
import InitECandidate.Solver.CrepStatic.Chunk18
import InitECandidate.Solver.CrepStatic.Chunk19
import InitECandidate.Solver.CrepStatic.Chunk20
import InitECandidate.Solver.CrepStatic.Chunk21
import InitECandidate.Solver.CrepStatic.Chunk22
import InitECandidate.Solver.CrepStatic.Chunk23
import InitECandidate.Solver.CrepStatic.Chunk24
import InitECandidate.Solver.CrepStatic.Chunk25
import InitECandidate.Solver.CrepStatic.Chunk26
import InitECandidate.Solver.CrepStatic.Chunk27
import InitECandidate.Solver.CrepStatic.Chunk28
import InitECandidate.Solver.CrepStatic.Chunk29
import InitECandidate.Solver.CrepStatic.Chunk30
import InitECandidate.Solver.CrepStatic.Chunk31
import InitECandidate.Solver.CrepStatic.Chunk32
import InitECandidate.Solver.CrepStatic.Chunk33
import InitECandidate.Solver.CrepStatic.Chunk34
import InitECandidate.Solver.CrepStatic.Chunk35
import InitECandidate.Solver.CrepStatic.Chunk36
import InitECandidate.Solver.CrepStatic.Chunk37
import InitECandidate.Solver.CrepStatic.Chunk38
import InitECandidate.Solver.CrepStatic.Chunk39
import InitECandidate.Solver.CrepStatic.Chunk40
import InitECandidate.Solver.CrepStatic.Chunk41
import InitECandidate.Solver.CrepStatic.Chunk42
import InitECandidate.Solver.CrepStatic.Chunk43
import InitECandidate.Solver.CrepStatic.Chunk44
import InitECandidate.Solver.CrepStatic.Chunk45
import InitECandidate.Solver.CrepStatic.Chunk46
import InitECandidate.Solver.CrepStatic.Chunk47
import InitECandidate.Solver.CrepStatic.Chunk48
import InitECandidate.Solver.CrepStatic.Chunk49
import InitECandidate.Solver.CrepStatic.Chunk50
import InitECandidate.Solver.CrepStatic.Chunk51

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
set_option maxRecDepth 100000

def crepProgram : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := chunk0 ++ (chunk1 ++ (chunk2 ++ (chunk3 ++ (chunk4 ++ (chunk5 ++ (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ (chunk11 ++ (chunk12 ++ (chunk13 ++ (chunk14 ++ (chunk15 ++ (chunk16 ++ (chunk17 ++ (chunk18 ++ (chunk19 ++ (chunk20 ++ (chunk21 ++ (chunk22 ++ (chunk23 ++ (chunk24 ++ (chunk25 ++ (chunk26 ++ (chunk27 ++ (chunk28 ++ (chunk29 ++ (chunk30 ++ (chunk31 ++ (chunk32 ++ (chunk33 ++ (chunk34 ++ (chunk35 ++ (chunk36 ++ (chunk37 ++ (chunk38 ++ (chunk39 ++ (chunk40 ++ (chunk41 ++ (chunk42 ++ (chunk43 ++ (chunk44 ++ (chunk45 ++ (chunk46 ++ (chunk47 ++ (chunk48 ++ (chunk49 ++ (chunk50 ++ (chunk51 ++ [])))))))))))))))))))))))))))))))))))))))))))))))))))

theorem crepProgramSafe : entriesSafe 126 crepProgram = true := by
  simp only [entriesSafe, crepProgram, List.all_append, List.all_nil,
    (show chunk0.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk0Safe), (show chunk1.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk1Safe), (show chunk2.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk2Safe), (show chunk3.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk3Safe), (show chunk4.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk4Safe), (show chunk5.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk5Safe), (show chunk6.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk6Safe), (show chunk7.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk7Safe), (show chunk8.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk8Safe), (show chunk9.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk9Safe), (show chunk10.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk10Safe), (show chunk11.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk11Safe), (show chunk12.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk12Safe), (show chunk13.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk13Safe), (show chunk14.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk14Safe), (show chunk15.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk15Safe), (show chunk16.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk16Safe), (show chunk17.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk17Safe), (show chunk18.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk18Safe), (show chunk19.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk19Safe), (show chunk20.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk20Safe), (show chunk21.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk21Safe), (show chunk22.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk22Safe), (show chunk23.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk23Safe), (show chunk24.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk24Safe), (show chunk25.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk25Safe), (show chunk26.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk26Safe), (show chunk27.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk27Safe), (show chunk28.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk28Safe), (show chunk29.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk29Safe), (show chunk30.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk30Safe), (show chunk31.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk31Safe), (show chunk32.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk32Safe), (show chunk33.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk33Safe), (show chunk34.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk34Safe), (show chunk35.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk35Safe), (show chunk36.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk36Safe), (show chunk37.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk37Safe), (show chunk38.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk38Safe), (show chunk39.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk39Safe), (show chunk40.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk40Safe), (show chunk41.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk41Safe), (show chunk42.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk42Safe), (show chunk43.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk43Safe), (show chunk44.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk44Safe), (show chunk45.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk45Safe), (show chunk46.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk46Safe), (show chunk47.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk47Safe), (show chunk48.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk48Safe), (show chunk49.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk49Safe), (show chunk50.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk50Safe), (show chunk51.all (fun entry => decide (ceiling entry.2.2 ≤ 126)) = true from chunk51Safe), Bool.and_true]

theorem crepCodeSafe : CodeSafe 126 (alistToFmapCodeExact crepProgram) :=
  entriesSafe_codeSafe 126 crepProgram crepProgramSafe

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.crepProgramSafe
#print axioms InitECandidate.Solver.CrepStatic.crepCodeSafe
