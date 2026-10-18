#!/usr/bin/env python3
"""Untrusted original dispatcher proof-data generator; Lean checks body_shape.

Refuses to overwrite a file. Use --output for reproducibility checks.
"""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[2]
text = (root/'Guest/guest.pp.pnk').read_text()
part = text.split('fun 1 op_dispatch(1 op) {', 1)[1].split('\nfun 1 frame_open', 1)[0]
pattern = re.compile(r'\s*(<\+|==|[A-Za-z_][A-Za-z_0-9]*|\d+|[{}();,\-])')
tokens=[]; position=0
while position<len(part):
 match=pattern.match(part,position)
 if not match:
  assert not part[position:].strip(),part[position:position+80]
  break
 tokens.append(match.group(1));position=match.end()
i=0

def take(expected=None):
 global i
 token=tokens[i];i+=1
 if expected is not None:assert token==expected,(i,token,expected)
 return token

def expression():
 token=take()
 if token.isdigit():return f'.const (BitVec.ofNat 64 {token})'
 assert token=='op',token
 take('-');bound=take();assert bound.isdigit()
 return f'.op .sub [localVar "op", .const (BitVec.ofNat 64 {bound})]'

def block(opened=False):
 if not opened:take('{')
 statements=[]
 while tokens[i]!='}':
  token=take()
  if token=='if':
   take('op');cmp=take();assert cmp in ('<+','==')
   bound=take();assert bound.isdigit()
   yes=block();no=('action','skip')
   if i<len(tokens) and tokens[i]=='else':take('else');no=block()
   statements.append(('branch','lower' if cmp=='<+' else 'equal',bound,yes,no))
  elif token=='return':take('0');take(';');statements.append(('action','returned'))
  elif token=='throw':take('EvmErr');take('5');take(';');statements.append(('action','failed'))
  else:
   assert token.startswith('op_'),token
   take('(');arguments=[]
   if tokens[i]!=')':
    arguments.append(expression())
    while tokens[i]==',':take(',');arguments.append(expression())
   take(')');take(';');statements.append(('call',token,arguments))
 take('}')
 return sequence(statements)

def sequence(statements):
 if not statements:return ('action','skip')
 last=statements[-1]
 assert last[0]!='call',last
 result=last
 for left in reversed(statements[:-1]):
  if left[0]=='call':
   assert result==('action','returned'),(left,result)
   result=('invoke',left[1],left[2])
  else:result=('seq',left,result)
 return result

def render(node,indent=0):
 kind=node[0]
 if kind=='action':return f'.action .{node[1]}'
 if kind=='invoke':return f'.action (.invoke "{node[1]}" [{", ".join(node[2])}])'
 pad=' '*(indent+2)
 if kind=='branch':return f'.branch (.{node[1]} {node[2]})\n{pad}({render(node[3],indent+2)})\n{pad}({render(node[4],indent+2)})'
 assert kind=='seq',kind
 return f'.seq\n{pad}({render(node[1],indent+2)})\n{pad}({render(node[2],indent+2)})'

tree=block(opened=True);assert i==len(tokens),(i,len(tokens))
import argparse
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=root/'submission/InitECandidate/Solver/GasBudget/DispatchProgram.lean')
output = parser.parse_args().output
assert not output.exists()
output.write_text('''import InitECandidate.Solver.GasBudget.DispatchSyntax

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Literal proof description of the unchanged dispatcher. Its equality to
Guest.guestFn_op_dispatch is checked below; the text parser is untrusted. -/
def tree : Syntax :=
  '''+render(tree,2)+'''

def body : ProgHOL 64 := match Guest.guestFn_op_dispatch with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "op", .one)]

theorem body_shape : body = tree.program := by
  simp only [body, Guest.guestFn_op_dispatch, progToHOL, expToHOL,
    List.map_cons, List.map_nil, Option.map_none, tree, Syntax.program, Action.program, Guard.expression, localVar]

theorem body_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op))) :
    evaluateHOLFiniteState source body = evaluateHOLFiniteState source (tree.choose op).program := by
  rw [body_shape]
  exact tree.choose_execution source op opLocal

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.body_shape
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.body_choice
''')
print({'tokens':len(tokens),'output_lines':len(output.read_text().splitlines()),'bytes':output.stat().st_size})
