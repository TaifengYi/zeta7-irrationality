import Solution
import Lean

/-! Local surrogate of Comparator's declaration-closure comparison (run with
`lake env lean palomar_local_check/DumpSolution.lean`). Starting from the compared theorem names,
it walks the used-constant graph exactly as `Compare.loop` does: named theorems are compared by
kind and type only, every other reached declaration by kind, universe parameters, type and value.
It writes one line per reached constant to `palomar_local_check/solution_closure.txt`; the
Challenge and Solution files must be identical. It also prints the Solution-side axioms. -/

open Lean Elab Command

def roots : List Name := [`Zeta7Challenge.approximant_tendsto,
  `Zeta7Challenge.zeta7Three_irrational, `Zeta7Challenge.eta_irrational]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut work : Array Name := roots.toArray
  let mut lines : Array String := #[]
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "missing constant {n}"
    let named := roots.contains n
    let v : Option Expr := if named then none else ci.value? (allowOpaque := true)
    lines := lines.push s!"{n} {kindOf ci} {ci.levelParams} {hash ci.type} {(v.map hash).getD 0}"
    for c in ci.type.getUsedConstants do work := work.push c
    if let some e := v then
      for c in e.getUsedConstants do work := work.push c
    if let .inductInfo i := ci then
      for c in i.ctors do work := work.push c
    if let .ctorInfo c := ci then work := work.push c.induct
  let sorted := lines.qsort (· < ·)
  IO.FS.writeFile "palomar_local_check/solution_closure.txt" (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"CLOSURE Solution: {sorted.size} constants"
  for r in roots do
    let axs ← Lean.collectAxioms r
    logInfo m!"AXIOMS Solution {r}: {axs.toList}"
