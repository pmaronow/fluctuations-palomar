module

import all Solution
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted := [``propext, ``Quot.sound, ``Classical.choice]
  let roots := [
    ``LowerUpperBounds.theorem_1_1,
    ``LowerUpperBounds.corollary_1_2,
    ``LowerUpperBounds.theorem_1_3,
    ``LowerUpperBounds.theorem_1_6,
    ``LowerUpperBounds.corollary_1_7]
  for name in roots do
    let some info := env.find? name | throwError "missing Comparator export {name}"
    unless info.isTheorem do
      throwError "Comparator export is not a theorem: {name}"
    let axioms ← collectAxioms name
    for axName in axioms do
      unless permitted.contains axName do
        throwError "forbidden axiom {axName} in {name}"
    logInfo m!"Comparator export {name}: {axioms}"
  let mut count := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "LowerUpperBounds." then
      count := count + 1
      unless roots.contains name do
        throwError "unexpected manuscript export {name}"
  unless count == roots.length do
    throwError "expected exactly five manuscript exports, found {count}"
  logInfo m!"Audited {roots.length} manuscript exports; only the three standard axioms."
