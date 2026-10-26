import QuantumFoundations

/-!
Fails when a declaration of the `QuantumFoundations` modules depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`.
-/

open Lean Elab Command in
elab "#check_standard_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`QuantumFoundations).isPrefixOf mod do continue
    let axs ← liftCoreM <| collectAxioms n
    for a in axs do
      unless allowed.contains a do bad := bad.push (n, a)
  if bad.isEmpty then
    logInfo "standard axioms only"
  else
    throwError m!"non-standard axioms: {bad.toList}"

#check_standard_axioms
