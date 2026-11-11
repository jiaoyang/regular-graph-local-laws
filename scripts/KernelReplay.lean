import LocalLaw.Audit
import SpectralConsequences.Audit
import Lean.Replay

set_option maxHeartbeats 0

/-! Verification program, executed afresh by `check.sh --kernel`.
Lean's official Environment.replay sends every safe project declaration
back through the kernel (addDeclCore with trust level zero), starting from
an environment importing only Mathlib and Lean.Replay. Module-origin metadata
includes private declarations and declarations in other namespaces.
-/
open Lean in
run_cmd do
  let source ← getEnv
  let projectModule (n : Name) :=
    (`LocalLaw).isPrefixOf n || (`SpectralConsequences).isPrefixOf n
  let modules := source.header.moduleNames.filter projectModule
  if modules.size != 1371 then
    throwError "Expected all 1371 project modules, imported {modules.size}"
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let mut byModule : Std.HashMap Name (Std.HashMap Name ConstantInfo) := {}
  for (name, info) in source.constants.toList do
    if let some idx := source.getModuleIdxFor? name then
      let moduleName := source.header.moduleNames[idx.toNat]!
      if projectModule moduleName then
        declarations := declarations.insert name info
        let members := (byModule[moduleName]?).getD {}
        byModule := byModule.insert moduleName (members.insert name info)
  let safe := declarations.toList.countP (fun (_, info) => !info.isUnsafe && !info.isPartial)
  let skipped := declarations.size - safe
  if safe == 0 then
    throwError "No project declarations selected for kernel replay"
  let required : Array Name := #[`SpectralConsequences.full_paper_theorem_1_2,
    `SpectralConsequences.full_paper_theorem_1_4,
    `SpectralConsequences.paperOmega_eq_finiteOmega,
    `SpectralConsequences.source_actual_high_moment_bounds,
    `LocalLaw.source_theorem_4_2]
  for name in required do
    unless declarations.contains name do
      throwError "Missing required project proof {name}"
  logInfo m!"Kernel replay: {modules.size} project modules; {safe} safe declarations; {skipped} unsafe/partial implementation declarations skipped by Lean.Replay."
  let base ← liftM <| importModules #[{module := `Mathlib}, {module := `Lean.Replay}] {} 0
  for (name, _) in declarations.toList do
    if base.contains name then
      throwError "Base environment already contains project declaration {name}"
  let mut checked := base
  -- Imported module order is dependency order. Reset only elaboration's async
  -- private-name trie at module boundaries, keeping the complete checked
  -- kernel environment. This avoids Lean4.19's cross-module private-name
  -- normalization collisions; every declaration is still kernel checked.
  for moduleName in modules do
    let members := (byModule[moduleName]?).getD {}
    let clean := Environment.ofKernelEnv checked.toKernelEnv
    checked ← liftM <| Environment.replay members clean
    for (name, info) in members.toList do
      if !info.isUnsafe && !info.isPartial then
        if (checked.toKernelEnv.find? name).isNone then
          throwError "Kernel environment missing {name} immediately after replay of {moduleName} ({members.size} declarations)"
  if checked.header.trustLevel != 0 then
    throwError "Kernel replay environment unexpectedly has nonzero trust level"
  for name in required do
    if (checked.toKernelEnv.find? name).isNone then
      throwError "Required proof {name} was not replayed"
  logInfo m!"PASSED: every safe declaration from all {modules.size} project modules replayed through the Lean kernel at trust level zero."
