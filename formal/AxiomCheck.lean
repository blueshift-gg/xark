import Formal

/-!
The axiom check CI runs after `lake build` (`lake env lean AxiomCheck.lean`).

1. Every harness `templates/<gadget>/` needs its proof: `Xark.Templates.<Gadget>.soundness`,
   whose statement mentions `Xark.Templates.<Gadget>.template` and `Template.Sat`, and,
   when `Formal/Templates/Consts/<Gadget>.lean` exists, that module in `Formal` (the
   obligations of its production calls' constant plugs). The mention check is syntactic:
   it catches a theorem about the wrong object, not a vacuous one (an unsatisfiable
   `Assumptions`, or a `Spec` that is `True`); statements are reviewed by hand.
2. Every declaration of every `Formal.*` module may depend only on `propext`,
   `Classical.choice` and `Quot.sound`: no `sorryAx`, no declared `axiom`, no
   `native_decide`.

It prints every theorem it checked, one per line, after `checked:`.
-/

open Lean Elab Command

/-- `xtask`'s `camel`: `to_bits__106` ↦ `ToBits106`. -/
def camel (s : String) : String :=
  String.join <| (s.splitOn "_").map String.capitalize

def standard : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut errors : Array String := #[]
  let mut harnesses := #[]
  for e in ← System.FilePath.readDir "templates" do
    if ← e.path.isDir then harnesses := harnesses.push e.fileName
  if harnesses.isEmpty then errors := errors.push "no harness under templates/"
  for h in harnesses.qsort (· < ·) do
    let m := camel h
    let n := Name.mkStr4 "Xark" "Templates" m "soundness"
    -- About this harness's rows: its statement reads `template` and `Template.Sat`.
    let about := [Name.mkStr4 "Xark" "Templates" m "template", ``Xark.Template.Template.Sat]
    match env.find? n with
    | none => errors := errors.push s!"{h}: no theorem {n}"
    | some c =>
      let used := c.type.getUsedConstants
      unless about.all used.contains do
        errors := errors.push s!"{h}: {n}'s statement doesn't mention {about}"
    let consts := Name.mkStr3 "Formal" "Templates" "Consts" |>.str m
    if ← System.FilePath.pathExists s!"Formal/Templates/Consts/{m}.lean" then
      unless (env.getModuleIdx? consts).isSome do
        errors := errors.push s!"{h}: {consts} is not imported by Formal.lean"
  let mut checked := #[]
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless (`Formal).isPrefixOf mod do continue
    for c in data.constNames do
      let axioms ← collectAxioms c
      let bad := axioms.filter (!standard.contains ·)
      unless bad.isEmpty do errors := errors.push s!"{c} ({mod}) depends on {bad.toList}"
      if (env.find? c).any (·.isThm) && !c.isInternalDetail then checked := checked.push c
  logInfo m!"checked:\n{"\n".intercalate (checked.qsort Name.lt |>.map toString).toList}"
  unless errors.isEmpty do
    throwError "axiom check failed:\n{"\n".intercalate errors.toList}"
  logInfo m!"{checked.size} theorems in {harnesses.size} harnesses' proofs and the rest of \
    Formal: standard axioms only"
