import Formal

/-!
The axiom check CI runs after `lake build` (`lake env lean AxiomCheck.lean`).

1. Every harness `templates/<gadget>/` needs its proof: `Xark.Templates.<Gadget>.soundness`,
   whose statement mentions `Xark.Templates.<Gadget>.template` and `Template.Sat`, and,
   when `Formal/Templates/Consts/<Gadget>.lean` exists, that module in `Formal` (the
   obligations of its production calls' constant plugs). The mention check is syntactic:
   it catches a theorem about the wrong object. Against a vacuous one, it also needs
   `Xark.Templates.<Gadget>.satisfiable` (`Formal/Templates/Witness/<Gadget>.lean`, in
   `Formal`), whose statement is `obligation soundness` (`Formal/TemplateSolve.lean`):
   some assignment meets every hypothesis of `soundness`. Not `soundness_consts`, and
   not a `Spec` that says too little (`True`): those are for review.
2. Every declaration of every `Formal.*` module may depend only on `propext`,
   `Classical.choice` and `Quot.sound`: no `sorryAx`, no declared `axiom`, no
   `native_decide`. So may this file's own: a copy with a bad theorem added is how
   `xtask`'s `lean::tests` show the check refusing it.
3. No `Formal` file uses `example` outside comments: it leaves no declaration, so (2)
   never sees its axioms. No theorem can cite one either, so this keeps a check from
   passing on `native_decide` unseen; it guards no other theorem.
4. No declaration of `Formal.Minimize` is `implemented_by`, `extern`, `opaque` (what
   `partial` makes) or `unsafe`: `lake exe minimize_check` runs the compiled
   `Xark.Minimize.check`, and `Sound.lean` is about its definition, so they must be
   the same function.

It prints every theorem it checked, one per line, after `checked:`.
-/

open Lean Elab Command

/-- `xtask`'s `camel`: `to_bits__106` ↦ `ToBits106`. -/
def camel (s : String) : String :=
  String.join <| (s.splitOn "_").map String.capitalize

def standard : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]

/-- Why `name`'s compiled code can differ from its definition, if it can. -/
def compiledApart (env : Environment) (name : Name) : Option String :=
  if (Compiler.implementedByAttr.getParam? env name).isSome then some "implemented_by"
  else if isExtern env name then some "extern"
  else match env.find? name with
    | some (.opaqueInfo _) => some "opaque"
    | some info => if info.isUnsafe then some "unsafe" else none
    | none => none

/-- Whether `line` of a Lean file uses `example` as a word outside comments, given the
block-comment depth at its start; and the depth at its end. A line that opens a
comment counts as comment: a bypass that needs one on the same line as the
`example` is left to review. -/
def exampleIn (depth : Nat) (line : String) : Bool × Nat :=
  let opens := (line.splitOn "/-").length - 1
  let closes := (line.splitOn "-/").length - 1
  let ident (c : Char) := c.isAlphanum || c == '_' || c == '\'' || c == '.'
  let word := (line.split (!ident ·)).any (·.toString == "example")
  (depth == 0 && opens == 0 && !line.trimAsciiStart.startsWith "--" && word,
    depth + opens - closes)

/-- (4)'s control: what `controlSpec` runs is `controlImpl`, so (4) must flag it. -/
def controlImpl : Nat := 0
@[implemented_by controlImpl]
def controlSpec : Nat := 1

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
    let sat := Name.mkStr4 "Xark" "Templates" m "satisfiable"
    match env.find? sat with
    | none => errors := errors.push s!"{h}: no theorem {sat} (`cargo xtask lean-export --witnesses`)"
    | some c =>
      let ok ← liftTermElabM do
        -- Reducible only: the two are the same term, and a mismatch must fail, not
        -- unfold `template`'s thousands of rows looking for a match.
        if env.contains n then
          Meta.withReducible <| Meta.isDefEq c.type (← Xark.Template.obligation n)
        else pure false
      unless ok do errors := errors.push s!"{h}: {sat} isn't `obligation% soundness`"
    unless (env.getModuleIdx? (Name.mkStr4 "Formal" "Templates" "Witness" m)).isSome do
      errors := errors.push s!"{h}: Formal.Templates.Witness.{m} is not imported by Formal.lean"
    let consts := Name.mkStr3 "Formal" "Templates" "Consts" |>.str m
    if ← System.FilePath.pathExists s!"Formal/Templates/Consts/{m}.lean" then
      unless (env.getModuleIdx? consts).isSome do
        errors := errors.push s!"{h}: {consts} is not imported by Formal.lean"
  let mut decls := env.constants.map₂.toList.map (·.1, `this)
  for mod in env.header.moduleNames, data in env.header.moduleData do
    if (`Formal).isPrefixOf mod then decls := decls ++ data.constNames.toList.map (·, mod)
  if (compiledApart env ``controlSpec).isNone then
    errors := errors.push "the compiled-code check accepts implemented_by"
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless (`Formal.Minimize).isPrefixOf mod do continue
    for c in data.constNames do
      if let some why := compiledApart env c then
        errors := errors.push s!"{c} ({mod}) is {why}: minimize_check would run other code"
  let mut checked := #[]
  for (c, mod) in decls do
    let bad := (← collectAxioms c).filter (!standard.contains ·)
    unless bad.isEmpty do errors := errors.push s!"{c} ({mod}) depends on {bad.toList}"
    if (env.find? c).any (·.isThm) && !c.isInternalDetail then checked := checked.push c
  -- (3)'s controls: the forms it must see, and prose it must not.
  for (line, hit) in [("example : True := trivial", true),
      ("set_option maxRecDepth 1000 in example : True := trivial", true),
      ("@[simp] example (n : ℕ) : n = n := rfl", true), ("/-- for example: x -/", false),
      ("-- an example", false), ("theorem example_1 : True := trivial", false)] do
    unless (exampleIn 0 line).1 == hit do errors := errors.push s!"the `example` scan misreads `{line}`"
  for f in ← System.FilePath.walkDir "Formal" do
    unless f.extension == some "lean" do continue
    let mut depth := 0
    for line in (← IO.FS.lines f), i in [1:1000000] do
      let (hit, d) := exampleIn depth line
      depth := d
      if hit then errors := errors.push s!"{f}:{i}: `example` hides its axioms; name it"
  logInfo m!"checked:\n{"\n".intercalate (checked.qsort Name.lt |>.map toString).toList}"
  unless errors.isEmpty do
    throwError "axiom check failed:\n{"\n".intercalate errors.toList}"
  logInfo m!"{checked.size} theorems in {harnesses.size} harnesses' proofs and the rest of \
    Formal: standard axioms only"
