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
   `native_decide`, except the nine hand-restated lemmas in `legacyNative` below, which
   evaluate GF(2⁸) tables and secp256k1 constants with the compiler. Each goes when the
   template proof of its gadget lands; the list only shrinks.

It prints every theorem it checked, one per line, after `checked:`.
-/

open Lean Elab Command

/-- `xtask`'s `camel`: `to_bits__106` ↦ `ToBits106`. -/
def camel (s : String) : String :=
  String.join <| (s.splitOn "_").map String.capitalize

def standard : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]

/-- The hand-restated lemmas still proven with `native_decide` (`Formal/Aes.lean`,
`GF256.lean`). -/
def legacyNative : List Name := [
  `Xark.aesSbox_algebraic_eq_table_all,
  `Xark.gf256_inv_unique_all, `Xark.gf256_inv_zero, `Xark.aesAffine_nat_lt_256_all,
  `Xark.aesSbox_algebraic_lt_256_all, `Xark.gf256_bit_xor_byte_all, `Xark.gf256_pow254_eq_inv_all,
  `Xark.gf256_inv_lt_256_all, `Xark.gf256_mul_inv_all]

/-- `native_decide`'s axiom for one of the listed lemmas, `<lemma>._native.native_decide.<n>`
(a `private` lemma's name carries the module's `_private` prefix). -/
def isLegacyNative (ax : Name) : Bool :=
  match (toString ax).splitOn "._native." with
  | [head, _] => legacyNative.any fun l => head.endsWith (toString l)
  | _ => false

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
  let mut natives := #[]
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless (`Formal).isPrefixOf mod do continue
    for c in data.constNames do
      let axioms ← collectAxioms c
      let bad := axioms.filter fun a => !standard.contains a && !isLegacyNative a
      unless bad.isEmpty do errors := errors.push s!"{c} ({mod}) depends on {bad.toList}"
      if axioms.any isLegacyNative then natives := natives.push c
      if (env.find? c).any (·.isThm) && !c.isInternalDetail then checked := checked.push c
  logInfo m!"checked:\n{"\n".intercalate (checked.qsort Name.lt |>.map toString).toList}"
  unless errors.isEmpty do
    throwError "axiom check failed:\n{"\n".intercalate errors.toList}"
  logInfo m!"{checked.size} theorems in {harnesses.size} harnesses' proofs and the rest of \
    Formal: standard axioms only, {legacyNative.length} legacy lemmas by native_decide \
    (reached by {natives.size} declarations)"
