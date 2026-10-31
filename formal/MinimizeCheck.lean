import Formal.Minimize.Check

/-!
`lake exe minimize_check`: reads minimizer certificates on stdin (written by
`cargo xtask minimize-check`, `xtask/src/minimize_check.rs`, which documents the
format), runs `Xark.Minimize.check` on each, and exits nonzero unless it accepts all.

This file only decodes bytes: what acceptance means is `Formal/Minimize/Sound.lean`'s.
The rows that define no step are decoded and checked one at a time (`recOk` reads only
the header), so a million-row certificate is never decoded at once.

Each decoder takes the input and a position and returns the value and the next
position. A read past the end reads `0` and leaves the position past the end, which
`main` refuses.
-/

open Xark.Minimize

/-- A decoder: the value at position `i`, and the position after it. -/
abbrev Dec (α : Type) := ByteArray → Nat → α × Nat

def byte : Dec UInt8 := fun b i => (if h : i < b.size then b[i] else 0, i + 1)

/-- Unsigned LEB128. Up to nine bytes (63 bits) are gathered in a `UInt64` before they
are added to the natural, which keeps a 254-bit coefficient to five big additions. -/
def uvar : Dec Nat := fun b i => go b i 0 0 (b.size + 1 - i)
where
  /-- Gather up to `n` more bytes (continuing ones) into `w` at bit `s`. -/
  word (b : ByteArray) (i : Nat) (w : UInt64) (s : UInt64) : Nat → UInt64 × Nat × Bool
    | 0 => (w, i, true)
    | n + 1 =>
      let x := if h : i < b.size then b[i] else 0
      let w := w ||| ((x &&& 0x7f).toUInt64 <<< s)
      if x &&& 0x80 == 0 then (w, i + 1, false) else word b (i + 1) w (s + 7) n
  go (b : ByteArray) (i acc shift : Nat) : Nat → Nat × Nat
    | 0 => (acc, i)
    | fuel + 1 =>
      let (w, i, more) := word b i 0 0 9
      let acc := acc + (w.toNat <<< shift)
      if more then go b i acc (shift + 63) fuel else (acc, i)

/-- A field element: zigzag LEB128 of its representative in `(-p/2, p/2]`. -/
def fe (p : Nat) : Dec Nat := fun b i =>
  let (z, i) := uvar b i
  (if z % 2 == 0 then z / 2 else p - (z + 1) / 2, i)

/-- `n` values, `n` read first. -/
def many {α : Type} (f : Dec α) : Dec (List α) := fun b i =>
  let (n, i) := uvar b i
  let rec go : Nat → List α → Nat → List α × Nat
    | 0, acc, i => (acc.reverse, i)
    | k + 1, acc, i => let (x, i) := f b i; go k (x :: acc) i
  go n [] i

def lc (p : Nat) : Dec Lc := fun b i =>
  let (k, i) := fe p b i
  let (t, i) := many (fun b i => let (c, i) := fe p b i; let (x, i) := uvar b i; ((c, x), i)) b i
  (⟨k, t⟩, i)

def row (p : Nat) : Dec Row := fun b i =>
  let (a, i) := lc p b i
  let (c', i) := lc p b i
  let (c, i) := lc p b i
  (⟨a, c', c⟩, i)

def mults (p : Nat) : Dec (List (Nat × Nat)) :=
  many fun b i => let (j, i) := uvar b i; let (m, i) := fe p b i; ((j, m), i)

def orig (p : Nat) : Dec Orig := fun b i =>
  let (r, i) := row p b i
  let (ma, i) := mults p b i
  let (mb, i) := mults p b i
  let (mc, i) := mults p b i
  (⟨r, ma, mb, mc⟩, i)

def var : Dec Var := fun b i =>
  let (id, i) := uvar b i
  let (vis, i) := uvar b i
  let (e, i) := uvar b i
  (⟨id, vis, if e == 0 then none else some (e - 1)⟩, i)

/-- Decode and check one certificate: the header, then each remaining row as it comes. -/
def problem (b : ByteArray) (i : Nat) : Bool × Nat := Id.run do
  let (p, i) := uvar b i
  let (vars, i) := many var b i
  let (outVars, i) := many (fun b i => let (id, i) := uvar b i; let (v, i) := uvar b i;
    ((id, v), i)) b i
  let (steps, i) := many (fun b i => let (v, i) := uvar b i; let (e, i) := lc p b i;
    let (src, i) := orig p b i; ((⟨v, e, src⟩ : Step), i)) b i
  let P : Problem := ⟨p, vars.toArray, outVars.toArray, steps.toArray, #[]⟩
  let mut ok := P.p == bn254 && headerOk bn254 P
  let (n, i) := uvar b i
  let mut i := i
  for _ in [0:n] do
    let (o, j) := orig p b i
    let (f, j) := byte b j
    let (fate, j) := if f == 0 then let (M, j) := row p b j; (Fate.kept M, j) else (.dropped, j)
    ok := ok && recOk bn254 P (o, fate)
    i := j
  return (ok, i)

/-- All of stdin. -/
partial def readAll (acc : Array ByteArray := #[]) : IO ByteArray := do
  let c ← (← IO.getStdin).read ((1 : USize) <<< 24)
  if c.isEmpty then
    let mut out := ByteArray.emptyWithCapacity (acc.foldl (· + ·.size) 0)
    for a in acc do out := out ++ a
    return out
  readAll (acc.push c)

def main : IO UInt32 := do
  let b ← readAll
  unless b.extract 0 4 == "XMC1".toUTF8 do
    IO.eprintln "not a minimizer certificate"
    return 1
  let mut i := 4
  let mut n := 0
  let mut bad := #[]
  while (byte b i).1 == 1 do
    let (ok, j) := problem b (i + 1)
    unless ok do bad := bad.push n
    n := n + 1
    i := j
  if i + 1 != b.size then
    IO.eprintln s!"refused: the certificate stream is malformed at byte {i}"
    return 1
  if bad.isEmpty then
    IO.println s!"accepted {n} certificates"
    return 0
  IO.eprintln s!"refused {bad.size} of {n} certificates: {bad.toList.take 10}"
  return 1
