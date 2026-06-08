/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib
import Formal.Poseidon

-- The `style.header` linter hard-codes mathlib's Apache license string; this is
-- an MIT project, so disable that house-style check (it is not a correctness lint).
set_option linter.style.header false
-- The round-constant table and internal-diagonal vector are 254-bit decimal
-- literals, which necessarily exceed the 100-column house style. They are
-- mechanical data, not prose.
set_option linter.style.longLine false

/-!
# xark Poseidon2 — concrete BN254 / `t = 4` specialisation, Lean 4 / mathlib

This file instantiates the parametric Poseidon2 model from `Formal.Poseidon` to
the **specific** Poseidon2 permutation used by the in-circuit gadget
`crates/acir-r1cs/src/gadgets/poseidon.rs::poseidon2_permutation_native`:

* State width `t = 4` over BN254 `Fr` (`ZMod bn254FrModulus`).
* `R_F = 8` full rounds (split `4 + 4` around `R_P = 56` partial rounds), for a
  total of `64` scheduled rounds.
* The external 4×4 matrix `M_E` (Poseidon2's optimized fast-mix matrix as
  emitted by Barretenberg's straight-line `matrix_multiplication_4x4`,
  `poseidon.rs` lines 492–511) — verified by symbolic expansion to be the
  fixed-integer matrix encoded by `Xark.poseidon2_bn254_M_E` below.
* The internal-round matrix `M_I` (`internal_m_multiplication`,
  `poseidon.rs` lines 513–523): `M_I[i][j] = diag[i] * δ_{ij} + 1`, where
  `diag` is the four-element diagonal from
  `INTERNAL_DIAG_HEX` in `poseidon.rs` lines 54–60.
* All 256 round constants `rc_table[round][cell]` from
  `ROUND_CONSTANT_HEX` in `poseidon.rs` lines 64–449 (full transcription;
  partial-round entries store the cell-0 constant only, with the remaining
  three cells set to `0`).

All constants are stored as natural-number literals (the decimal reduction of
the hex strings modulo `bn254FrModulus`), then coerced to `ZMod bn254FrModulus`
via `Nat.cast`. We do this because Lean 4 has no native big-integer hex literal
in `ZMod`, and pulling 256 enormous `OfNat` instances into elaboration would
balloon compile time.

The headline theorem `poseidon2_bn254_determined` is an immediate instance of
`poseidon_permutation_determined` from `Formal.Poseidon` — its content is the
named *concrete* specialisation: that we have actually pinned down the BN254 /
`t = 4` instance used by the gadget. Combined with `Xark.sbox_sound`, this
shows the entire `poseidon.rs` permutation carries **no prover freedom**
anywhere: every output cell is a fixed function of the input state.

Scope notes:

* The expected-value smoke check on the all-zeros input (Section "Stretch")
  is *stated only* — the RHS would come from running
  `poseidon2_permutation_native(&mut [0; 4])` (see the Rust test
  `native_matches_external_kat_all_zeros`). We do not embed the expected
  vector because the entire point of the file is structural: we have not
  added the KAT as an axiom or unproven theorem; it is a `def`-level
  identity that would discharge by `decide` over `ZMod`, which is out of
  scope for this file.
-/

namespace Xark

/-- BN254 scalar field modulus (Fr). Same value as `ark_bn254::Fr` / Noir's
`field_from_hex` reduction modulus. -/
def bn254FrModulus : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- BN254 scalar field `Fr` as `ZMod` (the same field the Rust gadget computes
in). -/
abbrev Bn254Fr : Type := ZMod bn254FrModulus

/-! ## Round constants

All 256 BN254 / `t = 4` Poseidon2 round constants, transcribed from
`ROUND_CONSTANT_HEX` in `poseidon.rs` (lines 64–449). Each entry is the
hex constant reduced modulo `bn254FrModulus` and rewritten in decimal.

For internal (partial) rounds 4..59 (zero-indexed), only the cell-0 constant is
non-zero in the Rust source; the remaining three slots are stored as `0` to
preserve the uniform `(c0, c1, c2, c3)`-per-round shape. The cell-0-only
addition matches the gadget's `state[0] += rc_table[r][0]` line at
`poseidon.rs` line 549 and the `partialRound` model in `Formal.Poseidon`.
-/

/-- All 256 BN254 / `t = 4` Poseidon2 round constants in declaration order,
expressed as `ℕ` literals. Row `r` is `(rc[r][0], rc[r][1], rc[r][2], rc[r][3])`.
Source: `poseidon.rs::ROUND_CONSTANT_HEX`. -/
def poseidon2Bn254RoundConstantsNat : List (ℕ × ℕ × ℕ × ℕ) :=
  [
  (11633431549750490989983886834189948010834808234699737327785600195936805266405, 17353750182810071758476407404624088842693631054828301270920107619055744005334, 11575173631114898451293296430061690731976535592475236587664058405912382527658, 9724643380371653925020965751082872123058642683375812487991079305063678725624),
  (20936725237749945635418633443468987188819556232926135747685274666391889856770, 6427758822462294912934022562310355233516927282963039741999349770315205779230, 16782979953202249973699352594809882974187694538612412531558950864304931387798, 8979171037234948998646722737761679613767384188475887657669871981433930833742),
  (5428827536651017352121626533783677797977876323745420084354839999137145767736, 507241738797493565802569310165979445570507129759637903167193063764556368390, 6711578168107599474498163409443059675558516582274824463959700553865920673097, 2197359304646916921018958991647650011119043556688567376178243393652789311643),
  (4634703622846121403803831560584049007806112989824652272428991253572845447400, 17008376818199175111793852447685303011746023680921106348278379453039148937791, 18430784755956196942937899353653692286521408688385681805132578732731487278753, 4573768376486344895797915946239137669624900197544620153250805961657870918727),
  (5624865188680173294191042415227598609140934495743721047183803859030618890703, 0, 0, 0),
  (8228252753786907198149068514193371173033070694924002912950645971088002709521, 0, 0, 0),
  (17586714789554691446538331362711502394998837215506284064347036653995353304693, 0, 0, 0),
  (12985198716830497423350597750558817467658937953000235442251074063454897365701, 0, 0, 0),
  (13480076116139680784838493959937969792577589073830107110893279354229821035984, 0, 0, 0),
  (480609231761423388761863647137314056373740727639536352979673303078459561332, 0, 0, 0),
  (19503345496799249258956440299354839375920540225688429628121751361906635419276, 0, 0, 0),
  (16837818502122887883669221005435922946567532037624537243846974433811447595173, 0, 0, 0),
  (5492108497278641078569490709794391352213168666744080628008171695469579703581, 0, 0, 0),
  (11365311159988448419785032079155356000691294261495515880484003277443744617083, 0, 0, 0),
  (13876891705632851072613751905778242936713392247975808888614530203269491723653, 0, 0, 0),
  (10660388389107698747692475159023710744797290186015856503629656779989214850043, 0, 0, 0),
  (18876318870401623474401728758498150977988613254023317877612912724282285739292, 0, 0, 0),
  (15543349138237018307536452195922365893694804703361435879256942490123776892424, 0, 0, 0),
  (2839988449157209999638903652853828318645773519300826410959678570041742458201, 0, 0, 0),
  (7566039810305694135184226097163626060317478635973510706368412858136696413063, 0, 0, 0),
  (6344830340705033582410486810600848473125256338903726340728639711688240744220, 0, 0, 0),
  (12475357769019880256619207099578191648078162511547701737481203260317463892731, 0, 0, 0),
  (13337401254840718303633782478677852514218549070508887338718446132574012311307, 0, 0, 0),
  (21161869193849404954234950798647336336709035097706159414187214758702055364571, 0, 0, 0),
  (20671052961616073313397254362345395594858011165315285344464242404604146448678, 0, 0, 0),
  (2772189387845778213446441819361180378678387127454165972767013098872140927416, 0, 0, 0),
  (3339032002224218054945450150550795352855387702520990006196627537441898997147, 0, 0, 0),
  (14919705931281848425960108279746818433850049439186607267862213649460469542157, 0, 0, 0),
  (17056699976793486403099510941807022658662936611123286147276760381688934087770, 0, 0, 0),
  (16144580075268719403964467603213740327573316872987042261854346306108421013323, 0, 0, 0),
  (15582343953927413680541644067712456296539774919658221087452235772880573393376, 0, 0, 0),
  (17528510080741946423534916423363640132610906812668323263058626230135522155749, 0, 0, 0),
  (3190600034239022251529646836642735752388641846393941612827022280601486805721, 0, 0, 0),
  (8463814172152682468446984305780323150741498069701538916468821815030498611418, 0, 0, 0),
  (16533435971270903741871235576178437313873873358463959658178441562520661055273, 0, 0, 0),
  (11845696835505436397913764735273748291716405946246049903478361223369666046634, 0, 0, 0),
  (18391057370973634202531308463652130631065370546571735004701144829951670507215, 0, 0, 0),
  (262537877325812689820791215463881982531707709719292538608229687240243203710, 0, 0, 0),
  (2187234489894387585309965540987639130975753519805550941279098789852422770021, 0, 0, 0),
  (19189656350920455659006418422409390013967064310525314160026356916172976152967, 0, 0, 0),
  (15839474183930359560478122372067744245080413846070743460407578046890458719219, 0, 0, 0),
  (1805019124769763805045852541831585930225376844141668951787801647576910524592, 0, 0, 0),
  (323592203814803486950280155834638828455175703393817797003361354810251742052, 0, 0, 0),
  (9780393509796825017346015868945480913627956475147371732521398519483580624282, 0, 0, 0),
  (14009429785059642386335012561867511048847749030947687313594053997432177705759, 0, 0, 0),
  (13749550162460745037234826077137388777330401847577727796245150843898019635981, 0, 0, 0),
  (19497187499283431845443758879472819384797584633472792651343926414232528405311, 0, 0, 0),
  (3708428802547661961864524194762556064568867603968214870300574294082023305587, 0, 0, 0),
  (1339414413482882567499652761996854155383863472782829777976929310155400981782, 0, 0, 0),
  (6396261245879814100794661157306877072718690153118140891315137894471052482309, 0, 0, 0),
  (2069661495404347929962833138824526893650803079024564477269192079629046031674, 0, 0, 0),
  (15793521554502133342917616035884588152451122589545915605459159078589855944361, 0, 0, 0),
  (17053424498357819626596285492499512504457128907932827007302385782133229252374, 0, 0, 0),
  (13658536470391360399708067455536748955260723760813498481671323619545320978896, 0, 0, 0),
  (21546095668130239633971575351786704948662094117932406102037724221634677838565, 0, 0, 0),
  (21411726238386979516934941789127061362496195649331822900487557574597304399109, 0, 0, 0),
  (1944776378988765673004063363506638781964264107780425928778257145151172817981, 0, 0, 0),
  (15590719714223718537172639598316570285163081746016049278954513732528516468773, 0, 0, 0),
  (1351266421179051765004709939353170430290500926943038391678843253157009556309, 0, 0, 0),
  (6772476224477167317130064764757502335545080109882028900432703947986275397548, 0, 0, 0),
  (10670120969725161535937685539136065944959698664551200616467222887025111751992, 4731853626374224678749618809759140702342195350742653173378450474772131006181, 14473527495914528513885847341981310373531349450901830749157165104135412062812, 16937191362061486658876740597821783333355021670608822932942683228741190786143),
  (5656559696428674390125424316117443507583679061659043998559560535270557939546, 8897648276515725841133578021896617755369443750194849587616503841335248902806, 14938684446722672719637788054570691068799510611164812175626676768545923371470, 15284149043690546115252102390417391226617211133644099356880071475803043461465),
  (2623479025068612775740107497276979457946709347831661908218182874823658838107, 6809791961761836061129379546794905411734858375517368211894790874813684813988, 2417620338751920563196799065781703780495622795713803712576790485412779971775, 4445143310792944321746901285176579692343442786777464604312772017806735512661),
  (1429019233589939118995503267516676481141938536269008901607126781291273208629, 19874283200702583165110559932895904979843482162236139561356679724680604144459, 13426632171723830006915194799390005513190035492503509233177687891041405113055, 10582332261829184460912611488470654685922576576939233092337240630493625631748)
  ]

/-- The BN254 / `t = 4` Poseidon2 round constants as a function
`Fin 64 → Fin 4 → Bn254Fr`. The natural-number table
`poseidon2Bn254RoundConstantsNat` is looked up by index and coerced into
`Bn254Fr` via `Nat.cast`; out-of-range lookups (impossible by `Fin` bounds,
but typing requires a default) are pinned to `0`.

Indexing matches `poseidon.rs::ROUND_CONSTANT_HEX[r][i]` exactly. -/
def poseidon2Bn254RC (r : Fin 64) (i : Fin 4) : Bn254Fr :=
  match poseidon2Bn254RoundConstantsNat[r.val]? with
  | none => 0
  | some (c0, c1, c2, c3) =>
      match i.val with
      | 0 => (c0 : Bn254Fr)
      | 1 => (c1 : Bn254Fr)
      | 2 => (c2 : Bn254Fr)
      | _ => (c3 : Bn254Fr)

/-- Per-round constant vector for round `r`, as the cell-indexed function
expected by `RoundKind.full`. -/
def poseidon2Bn254RCFull (r : Fin 64) : Fin 4 → Bn254Fr :=
  fun i => poseidon2Bn254RC r i

/-! ## Matrices

We encode both the external matrix `M_E` and the internal matrix `M_I`.
-/

/-- The BN254 / `t = 4` Poseidon2 external matrix `M_E`. The straight-line
implementation in `poseidon.rs::matrix_multiplication_4x4` (lines 492–511)
computes a linear map; expanding the temporaries symbolically gives the
fixed integer matrix
```
            ⎛ 5 7 1 3 ⎞
       M_E = ⎜ 4 6 1 1 ⎟
            ⎜ 1 3 5 7 ⎟
            ⎝ 1 1 4 6 ⎠
```
i.e. `(M_E · s) i = ∑ⱼ M_E i j · s j`. This is exactly Barretenberg's
optimized fast-mix matrix for Poseidon2 / `t = 4`. -/
def poseidon2Bn254_M_E : Fin 4 → Fin 4 → Bn254Fr := fun i j =>
  match i.val, j.val with
  | 0, 0 => 5 | 0, 1 => 7 | 0, 2 => 1 | 0, 3 => 3
  | 1, 0 => 4 | 1, 1 => 6 | 1, 2 => 1 | 1, 3 => 1
  | 2, 0 => 1 | 2, 1 => 3 | 2, 2 => 5 | 2, 3 => 7
  | 3, 0 => 1 | 3, 1 => 1 | 3, 2 => 4 | 3, 3 => 6
  | _, _ => 0

/-- BN254 / `t = 4` Poseidon2 internal-matrix diagonal entries. Transcribed
from `INTERNAL_DIAG_HEX` in `poseidon.rs` lines 54–60, reduced mod
`bn254FrModulus` and rewritten in decimal. -/
def poseidon2Bn254InternalDiagNat : Fin 4 → ℕ
  | ⟨0, _⟩ => 7626475329478847982857743246276194948757851985510858890691733676098590062311
  | ⟨1, _⟩ => 5498568565063849786384470689962419967523752476452646391422913716315471115275
  | ⟨2, _⟩ => 148936322117705719734052984176402258788283488576388928671173547788498414613
  | ⟨3, _⟩ => 15456385653678559339152734484033356164266089951521103188900320352052358038155
  | ⟨_+4, h⟩ => absurd h (by omega)

/-- The internal-matrix diagonal as `Bn254Fr` values. -/
def poseidon2Bn254InternalDiag (i : Fin 4) : Bn254Fr :=
  (poseidon2Bn254InternalDiagNat i : Bn254Fr)

/-- The BN254 / `t = 4` Poseidon2 internal matrix `M_I`. Mirrors
`poseidon.rs::internal_m_multiplication` (lines 513–523):
`(M_I · s) i = diag[i] · s[i] + ∑ⱼ s[j]`, which in matrix form is
`M_I[i][j] = diag[i] · δ_{ij} + 1`, i.e. each row is the all-ones row plus
`diag[i]` on the diagonal. -/
def poseidon2Bn254_M_I : Fin 4 → Fin 4 → Bn254Fr := fun i j =>
  if i = j then poseidon2Bn254InternalDiag i + 1 else 1

/-! ## Schedule

The full Poseidon2 round schedule for BN254 / `t = 4` is
`R_F/2 = 4` full rounds, then `R_P = 56` partial rounds, then `R_F/2 = 4`
full rounds (cf. `poseidon.rs` lines 535–562). We build the schedule as a
`List (RoundKind Bn254Fr 4)` of length exactly 64, in declaration order,
using the constants and matrices defined above. -/

/-- The BN254 / `t = 4` Poseidon2 round schedule, length `64`:
* Rounds `0..3`: full with constants `rc[r]` and external matrix `M_E`.
* Rounds `4..59`: partial with constant `rc[r][0]` and internal matrix `M_I`.
* Rounds `60..63`: full with constants `rc[r]` and external matrix `M_E`.

Matches the per-round behaviour of `poseidon2_permutation_native`. -/
def poseidon2Bn254Schedule : List (RoundKind Bn254Fr 4) :=
  (List.range 64).map (fun r =>
    if r < 4 then
      -- First-half full rounds.
      RoundKind.full (poseidon2Bn254RCFull ⟨r % 64, Nat.mod_lt _ (by decide)⟩)
        poseidon2Bn254_M_E
    else if r < 60 then
      -- Partial rounds: only the cell-0 constant matters.
      RoundKind.partialR (poseidon2Bn254RC ⟨r % 64, Nat.mod_lt _ (by decide)⟩ ⟨0, by decide⟩)
        poseidon2Bn254_M_I
    else
      -- Second-half full rounds.
      RoundKind.full (poseidon2Bn254RCFull ⟨r % 64, Nat.mod_lt _ (by decide)⟩)
        poseidon2Bn254_M_E)

/-! ## Concrete Poseidon2 permutation -/

/-- The concrete BN254 / `t = 4` Poseidon2 permutation, modelled as the
parametric `poseidonPermutation` from `Formal.Poseidon` instantiated with
the external matrix `M_E` (initial linear layer) and the 64-round schedule
`poseidon2Bn254Schedule`. -/
def poseidon2Bn254 : (Fin 4 → Bn254Fr) → (Fin 4 → Bn254Fr) :=
  poseidonPermutation poseidon2Bn254_M_E poseidon2Bn254Schedule

/-- **Concrete-permutation determinism.** The BN254 / `t = 4` Poseidon2
permutation is a function of its input state: any two prover witnesses on
the same input produce the same output.

This is an immediate specialisation of
`Xark.poseidon_permutation_determined` to the concrete BN254 / `t = 4`
schedule. The *content* is the named, fully-specialised instance: combined
with `Xark.sbox_sound` (which pins each per-cell `x⁵` map), this shows the
entire `poseidon.rs::poseidon2_permutation` gadget carries no prover
freedom anywhere. -/
theorem poseidon2_bn254_determined
    (s s' : Fin 4 → Bn254Fr) (hs : s = s') :
    poseidon2Bn254 s = poseidon2Bn254 s' := by
  unfold poseidon2Bn254
  exact poseidon_permutation_determined
    poseidon2Bn254_M_E poseidon2Bn254Schedule s s' hs

end Xark
