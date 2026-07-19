//! `xark-poseidon2`: the Poseidon2 permutation over BN254 `Fr`, state width
//! `t = 3`, S-box `x^5` (`alpha = 5`), written entirely in the `Field` subset so
//! the compiler inlines it into flat R1CS.
//!
//! Poseidon2 (Grassi, Khovratovich, Schofnegger — <https://eprint.iacr.org/2023/323>)
//! keeps Poseidon's `x^5` S-box but replaces the round structure:
//!
//!   * an **extra external linear layer** `M_E` is applied *before* the rounds;
//!   * full (external) rounds use the fixed matrix `M_E = circ(2,1,1)`;
//!   * partial (internal) rounds use the sparse matrix `M_I = J + diag(mu-1)`,
//!     which for `t = 3` is `[[2,1,1],[1,2,1],[1,1,3]]`.
//!
//! ## Parameters (BN254 / BN256, t = 3, alpha = 5)
//!
//!   * `t   = 3`, `alpha = 5`
//!   * `R_F = 8`  full rounds (4 before + 4 after the partial rounds)
//!   * `R_P = 56` partial rounds
//!
//! ## Constants — CANONICAL
//!
//! The round constants (`RC_EXT`: 8x3, `RC_INT`: 56) and the internal diagonal
//! are transcribed from the reference Horizen Labs implementation
//! (`HorizenLabs/poseidon2`, `poseidon2_instance_bn256.rs`, params
//! `new(t=3, d=5, R_F=8, R_P=56, MAT_DIAG3_M_1=[1,1,2], MAT_INTERNAL3, RC3)`).
//! The permutation ordering here matches that repo's `Poseidon2::permutation`
//! exactly, so this gadget reproduces the canonical Poseidon2 for BN256/BN254
//! t=3.
//!
//! ## Cost model
//!
//! Only `variable * variable` products emit an R1CS gate. Adding round constants
//! (ARK) and both linear layers (`M_E`, `M_I` are constant-matrix products) fold
//! into linear combinations for free. Every gate comes from an S-box:
//! `x^5` = `x2 = x*x`, `x4 = x2*x2`, `x5 = x4*x` = 3 gates. So the permutation
//! costs `8*3*3 + 56*1*3 = 72 + 168 = 240` multiplication gates.

#![no_std]
// Circuit-lowered gadget code: the xark compiler rejects compound assignment on
// `Field` (`+=`/`-=`/`*=`), so `x = x + y` is required — not a clippy oversight.
#![allow(clippy::assign_op_pattern)]

use xark::Field;

/// State width.
const T: usize = 3;

/// The Poseidon2 S-box for `alpha = 5`: `x^5`. Lowers to 3 gates via repeated
/// squaring (`x2`, `x4`, `x5`).
fn sbox(x: Field) -> Field {
    x.pow(5)
}

/// External linear layer `M_E = circ(2,1,1) = [[2,1,1],[1,2,1],[1,1,2]]`.
///
/// Since `2*x_i + (others) = x_i + sum`, this is `out[i] = state[i] + sum`, which
/// is purely additive/linear and emits ZERO gates. (Cross-checked against the
/// explicit matrix product for 1000 random vectors in `poseidon2_ref.py`.)
fn matmul_external(state: [Field; T]) -> [Field; T] {
    let s = state[0] + state[1] + state[2];
    [state[0] + s, state[1] + s, state[2] + s]
}

/// Internal linear layer `M_I = J + diag(mu - 1)` with `mu - 1 = [1,1,2]`, i.e.
/// `M_I = [[2,1,1],[1,2,1],[1,1,3]]`. Equivalently `out[i] = sum + diag[i]*x[i]`
/// with `diag = [1,1,2]`. Only `state[2]` gets a nontrivial constant scale
/// (`2`), which folds into the linear combination — ZERO gates. (Cross-checked
/// against the explicit matrix product in `poseidon2_ref.py`.)
fn matmul_internal(state: [Field; T]) -> [Field; T] {
    let s = state[0] + state[1] + state[2];
    let two = Field::from(2u8);
    [s + state[0], s + state[1], s + two * state[2]]
}

/// One external (full) round: add the 3-lane round constant, S-box ALL lanes,
/// then apply `M_E`.
fn external_round(state: [Field; T], rc: [Field; T]) -> [Field; T] {
    let s = [state[0] + rc[0], state[1] + rc[1], state[2] + rc[2]];
    let s = [sbox(s[0]), sbox(s[1]), sbox(s[2])];
    matmul_external(s)
}

/// One internal (partial) round: add the round constant to `state[0]`, S-box
/// `state[0]` ONLY, then apply `M_I`.
fn internal_round(state: [Field; T], rc0: Field) -> [Field; T] {
    let mut s = state;
    s[0] = s[0] + rc0;
    s[0] = sbox(s[0]);
    matmul_internal(s)
}

/// The Poseidon2 permutation on a width-3 BN254 state.
///
/// Schedule: initial `M_E`, then 4 full rounds, 56 partial rounds, 4 full
/// rounds (matching Horizen Labs `Poseidon2::permutation`).
pub fn poseidon2_perm(state: [Field; T]) -> [Field; T] {
    let rc_ext: [[Field; 3]; 8] = [
        [
            Field::from(
                "13128406282895484157369354038809433636203389051939936481821261911791933663254",
            ),
            Field::from(
                "18931653859213243425446645781588512487838213266321401679594943842133071369744",
            ),
            Field::from(
                "14100663835952519432830313936592734340076294692040144715814219945570907513297",
            ),
        ],
        [
            Field::from(
                "4829113795940962171577509772302063766582957624337039572002553144762883322341",
            ),
            Field::from(
                "15524196826242151316602020382811195434692947787822797536837043495207890599720",
            ),
            Field::from(
                "11824742889827005569732308046012743315382715056680481843559537371456931944245",
            ),
        ],
        [
            Field::from(
                "15824369292130948538570881538463827283727388637222356799784648390667783881850",
            ),
            Field::from(
                "7395652367440825515524159918310823124942438011035473842936180620057265532493",
            ),
            Field::from(
                "1241351203963627868835881804826107927839874261162687401459390240620885410254",
            ),
        ],
        [
            Field::from(
                "6688265362431458560657026053775250595854204120757399493099812773970419156132",
            ),
            Field::from(
                "18628865421786169197184064906533816626840829027307965436801990532221681661310",
            ),
            Field::from(
                "17770079997659052348824924629777474963416629061770380464722096481670103655806",
            ),
        ],
        [
            Field::from(
                "12123026335854515584932892161148559902027319284544852339906677442670161590992",
            ),
            Field::from(
                "11747143856113197599032240626240804787576886917202313931914972592787570603429",
            ),
            Field::from(
                "12689083329367969619896630238881490862330991685178863399139986099061967775891",
            ),
        ],
        [
            Field::from(
                "9363616378570856727297258914956380343356030981401312041884116403700849212733",
            ),
            Field::from(
                "13238291046435061349401827110993774315432323243867917623501520885175217584478",
            ),
            Field::from(
                "13857006478672530359037215101120381968370236111775805219419707798416454682620",
            ),
        ],
        [
            Field::from(
                "2022752961549084842139747691238383165524359342011064407942599644003308437489",
            ),
            Field::from(
                "11377043765620686524844863869245961003946340433252666374730228559486855986878",
            ),
            Field::from(
                "9107028336454933966239128359918274121166034584181733998485105905495346200934",
            ),
        ],
        [
            Field::from(
                "900063247840342897532382686223939136593244983486268682637380837456165317070",
            ),
            Field::from(
                "11261302954518146885624063833699323298803404236535464228351677636819579513431",
            ),
            Field::from(
                "7126990412157463341897179572979760225771626877677162088926546182321369054630",
            ),
        ],
    ];
    let rc_int: [Field; 56] = [
        Field::from(
            "11811415718957691261673974625780511541635150909919309658375768251762566747317",
        ),
        Field::from(
            "17491388639298611159333770975992024026420968324544834879936543171716736973879",
        ),
        Field::from("5647537972700463414111873015737673282707440513292923385601908870282442800104"),
        Field::from(
            "13098696909140066209556423100763036393001603197583133354863092304798723388565",
        ),
        Field::from("6951180250619279643770888203380891623788978362131976553140006882493632020745"),
        Field::from(
            "11250251081997661635793843737498879309304455145146915350538637298238893102958",
        ),
        Field::from("2246982048814095620312232487641427155108104073024754628893054837638848127964"),
        Field::from(
            "18897180842973857564376958241871700087418903006311506731527228148081597475814",
        ),
        Field::from(
            "11557404599711559103972421944754928847181400366333080241838467983028485750549",
        ),
        Field::from(
            "17156358787639157774388183034849932704703797218604790661321342987075785318260",
        ),
        Field::from("8846001957151556825394442611430138293780354129800063716225175548340091032449"),
        Field::from(
            "21883449834630454155761926448978525628607016008113566399646971468161186616967",
        ),
        Field::from(
            "11782201180140779170005707786217005381305915516114251118577530420880166417952",
        ),
        Field::from(
            "19574374768428302416384468550351257389078501920039012797497943057156188490399",
        ),
        Field::from("8515987927591912252146893631936027853249294776314628553087138119917968203620"),
        Field::from(
            "17278996890957540943430295799612663512184925495827057764219426280563743078943",
        ),
        Field::from("4560144125266860756441160513270281593457202308593722614013851111005532208589"),
        Field::from(
            "18507459160700813704135500972073304101922968342745790738233104310822653821881",
        ),
        Field::from(
            "12853272419783978245995917302225694649366687506910892647236063701566570840428",
        ),
        Field::from(
            "14374895923592519298500369713759001634990764548024903321294831249025876110484",
        ),
        Field::from("1754533789272381217541450481312878927560073411620344950409407505576538004136"),
        Field::from(
            "20448232810715691360468548645921483318770769828465347895613479253435247065293",
        ),
        Field::from("4203277692183102377396835282861288449527228200284576966986741905195109677387"),
        Field::from(
            "11506339386261725202512749094297334054772084639665212079028551409689271965431",
        ),
        Field::from("4408799661846477128378547528471700197737434561274043409442231147309460168718"),
        Field::from(
            "10862521404448958117187164110262290189825635328197001646848012017699995213390",
        ),
        Field::from("7012061838863338817532836723152059636816924388921632356281537445328382279260"),
        Field::from("8337544039076735620694225144163354013921209405711398618659178986151546625400"),
        Field::from(
            "16173744372216956516796750206695252671549928142051779144629150462255079400849",
        ),
        Field::from(
            "19072902632067672883974143637757649536845413107085656789672471396027868707732",
        ),
        Field::from("3487852254355424154670010750480228751987308757772575371606146474985412561707"),
        Field::from(
            "17727517395793273304860106667199855253218123164763798377815886217088561516989",
        ),
        Field::from(
            "13280131383170382695839570176732265848909891244754629477752800360224963964534",
        ),
        Field::from(
            "21504421972374418324171209120165696620934505501591484695447432472073975792776",
        ),
        Field::from(
            "13753604424945682926871108642602624411461374991709441590662260371815673344981",
        ),
        Field::from("8053178768600673579416591772204841415225213226540397062676127402210384682315"),
        Field::from(
            "15101558583452488762759591936595783545455044970328380152280373697190919758012",
        ),
        Field::from("6286700389345423344101403023711121482167900236544298155098199100234816571786"),
        Field::from(
            "19368755554193272721035317233504719593365546521121074341670771231332472422552",
        ),
        Field::from(
            "13306281365497267243785678269212920842854030794417306689235276460198094483575",
        ),
        Field::from(
            "10121764749051640353641114693266514664967620368543293902008953934189850195966",
        ),
        Field::from("179619165022370308972665071682395477322215797039585945216341070107573537790"),
        Field::from(
            "14053393851645634065914179337120715807963438235922115988819572738574714471437",
        ),
        Field::from(
            "17345906218970918797922168310670548252023720338285437740234091480846393436478",
        ),
        Field::from(
            "10383068492552043678323859571562933490503408853170063884414176092784243607055",
        ),
        Field::from(
            "12096041499044892166554391619429604246288825927654072010011878199637889490527",
        ),
        Field::from("6449742640166027959651492823149770763572943879017164812917305794918053034585"),
        Field::from("6551805454148805882554763665748573416514894105513920161214733482541847062214"),
        Field::from("3651410956659878392469489270906333016569562868954890104332567650040497030813"),
        Field::from(
            "15219053914464753937310253926447830297339787956721755285255510737973021838676",
        ),
        Field::from("881679665678132972106931291023348167890022611850562267871389203532691753422"),
        Field::from("5006067481688857073852527145736822635357747460125905556158034280392250104971"),
        Field::from(
            "12765332320844032254009314500332101047115754896003948733635815046365410860591",
        ),
        Field::from(
            "12908190215073542091623737558383307555705501651914623082354191483197810853182",
        ),
        Field::from("1446042792715825508366007519346636771782990303010685652946852324744810237839"),
        Field::from(
            "17414863822034645298427260856470503848317996477890518738401812766215195632841",
        ),
    ];

    // Initial external linear layer (Poseidon2 adds this before the rounds).
    let mut s = matmul_external(state);

    // First 4 external (full) rounds.
    let mut r = 0usize;
    while r < 4usize {
        s = external_round(s, rc_ext[r]);
        r += 1;
    }

    // 56 internal (partial) rounds.
    let mut r = 0usize;
    while r < 56usize {
        s = internal_round(s, rc_int[r]);
        r += 1;
    }

    // Last 4 external (full) rounds.
    let mut r = 0usize;
    while r < 4usize {
        s = external_round(s, rc_ext[4usize + r]);
        r += 1;
    }

    s
}

/// 2-to-1 compression: absorb `a` and `b` alongside a zero capacity element, run
/// the permutation once, and squeeze the first state element.
///
/// `hash2(a, b) = poseidon2_perm([a, b, 0])[0]`.
pub fn hash2(a: Field, b: Field) -> Field {
    let out = poseidon2_perm([a, b, Field::from(0u8)]);
    out[0]
}

/// Variable-length hash of `N` field elements via a Poseidon2 **sponge**
/// (rate 2, capacity 1). `N` is a compile-time constant (a circuit is
/// fixed-size, so length is chosen at compile time and the absorb loop unrolls).
///
/// Construction: the capacity lane is seeded with the length `N` for domain
/// separation (so `hash([a]) != hash([a, 0])`); inputs are absorbed two at a
/// time by *adding* into the rate lanes and permuting; a final partial pair is
/// zero-padded; the first state element is squeezed as the digest.
pub fn hash<const N: usize>(inputs: [Field; N]) -> Field {
    let mut state = [Field::from(0u8), Field::from(0u8), Field::from(N as u64)];
    let mut i = 0usize;
    while i < N {
        state[0] = state[0] + inputs[i];
        if i + 1 < N {
            state[1] = state[1] + inputs[i + 1];
        }
        state = poseidon2_perm(state);
        i += 2;
    }
    state[0]
}
