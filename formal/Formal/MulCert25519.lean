import Formal.CertCall
import Formal.Ed25519Curve
import Formal.Templates.MulCert25519
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Lift
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

set_option linter.style.header false
set_option linter.style.longLine false

namespace Xark.Templates.MulCert25519

open Xark.Template Xark.R1cs
open Xark.Templates.MulCertK1 (bitRows lowOf)
open Xark.Templates.EcK1Check (norm eval_norm)

def Mtab : List (List ℕ) :=
  [[18843151392664519973366732945053484794762259524796137259282899784967396376100, 14468094559072748899220492219710784247997235066191315662624437230659689852553, 8899704280177085961957479666400986254772487022589251473614170177233698953964, 4522872513814327616651996063125362620073242086825348416414811471334872904972, 962294831058042838247772146176527420985023565971489022379189776343511267393, 1475688067349501731293706377934481572827361976649429512661959528241455493335, 10254849581413197041884623187298404882822761590629742979678456435643082069890, 11400228174882388834750416236994192876824897239721253128117118519167767476643, 14944798287728504245248536936841363440641323315789487653246731083270759138455, 10465658931134754049523375009239822038304870949272464235639456131245598998921, 17627443080797453511005060890838830810235080490294033967088831459844318747853, 21556857078381963576261008336699114555881968450229363785525254973261284118347, 13804397591519736054558170459964736674281552183976843274250440709299887909151, 18332230768843170947425636048789594629080894813871243577490510245218032525976, 7547673835876806496576239436990513888895956926520870801571365966875112131384],
   [19121532149675178430029117290541028281342289948623735032829087440868207744216, 15613299594304725859397884507372270312088495608344825168206583981293537170549, 727935775584617860402214898300663419089646749295719843665108149056845693495, 4136653519335484453005929932355575065965883927466853739284140933746364892417, 7130337292792016574199063076166662320300429201018932772936679509725617627191, 15537407323633021229535036106499577676736832380587430287223225624515677596859, 11840628288317332032547276319585249229154079484087739140680472839457358549731, 18952511249356043860675334413835681767396138501882721060146433473601839525330, 12202745163507321827611747176538966127661425378762776732668664483868454607821, 9630778609105595385100538795978136538795741208395576239899291636175836832209, 141001167722892652506072955881440249335504492756620734905995134925166099799, 20585284633557051483531313979814177539149241613595353243658791271122525668289, 13298188747115567697427496733913833573127242455240939324487826344684211650958, 8233108253187096061276050101344629311335816381360683881374267210935008755880, 17954531207520256370726169673930309296908147871908367547619065458629815550192],
   [7764660496714020969081761782282660002668953843425600807502074261837062551081, 20655835227685921212848657631859365188300182084084703503435357914538743642169, 16808091387062336864855703412453185994679388929117306847886345071345214557408, 8600455209350062510498000814244555468242636764874506245580414088414230225484, 15616413517745694506287623458806901338395942448380571083586305706908429080771, 7239246199657429932222121811984268428292067519615386645319072821630866235755, 7752853565308994175320522354204071299618985809850264627119479612287800610618, 3299817022917328489411635895619146838019824247324341617479768454145278259268, 11331965501340313161435052059086586859164748694326086755262684711411189589129, 10661592322141949942601703220574636252129371069681464690040671408837990655664, 14302928943327075499244312669597148363681230268692410967110735519913649877816, 7820589316904573182410199816427892641364363343780371538955663725070042585778, 12968970842070999973164059782233826465511516297188333741257202439266403129197, 17858313277304695664399298513723421159463934373943146588737314077687561552590, 12424210145182805694190592738960534408853769509043779090312543679312005412208],
   [6006393667117713044199164343121228240132187156468945205743826814136151661182, 19919867822485838668761293857530229782923713889962943089973376647378576879218, 16268000478391255506273385409110601836950307195558383353619162700587101382199, 3784515181995730528824316142314770005667609372708256613089035109608567628125, 19795551106367808504914334048992180091771900132073614454491767100537064219894, 19798018620519820625589350758046676251278479072789591322707917859381859118863, 7538754364268447693284136724814767127642568207779947404062389731996104089619, 11326827904651024938697356849625188357165004682702945673568393225130348555746, 3365424406225341240446618038564230404606600966342434026102417413065525627576, 18675240871177938756118394714955063816208310235029126409928422271538205055675, 1220399123553478934587480817098714212672779514735819467039688565542605218977, 4940924127020022972988905356331108851565571227078427620003523939875739294173, 18807588854862054260089398241276443328472335113577675224491085037356472316395, 3000814518764914487889103114203966218664294660018263116844118230546400252712, 20657621927312811615308007546073032182665253776501901767920508845925746664582],
   [6919229505415562417351464162115485457828607679895127701973185682638899963361, 16456407674776720398563971680198324790580876478864038595594135298981466153298, 8446124283330624520154786908255354599315192983642614111693013639296256302531, 7725255233585010538308656085990538549165219562072303825906593661387577077430, 12137630737294253150389703068912659039700282755371235591406370411293099041751, 18723506433187412753155765755254682929702040739292628312525942777913209239669, 11985904503476130793495194276588810040030316079266316132294221529887715239222, 935015454292133324873595772761053582610294356031220003239096512284463837308, 5731731773871800385735905153503131053574695604218043634013394084227488059709, 15141248906697081371200076024855150265615195962170527259694069630541556569599, 808712809452340780898555329849989519115364600373111303447519892360212867047, 20120578226575709187209837198118493662757172740393762870719827953964743578081, 19859522138460400001382470341770775131303004824122071960936665956759997374619, 13434099795828461384281771299917712456516028650172894874773116182673519807056, 16680975498470560770969492903966039630572622187442378571368480278396262854255],
   [20543678737887796111712329437116537464053935989109344910148469437332293653160, 3884406391398218130252441223528745757439561995315654704727713923047023162267, 17721762722846350604281860256732215296681413062833511771539621058215307252595, 17651116895670543446799253960651720064271079265628968835416369686293601245371, 11612532265301448513982775945781298477910968628161831803069108355215334330899, 3152647680176431321762436312520287690291990085197709620376085863700831632566, 913697519335729566481227948823339868853211558169069879402231604285564601112, 18616659903703483553032400145786760615243809101029776617835720287670253045931, 2639531907281165276671810539388954414401501659297772640228845795828621115347, 13513577248176466815343168950943142358901658627882957640837730789334616441205, 12267418262072098257542557902509162474525241395931334029911039964823168513136, 15889989821745336827320997429124499159013364816117139751777578571303364792259, 7552784087041752261190351286457866775203947230581545839976608567253831047376, 3433737250471423812343311717981744892343957151342813820869469475376207215943, 3824159409766682057007917159454650310702910236312808539770835926350641420152],
   [21564149374040170702723454451766954817916689085379490254725359325748973046941, 6948751387916785805021778654815694103065928637438036978729631620213623863486, 4373820840697649164702184912997844297192106044623022081188129059960153471240, 3257038439265400700605468064361092232121051453048923528224471022107328498199, 11056664510093881205952203919805788820982986080298973541115335288356295473334, 5095473523477075918219195965333134886488699260158744454476887402716874098032, 20107386286066205619700958815734364229244083839614548551212855697581819297340, 15720681375381621283294249405298482484037692512274146367179994428246591470166, 7088177936103105470207139781149996831920962492195986379626141977163318351428, 21006221920917815737822394742432161635654635071821245633192612360583201640902, 6676978690898544978961500338120829436909458148938143073500147694960882457119, 728180749442817771121649787414186890100494537239540136457692904666522640135, 19945777886318560619251943671129280503911562888464204667624457640107727015754, 13969540401669553328083376547025145688181326076676420834189001589626867375546, 17567099652425013472303746904673243850659239075156848268142915480566289265314],
   [15612838914589851321080782691554701412070614247748737818497864859174723863829, 2411442418729322531700460545951210314222474226926419733109803568637927582022, 16933164570208080220645376310308494462337279856474267088858505697601089650378, 12834901781088760716658679150228479780676595860886371849332123662389961549818, 7259713900311913034244192067503632120903218706513781447789545590989315164843, 2581515416969616900132575751086041147665130113895701728357520324933312143438, 19638407550534344809544577226145855565705079812952512331456300882922721974448, 12199558858310824611690188627201738351105669847045812510297065449377284339636, 13101404619155371088471705540286345749613419691287063977143886447139728862597, 12930144107738436134361300057062036982409449331422794132810682592092902471392, 277092691021304068773965894307229401099098249427826097984479058398603914754, 11229892649163709100861622014069784941291153478955806321002037237821119343078, 15063978618089393602443245487524339638557016913273826902195213757900383651581, 19246377155593393653805578587383899067182298466980090874557647660798851118913, 13785509723209879983556996011444411773548416399537261936192956702428542334209]]

/-- The interpolation-and-fold matrix: `d_k = Σ_j M k j · C(j)`. -/
def M (k j : ℕ) : F := ((Mtab.getD k []).getD j 0 : ℕ)

/-- Plug offsets of `aᵢ`, `bᵢ` (`i < 3`) and `t`. -/
def ao (i : ℕ) : ℕ := 16 * i
def bo (i : ℕ) : ℕ := 16 * i + 8

/-- `V(j) = Σ_l jˡ·v_l` over the 8 plugs from `o`. -/
def evT (o j : ℕ) : List (F × TVar) := (List.range 8).map fun l => (((j ^ l : ℕ) : F), .plug (o + l))
def aLC (i j : ℕ) : LC := norm ⟨0, evT (ao i) j⟩
def bLC (i j : ℕ) : LC := norm ⟨0, evT (bo i) j⟩

/-- The sign of pair `i`: `+` for the first, `−` for the others. -/
def sg (i : ℕ) : F := if i = 0 then 1 else -1

def scale (c : F) (ts : List (F × TVar)) : List (F × TVar) := ts.map fun t => (c * t.1, t.2)

/-- `d_k = Σ_j M k j · Σ_i sg i · P_{ij}`, `P_{ij}` the product `wit (3j + i)`. -/
def dT (k : ℕ) : List (F × TVar) :=
  (List.range 15).flatMap fun j => (List.range 3).map fun i => (sg i * M k j, .wit (3 * j + i))

/-- `Σ_{k<4} 2^(32k)·(d_{o+k} − t_{o+k})`: `L` at `o = 0`, `U` at `o = 4`. -/
def halfT (o : ℕ) : List (F × TVar) :=
  (List.range 4).flatMap fun k =>
    scale (2 ^ (32 * k)) (dT (o + k)) ++ [(-(2 ^ (32 * k)), .plug (48 + o + k))]

/-- `K + 2⁵¹ = q − 2⁵¹`, `q` the quotient `wit 45`. -/
def kLC : LC := ⟨-(2 ^ 51), [(1, .wit 45)]⟩
/-- `T + 2⁵⁰ = 2¹²⁷·(q − 2⁵²) − U + 2⁵⁰`. -/
def tTerms : List (F × TVar) := [(2 ^ 127, .wit 45)] ++ scale (-1) (halfT 4)
def tLC : LC := norm ⟨-(2 ^ 179) + 2 ^ 50, tTerms⟩
/-- `L + 19·K − 2¹²⁸·T`. -/
def eLC : LC :=
  norm ⟨19 * -(2 ^ 52) - 2 ^ 128 * -(2 ^ 179),
    halfT 0 ++ [(19, .wit 45)] ++ scale (-(2 ^ 128)) tTerms⟩

def prodRows : List Row :=
  (List.range 15).flatMap fun j => (List.range 3).map fun i =>
    ⟨aLC i j, bLC i j, LC.var (.wit (3 * j + i))⟩

def rows : List Row := prodRows ++ bitRows kLC 47 51 ++ bitRows tLC 98 50 ++ [⟨eLC, ⟨1, []⟩, ⟨0, []⟩⟩]

theorem inputs_eq : template.inputs = (List.range 56).map fun j => LC.var (.plug j) := by
  decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem rows_eq : template.rows = rows := by decide +kernel

/-! ### The fold -/

open Finset

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- Limb `m` of a product polynomial contributes to column `k` of its fold by
`2²⁵⁶ ≡ 38`: `δ k m`. -/
def δ (k m : ℕ) : ℤ := (if m = k then 1 else 0) + (if m = k + 8 then 38 else 0)

/-- `Σ_l 2^(32l)·v l`, an 8-limb number. -/
def num {R : Type*} [CommSemiring R] (v : ℕ → R) : R := ∑ l ∈ range 8, 2 ^ (32 * l) * v l

/-- Column `k` of `a·b` folded modulo `X⁸ − 38`. -/
def fold {R : Type*} [CommRing R] (a b : ℕ → R) (k : ℕ) : R :=
  ∑ l ∈ range 8, ∑ l' ∈ range 8, (δ k (l + l') : R) * (a l * b l')

theorem map_fold {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : ℕ → R) (k : ℕ) :
    f (fold a b k) = fold (fun l => f (a l)) (fun l => f (b l)) k := by
  simp [fold, map_sum]

theorem coef_dvd : ∀ m < 15,
    (2 ^ 256 - 38 : ℤ) ∣ 2 ^ (32 * m) - ∑ k ∈ range 8, 2 ^ (32 * k) * δ k m := by
  decide +kernel

/-- `a·b ≡ Σ 2^(32k)·fold k (mod 2²⁵⁶ − 38 = 2p)`. -/
theorem fold_dvd (a b : ℕ → ℤ) : (2 ^ 256 - 38 : ℤ) ∣ num a * num b - num (fold a b) := by
  have e1 : num a * num b = ∑ l ∈ range 8, ∑ l' ∈ range 8, 2 ^ (32 * (l + l')) * (a l * b l') := by
    rw [num, num, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [mul_add, pow_add]; ring
  have e2 : num (fold a b) = ∑ l ∈ range 8, ∑ l' ∈ range 8,
      (∑ k ∈ range 8, 2 ^ (32 * k) * δ k (l + l')) * (a l * b l') := by
    simp only [num, fold, Finset.mul_sum, Int.cast_id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun l hl => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun l' hl' => ?_
  rw [← sub_mul]
  exact dvd_mul_of_dvd_left (coef_dvd _ (by simp at hl hl'; omega)) _

theorem δ_nonneg (k m : ℕ) : 0 ≤ δ k m := by unfold δ; split_ifs <;> norm_num

theorem δ_sum : ∀ k < 8, ∑ l ∈ range 8, ∑ l' ∈ range 8, δ k (l + l') ≤ 267 := by decide

/-- A column of the fold of limbs in `[0, 2³⁶)` is in `[0, 267·2⁷²]`. -/
theorem fold_bounds (a b : ℕ → ℤ) (ha : ∀ l < 8, 0 ≤ a l ∧ a l < 2 ^ 36)
    (hb : ∀ l < 8, 0 ≤ b l ∧ b l < 2 ^ 36) (k : ℕ) (hk : k < 8) :
    0 ≤ fold a b k ∧ fold a b k ≤ 267 * 2 ^ 72 := by
  have hp : ∀ l ∈ range 8, ∀ l' ∈ range 8, 0 ≤ a l * b l' ∧ a l * b l' < 2 ^ 72 :=
    fun l hl l' hl' => by
      rw [Finset.mem_range] at hl hl'
      obtain ⟨h1, h2⟩ := ha l hl; obtain ⟨h3, h4⟩ := hb l' hl'
      exact ⟨mul_nonneg h1 h3, by nlinarith⟩
  refine ⟨Finset.sum_nonneg fun l hl => Finset.sum_nonneg fun l' hl' =>
    mul_nonneg (δ_nonneg _ _) (hp l hl l' hl').1, ?_⟩
  calc fold a b k ≤ ∑ l ∈ range 8, ∑ l' ∈ range 8, δ k (l + l') * 2 ^ 72 := by
        refine Finset.sum_le_sum fun l hl => Finset.sum_le_sum fun l' hl' => ?_
        exact mul_le_mul_of_nonneg_left (hp l hl l' hl').2.le (δ_nonneg _ _)
    _ = (∑ l ∈ range 8, ∑ l' ∈ range 8, δ k (l + l')) * 2 ^ 72 := by
        simp [Finset.sum_mul]
    _ ≤ 267 * 2 ^ 72 := by
        have := δ_sum k hk; nlinarith

/-- The interpolation matrix: `Σ_j M k j · jᵐ = δ k m` for every product limb `m < 15`. -/
theorem M_inv : ∀ k < 8, ∀ m < 15,
    ∑ j ∈ range 15, M k j * (j : F) ^ m = ((δ k m : ℤ) : F) := by decide +kernel

/-- The limb polynomial at `j`. -/
def ev (v : ℕ → F) (j : ℕ) : F := ∑ l ∈ range 8, (j : F) ^ l * v l

/-- The 15 products at the points recover the folded columns. -/
theorem crt (a b : ℕ → F) (k : ℕ) (hk : k < 8) :
    ∑ j ∈ range 15, M k j * (ev a j * ev b j) = fold a b k := by
  have hp : ∀ j : ℕ, ev a j * ev b j =
      ∑ l ∈ range 8, ∑ l' ∈ range 8, (j : F) ^ (l + l') * (a l * b l') := by
    intro j
    rw [ev, ev, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [pow_add]; ring
  simp only [hp, fold, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' hl' => ?_
  simp at hl hl'
  rw [← M_inv k hk (l + l') (by omega), Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]; ring

/-! ### The rows' meaning -/

open Xark.Templates.Add32 (sum_map_range)

/-- `Σ cᵢ·σ vᵢ` over a term list. -/
def tsum (ts : List (F × TVar)) (σ : TVar → F) : F := (ts.map fun t => t.1 * σ t.2).sum

theorem tsum_append (a b : List (F × TVar)) (σ : TVar → F) :
    tsum (a ++ b) σ = tsum a σ + tsum b σ := by simp [tsum]

theorem tsum_scale (c : F) (ts : List (F × TVar)) (σ : TVar → F) :
    tsum (scale c ts) σ = c * tsum ts σ := by
  simp only [tsum, scale, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]

theorem tsum_flatMap {α : Type*} (l : List α) (f : α → List (F × TVar)) (σ : TVar → F) :
    tsum (l.flatMap f) σ = (l.map fun x => tsum (f x) σ).sum := by
  induction l with
  | nil => simp [tsum]
  | cons x l ih => simp only [List.flatMap_cons, tsum_append, ih, List.map_cons, List.sum_cons]

theorem tsum_range_flatMap (n : ℕ) (f : ℕ → List (F × TVar)) (σ : TVar → F) :
    tsum ((List.range n).flatMap f) σ = ∑ j ∈ range n, tsum (f j) σ := by
  rw [tsum_flatMap, sum_map_range]

/-- Plug vector at offset `o` (`a₁ = 0`, `b₁ = 8`, `a₂ = 16`, `b₂ = 24`, `a₃ = 32`,
`b₃ = 40`, `t = 48`). -/
def pv (σ : TVar → F) (o : ℕ) : ℕ → F := fun l => σ (.plug (o + l))

theorem eval_aLC (i j : ℕ) (σ : TVar → F) : (aLC i j).eval σ = ev (pv σ (ao i)) j := by
  rw [aLC, eval_norm]
  simp only [LC.eval, evT, List.map_map, Function.comp_def, sum_map_range, ev, pv, zero_add]
  push_cast; rfl

theorem eval_bLC (i j : ℕ) (σ : TVar → F) : (bLC i j).eval σ = ev (pv σ (bo i)) j := by
  rw [bLC, eval_norm]
  simp only [LC.eval, evT, List.map_map, Function.comp_def, sum_map_range, ev, pv, zero_add]
  push_cast; rfl

/-- `Σ_j M k j·(P₀ⱼ − P₁ⱼ − P₂ⱼ)`, column `k` read from the products. -/
def dv (k : ℕ) (σ : TVar → F) : F :=
  ∑ j ∈ range 15, M k j * (σ (.wit (3 * j)) - σ (.wit (3 * j + 1)) - σ (.wit (3 * j + 2)))

theorem tsum_dT (k : ℕ) (σ : TVar → F) : tsum (dT k) σ = dv k σ := by
  rw [dT, tsum_range_flatMap, dv]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [tsum, List.range_succ, sg]; ring

/-- `Σ_{k<4} 2^(32k)·(d_{o+k} − t_{o+k})`. -/
def hv (o : ℕ) (σ : TVar → F) : F :=
  ∑ k ∈ range 4, 2 ^ (32 * k) * (dv (o + k) σ - σ (.plug (48 + o + k)))

theorem tsum_halfT (o : ℕ) (σ : TVar → F) : tsum (halfT o) σ = hv o σ := by
  rw [halfT, tsum_range_flatMap, hv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_append, tsum_scale, tsum_dT]
  simp [tsum]; ring

theorem eval_kLC (σ : TVar → F) : kLC.eval σ = σ (.wit 45) - 2 ^ 51 := by
  simp [kLC, LC.eval]; ring

theorem eval_tLC (σ : TVar → F) : tLC.eval σ = 2 ^ 127 * (σ (.wit 45) - 2 ^ 52) - hv 4 σ + 2 ^ 50 := by
  rw [tLC, eval_norm, LC.eval, ← tsum, tTerms, tsum_append, tsum_scale, tsum_halfT]
  simp [tsum]; ring

theorem eval_eLC (σ : TVar → F) : eLC.eval σ =
    hv 0 σ + 19 * (σ (.wit 45) - 2 ^ 52) - 2 ^ 128 * (2 ^ 127 * (σ (.wit 45) - 2 ^ 52) - hv 4 σ) := by
  rw [eLC, eval_norm, LC.eval, ← tsum, tsum_append, tsum_append, tsum_scale, tTerms, tsum_append,
    tsum_scale, tsum_halfT, tsum_halfT]
  simp [tsum]; ring

theorem sat_rows (σ : TVar → F) : Xark.R1cs.Sat rows σ ↔
    (∀ j < 15, ∀ i < 3, (aLC i j).eval σ * (bLC i j).eval σ = σ (.wit (3 * j + i))) ∧
      Xark.R1cs.Sat (bitRows kLC 47 51) σ ∧ Xark.R1cs.Sat (bitRows tLC 98 50) σ ∧
      eLC.eval σ = 0 := by
  simp only [Xark.R1cs.Sat, rows, prodRows, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range, List.mem_singleton]
  constructor
  · intro h
    refine ⟨fun j hj i hi => ?_, fun r hr => h r (Or.inl (Or.inl (Or.inr hr))),
      fun r hr => h r (Or.inl (Or.inr hr)), ?_⟩
    · simpa [Row.Sat, LC.eval, LC.var] using h _ (Or.inl (Or.inl (Or.inl ⟨j, hj, i, hi, rfl⟩)))
    · simpa [Row.Sat, LC.eval] using h _ (Or.inr rfl)
  · rintro ⟨hp, hk, ht, he⟩ row ((((⟨j, hj, i, hi, rfl⟩ | hr) | hr) | rfl))
    · simpa [Row.Sat, LC.eval, LC.var] using hp j hj i hi
    · exact hk _ hr
    · exact ht _ hr
    · simpa [Row.Sat, LC.eval] using he

/-- With the product rows holding, `dv k` is column `k` of `a₁b₁ − a₂b₂ − a₃b₃` folded. -/
theorem dv_fold (σ : TVar → F)
    (hp : ∀ j < 15, ∀ i < 3, (aLC i j).eval σ * (bLC i j).eval σ = σ (.wit (3 * j + i)))
    (k : ℕ) (hk : k < 8) :
    dv k σ = fold (pv σ 0) (pv σ 8) k - fold (pv σ 16) (pv σ 24) k - fold (pv σ 32) (pv σ 40) k := by
  rw [← crt _ _ k hk, ← crt _ _ k hk, ← crt _ _ k hk, dv, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have h0 := hp j hj 0 (by norm_num)
  rw [add_zero] at h0
  rw [← h0, ← hp j hj 1 (by norm_num), ← hp j hj 2 (by norm_num)]
  simp only [eval_aLC, eval_bLC, ao, bo]
  ring

/-! ### Integer content -/

/-- `Σ_{k<4} 2^(32k)·(D_{o+k} − t_{o+k})`: `L` at `o = 0`, `U` at `o = 4`. -/
def hz (D t : ℕ → ℤ) (o : ℕ) : ℤ := ∑ k ∈ range 4, 2 ^ (32 * k) * (D (o + k) - t (o + k))

theorem num_split (D t : ℕ → ℤ) : num (fun k => D k - t k) = hz D t 0 + 2 ^ 128 * hz D t 4 := by
  simp only [num, hz, Finset.sum_range_succ, Finset.sum_range_zero]; ring

/-- `L` and `U` of columns in `[−534·2⁷², 267·2⁷²]` and `t` limbs below `2³⁶`. -/
theorem hz_bounds (D t : ℕ → ℤ) (hD : ∀ k < 8, -(534 * 2 ^ 72) ≤ D k ∧ D k ≤ 267 * 2 ^ 72)
    (ht : ∀ k < 8, 0 ≤ t k ∧ t k < 2 ^ 36) (o : ℕ) (ho : o ≤ 4) :
    -(536 * 2 ^ 168) ≤ hz D t o ∧ hz D t o ≤ 536 * 2 ^ 168 := by
  obtain ⟨_, _⟩ := hD o (by omega); obtain ⟨_, _⟩ := hD (o + 1) (by omega)
  obtain ⟨_, _⟩ := hD (o + 2) (by omega); obtain ⟨_, _⟩ := hD (o + 3) (by omega)
  obtain ⟨_, _⟩ := ht o (by omega); obtain ⟨_, _⟩ := ht (o + 1) (by omega)
  obtain ⟨_, _⟩ := ht (o + 2) (by omega); obtain ⟨_, _⟩ := ht (o + 3) (by omega)
  simp only [hz, Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
  constructor <;> norm_num <;> linarith

open Xark.Templates.MulCertK1 (lift r_eq)

/-- The certificate's integer content: the closing row and `T = 2¹²⁷·K − U`, holding in
`Fr` with every quantity bounded, hold over `ℤ`, so `Σ 2^(32k)·(D_k − t_k) = p·K`. -/
theorem int_core (D t : ℕ → ℤ) (K T : ℤ)
    (hD : ∀ k < 8, -(534 * 2 ^ 72) ≤ D k ∧ D k ≤ 267 * 2 ^ 72)
    (ht : ∀ k < 8, 0 ≤ t k ∧ t k < 2 ^ 36) (hK : 0 ≤ K ∧ K < 2 ^ 52) (hT : 0 ≤ T ∧ T < 2 ^ 51)
    (h1 : ((hz D t 0 + 19 * (K - 2 ^ 51) - 2 ^ 128 * (T - 2 ^ 50) : ℤ) : F) = 0)
    (h2 : ((T - 2 ^ 50 - (2 ^ 127 * (K - 2 ^ 51) - hz D t 4) : ℤ) : F) = 0) :
    num (fun k => D k - t k) = (2 ^ 255 - 19) * (K - 2 ^ 51) := by
  obtain ⟨_, _⟩ := hz_bounds D t hD ht 0 (by norm_num)
  obtain ⟨_, _⟩ := hz_bounds D t hD ht 4 (by norm_num)
  have e1 := lift _ h1 (by rw [r_eq]; omega) (by rw [r_eq]; omega)
  have e2 := lift _ h2 (by rw [r_eq]; omega) (by rw [r_eq]; omega)
  rw [num_split]
  linear_combination e1 + 2 ^ 128 * e2

/-! ### Soundness -/

-- The generated constant obligations unfold `IsBit` too (`add32`'s assumption).
export Xark.Templates.Add32 (IsBit)

open Xark.Templates.MulCertK1 (bits_sound)

/-- The input assumption: every limb of the seven operands is below `2³⁶`. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, v.val < 2 ^ 36

/-- Limb `l` of the operand at plug offset `o`, as a natural. -/
def limb (ins : List F) (o l : ℕ) : ℕ := (ins.getD (o + l) 0).val

/-- The operand at offset `o` in `ZMod p`. -/
def X (ins : List F) (o : ℕ) : Xark.Ed25519.Fp := num fun l => ((limb ins o l : ℕ) : Xark.Ed25519.Fp)

/-- `a₁·b₁ − a₂·b₂ − a₃·b₃ ≡ t (mod p)`, the operands read as 8-limb numbers in base `2³²`. -/
def Spec (ins : List F) : Prop :=
  X ins 0 * X ins 8 - X ins 16 * X ins 24 - X ins 32 * X ins 40 = X ins 48

theorem ins_eq (σ : TVar → F) : template.ins σ = (List.range 56).map fun j => σ (.plug j) := by
  simp [Template.ins, inputs_eq]

theorem getD_ins (σ : TVar → F) (j : ℕ) (hj : j < 56) : (template.ins σ).getD j 0 = σ (.plug j) := by
  rw [ins_eq, List.getD_eq_getElem _ _ (by simpa using hj)]; simp

/-- Plug vector `o` as integers. -/
def zv (σ : TVar → F) (o : ℕ) : ℕ → ℤ := fun l => ((σ (.plug (o + l))).val : ℤ)

/-- Column `k` of `a₁b₁ − a₂b₂ − a₃b₃` over the integers. -/
def Dz (σ : TVar → F) (k : ℕ) : ℤ :=
  fold (zv σ 0) (zv σ 8) k - fold (zv σ 16) (zv σ 24) k - fold (zv σ 32) (zv σ 40) k

theorem zv_cast (σ : TVar → F) (o : ℕ) : (fun l => ((zv σ o l : ℤ) : F)) = pv σ o := by
  funext l; simp [zv, pv]

theorem Dz_cast (σ : TVar → F)
    (hp : ∀ j < 15, ∀ i < 3, (aLC i j).eval σ * (bLC i j).eval σ = σ (.wit (3 * j + i)))
    (k : ℕ) (hk : k < 8) : ((Dz σ k : ℤ) : F) = dv k σ := by
  rw [dv_fold σ hp k hk, Dz]
  have e := fun a b => map_fold (Int.castRingHom F) a b k
  simp only [eq_intCast] at e
  push_cast
  rw [e, e, e, zv_cast, zv_cast, zv_cast, zv_cast, zv_cast, zv_cast]

theorem hz_cast (σ : TVar → F)
    (hp : ∀ j < 15, ∀ i < 3, (aLC i j).eval σ * (bLC i j).eval σ = σ (.wit (3 * j + i)))
    (o : ℕ) (ho : o ≤ 4) : ((hz (Dz σ) (zv σ 48) o : ℤ) : F) = hv o σ := by
  simp only [hz, hv]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [Dz_cast σ hp _ (by omega)]
  simp [zv, add_assoc]

/-- The plugs' bounds give the columns' bounds. -/
theorem Dz_bounds (σ : TVar → F) (hpl : ∀ j < 56, (σ (.plug j)).val < 2 ^ 36) :
    ∀ k < 8, -(534 * 2 ^ 72) ≤ Dz σ k ∧ Dz σ k ≤ 267 * 2 ^ 72 := by
  intro k hk
  have hz : ∀ o, o ≤ 48 → ∀ l < 8, 0 ≤ zv σ o l ∧ zv σ o l < 2 ^ 36 := fun o ho l hl =>
    ⟨Int.natCast_nonneg _, by simp only [zv]; exact_mod_cast hpl (o + l) (by omega)⟩
  obtain ⟨_, _⟩ := fold_bounds _ _ (hz 0 (by norm_num)) (hz 8 (by norm_num)) k hk
  obtain ⟨_, _⟩ := fold_bounds _ _ (hz 16 (by norm_num)) (hz 24 (by norm_num)) k hk
  obtain ⟨_, _⟩ := fold_bounds _ _ (hz 32 (by norm_num)) (hz 40 (by norm_num)) k hk
  simp only [Dz]
  constructor <;> linarith

theorem p_int : ((Xark.Ed25519.p : ℕ) : ℤ) = 2 ^ 255 - 19 := by
  change ((57896044618658097711785492504343953926634992332820282019728792003956564819949 : ℕ) : ℤ) = _
  norm_num

/-- `Spec` is divisibility of the integer `a₁b₁ − a₂b₂ − a₃b₃ − t` by `p`, and so of the
folded columns' `Σ 2^(32k)·(D_k − t_k)`. -/
theorem spec_iff (σ : TVar → F) :
    Spec (template.ins σ) ↔ (2 ^ 255 - 19 : ℤ) ∣ num (fun k => Dz σ k - zv σ 48 k) := by
  have g : ∀ o l, o + l < 56 → limb (template.ins σ) o l = (σ (.plug (o + l))).val :=
    fun o l h => by rw [limb, getD_ins σ _ h]
  have hX : ∀ o ≤ 48, X (template.ins σ) o = ((num (zv σ o) : ℤ) : Xark.Ed25519.Fp) := by
    intro o ho
    simp only [X, num]
    push_cast
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [Finset.mem_range] at hl
    rw [g o l (by omega)]; simp [zv]
  obtain ⟨w1, hw1⟩ := fold_dvd (zv σ 0) (zv σ 8)
  obtain ⟨w2, hw2⟩ := fold_dvd (zv σ 16) (zv σ 24)
  obtain ⟨w3, hw3⟩ := fold_dvd (zv σ 32) (zv σ 40)
  have hlin : num (fun k => Dz σ k - zv σ 48 k) = num (fold (zv σ 0) (zv σ 8)) -
      num (fold (zv σ 16) (zv σ 24)) - num (fold (zv σ 32) (zv σ 40)) - num (zv σ 48) := by
    simp only [num, Dz, mul_sub, Finset.sum_sub_distrib]
  rw [Spec, hX 0 (by norm_num), hX 8 (by norm_num), hX 16 (by norm_num), hX 24 (by norm_num),
    hX 32 (by norm_num), hX 40 (by norm_num), hX 48 (by norm_num), ← sub_eq_zero]
  simp only [← Int.cast_mul, ← Int.cast_sub]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, p_int, hlin]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c - 2 * w1 + 2 * w2 + 2 * w3, by linear_combination hc - hw1 + hw2 + hw3⟩
  · rintro ⟨c, hc⟩
    exact ⟨c + 2 * w1 - 2 * w2 - 2 * w3, by linear_combination hc + hw1 - hw2 - hw3⟩

/-- **Soundness.** If every limb of the operands is below `2³⁶`, every assignment
satisfying the exported rows has `a₁·b₁ − a₂·b₂ − a₃·b₃ ≡ t (mod p)`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  rw [Template.Sat, rows_eq, sat_rows] at h
  obtain ⟨hp, hk, ht, he⟩ := h
  have hK := bits_sound kLC 47 51 (by norm_num) σ hk
  have hT := bits_sound tLC 98 50 (by norm_num) σ ht
  have hpl : ∀ j < 56, (σ (.plug j)).val < 2 ^ 36 := fun j hj =>
    ha _ (by rw [ins_eq]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have hKc : (((kLC.eval σ).val : ℕ) : F) = σ (.wit 45) - 2 ^ 51 := by
    rw [ZMod.natCast_zmod_val, eval_kLC]
  have hTc : (((tLC.eval σ).val : ℕ) : F) = 2 ^ 127 * (σ (.wit 45) - 2 ^ 52) - hv 4 σ + 2 ^ 50 := by
    rw [ZMod.natCast_zmod_val, eval_tLC]
  rw [eval_eLC] at he
  have core := int_core (Dz σ) (zv σ 48) _ _ (Dz_bounds σ hpl)
    (fun k hk => ⟨Int.natCast_nonneg _, by simp only [zv]; exact_mod_cast hpl (48 + k) (by omega)⟩)
    ⟨Int.natCast_nonneg _, by exact_mod_cast hK⟩ ⟨Int.natCast_nonneg _, by exact_mod_cast hT⟩
    (by
      push_cast
      rw [hz_cast σ hp 0 (by norm_num), hKc, hTc]
      linear_combination he)
    (by
      push_cast
      rw [hz_cast σ hp 4 (by norm_num), hKc, hTc]
      ring)
  exact (spec_iff σ).mpr ⟨_, core⟩

end Xark.Templates.MulCert25519
