import Formal.Pratt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

/-!
# Primality of the curve constants

Pratt certificates (`Formal/Pratt.lean`) for the BN254 scalar prime, the secp256k1 /
secp256r1 base primes and the secp256k1 and secp256r1 group orders `n`, replacing the
trusted primality axioms. Generated from the factorizations of `p - 1` (recursively for
factors above `2^24`; smaller ones by `norm_num`). Checked by the kernel — no `native_decide`.
-/

-- The certificates' numerals are up to 78 digits.
set_option linter.style.longLine false

namespace Pratt

set_option maxRecDepth 100000 in
theorem prime_405928799 : Nat.Prime 405928799 :=
  prime_of_certificate 405928799 22
    [(2, 1), (11, 1), (4999, 1), (3691, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_12048837557 : Nat.Prime 12048837557 :=
  prime_of_certificate 12048837557 2
    [(2, 2), (7, 2), (661, 1), (93001, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_5156902474397 : Nat.Prime 5156902474397 :=
  prime_of_certificate 5156902474397 2
    [(2, 2), (107, 1), (12048837557, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, prime_12048837557⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_1670836401704629 : Nat.Prime 1670836401704629 :=
  prime_of_certificate 1670836401704629 2
    [(2, 2), (3, 4), (5156902474397, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, prime_5156902474397⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_639533339 : Nat.Prime 639533339 :=
  prime_of_certificate 639533339 2
    [(2, 1), (229, 1), (853, 1), (1637, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_65865678001877903 : Nat.Prime 65865678001877903 :=
  prime_of_certificate 65865678001877903 5
    [(2, 1), (83, 1), (379, 1), (1637, 1), (639533339, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_639533339⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 :=
  prime_of_certificate 13818364434197438864469338081 3
    [(2, 5), (5, 1), (823, 1), (1593227, 1), (65865678001877903, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_65865678001877903⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_21888242871839275222246405745257275088548364400416034343698204186575808495617 : Nat.Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617 :=
  prime_of_certificate 21888242871839275222246405745257275088548364400416034343698204186575808495617 5
    [(2, 28), (3, 2), (13, 1), (29, 1), (983, 1), (237073, 1), (11003, 1), (405928799, 1), (1670836401704629, 1), (13818364434197438864469338081, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_405928799, prime_1670836401704629, prime_13818364434197438864469338081⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_173378833005251801 : Nat.Prime 173378833005251801 :=
  prime_of_certificate 173378833005251801 6
    [(2, 3), (5, 2), (2621, 1), (24809, 1), (13331831, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_22149492674086928081353 : Nat.Prime 22149492674086928081353 :=
  prime_of_certificate 22149492674086928081353 5
    [(2, 3), (3, 1), (5323, 1), (173378833005251801, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_173378833005251801⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_132896956044521568488119 : Nat.Prime 132896956044521568488119 :=
  prime_of_certificate 132896956044521568488119 6
    [(2, 1), (3, 1), (22149492674086928081353, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, prime_22149492674086928081353⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_107590001 : Nat.Prime 107590001 :=
  prime_of_certificate 107590001 3
    [(2, 4), (5, 4), (7, 1), (29, 1), (53, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_255515944373312847190720520512484175977 : Nat.Prime 255515944373312847190720520512484175977 :=
  prime_of_certificate 255515944373312847190720520512484175977 3
    [(2, 3), (7, 2), (11, 1), (1627, 1), (2657, 1), (4423, 1), (96557, 1), (41201, 1), (107590001, 1), (7240687, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_107590001, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_205115282021455665897114700593932402728804164701536103180137503955397371 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 :=
  prime_of_certificate 205115282021455665897114700593932402728804164701536103180137503955397371 10
    [(2, 1), (3, 1), (5, 1), (29, 2), (31, 1), (7723, 1), (132896956044521568488119, 1), (255515944373312847190720520512484175977, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_132896956044521568488119, prime_255515944373312847190720520512484175977⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_115792089237316195423570985008687907853269984665640564039457584007908834671663 : Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 :=
  prime_of_certificate 115792089237316195423570985008687907853269984665640564039457584007908834671663 3
    [(2, 1), (3, 1), (7, 1), (13441, 1), (205115282021455665897114700593932402728804164701536103180137503955397371, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_205115282021455665897114700593932402728804164701536103180137503955397371⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_66417393611 : Nat.Prime 66417393611 :=
  prime_of_certificate 66417393611 6
    [(2, 1), (5, 1), (53, 1), (173, 1), (197, 1), (3677, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_11290956913871 : Nat.Prime 11290956913871 :=
  prime_of_certificate 11290956913871 13
    [(2, 1), (5, 1), (17, 1), (66417393611, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_66417393611⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_204061199 : Nat.Prime 204061199 :=
  prime_of_certificate 204061199 11
    [(2, 1), (11, 1), (23, 1), (107, 1), (3769, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_34282281433 : Nat.Prime 34282281433 :=
  prime_of_certificate 34282281433 17
    [(2, 3), (3, 1), (7, 1), (204061199, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_204061199⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_46076956964474543 : Nat.Prime 46076956964474543 :=
  prime_of_certificate 46076956964474543 5
    [(2, 1), (23, 1), (18169, 1), (704251, 1), (78283, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_774023187263532362759620327192479577272145303 : Nat.Prime 774023187263532362759620327192479577272145303 :=
  prime_of_certificate 774023187263532362759620327192479577272145303 3
    [(2, 1), (3, 2), (2411, 1), (11290956913871, 1), (34282281433, 1), (46076956964474543, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_11290956913871, prime_34282281433, prime_46076956964474543⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_835945042244614951780389953367877943453916927241 : Nat.Prime 835945042244614951780389953367877943453916927241 :=
  prime_of_certificate 835945042244614951780389953367877943453916927241 11
    [(2, 3), (3, 3), (5, 1), (774023187263532362759620327192479577272145303, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_774023187263532362759620327192479577272145303⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_115792089210356248762697446949407573530086143415290314195533631308867097853951 : Nat.Prime 115792089210356248762697446949407573530086143415290314195533631308867097853951 :=
  prime_of_certificate 115792089210356248762697446949407573530086143415290314195533631308867097853951 6
    [(2, 1), (3, 1), (5, 2), (17, 1), (257, 1), (641, 1), (1531, 1), (65537, 1), (490463, 1), (6700417, 1), (835945042244614951780389953367877943453916927241, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_835945042244614951780389953367877943453916927241⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_107361793816595537 : Nat.Prime 107361793816595537 :=
  prime_of_certificate 107361793816595537 3
    [(2, 4), (16699, 1), (85831, 1), (4681609, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_44706919 : Nat.Prime 44706919 :=
  prime_of_certificate 44706919 6
    [(2, 1), (3, 1), (797, 1), (9349, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_174723607534414371449 : Nat.Prime 174723607534414371449 :=
  prime_of_certificate 174723607534414371449 3
    [(2, 3), (17, 1), (59, 1), (4051, 1), (120233, 1), (44706919, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_44706919⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_545358713 : Nat.Prime 545358713 :=
  prime_of_certificate 545358713 5
    [(2, 3), (41, 1), (59, 1), (28181, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_297159362677 : Nat.Prime 297159362677 :=
  prime_of_certificate 297159362677 2
    [(2, 2), (3, 2), (11, 1), (461, 1), (1627771, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_29047611873442575647497758179 : Nat.Prime 29047611873442575647497758179 :=
  prime_of_certificate 29047611873442575647497758179 2
    [(2, 1), (293, 1), (305873, 1), (545358713, 1), (297159362677, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_545358713, prime_297159362677⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_341948486974166000522343609283189 : Nat.Prime 341948486974166000522343609283189 :=
  prime_of_certificate 341948486974166000522343609283189 2
    [(2, 2), (3, 3), (109, 1), (29047611873442575647497758179, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_29047611873442575647497758179⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_115792089237316195423570985008687907852837564279074904382605163141518161494337 : Nat.Prime 115792089237316195423570985008687907852837564279074904382605163141518161494337 :=
  prime_of_certificate 115792089237316195423570985008687907852837564279074904382605163141518161494337 7
    [(2, 6), (3, 1), (149, 1), (631, 1), (107361793816595537, 1), (174723607534414371449, 1), (341948486974166000522343609283189, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_107361793816595537, prime_174723607534414371449, prime_341948486974166000522343609283189⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_187019741 : Nat.Prime 187019741 :=
  prime_of_certificate 187019741 2
    [(2, 2), (5, 1), (9350987, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_311245691 : Nat.Prime 311245691 :=
  prime_of_certificate 311245691 2
    [(2, 1), (5, 1), (7, 1), (17, 1), (29, 2), (311, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_622491383 : Nat.Prime 622491383 :=
  prime_of_certificate 622491383 5
    [(2, 1), (311245691, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, prime_311245691⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_1002328039319 : Nat.Prime 1002328039319 :=
  prime_of_certificate 1002328039319 19
    [(2, 1), (126241, 1), (3969899, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_191039911 : Nat.Prime 191039911 :=
  prime_of_certificate 191039911 3
    [(2, 1), (3, 1), (5, 1), (41, 1), (155317, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_208150935158385979 : Nat.Prime 208150935158385979 :=
  prime_of_certificate 208150935158385979 2
    [(2, 1), (3, 1), (11, 1), (43, 1), (127, 1), (3023, 1), (191039911, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_191039911⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_2624747550333869278416773953 : Nat.Prime 2624747550333869278416773953 :=
  prime_of_certificate 2624747550333869278416773953 7
    [(2, 6), (3, 2), (1297, 1), (16879, 1), (208150935158385979, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_208150935158385979⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_115792089210356248762697446949407573529996955224135760342422259061068512044369 : Nat.Prime 115792089210356248762697446949407573529996955224135760342422259061068512044369 :=
  prime_of_certificate 115792089210356248762697446949407573529996955224135760342422259061068512044369 7
    [(2, 4), (3, 1), (71, 1), (131, 1), (373, 1), (3407, 1), (17449, 1), (38189, 1), (187019741, 1), (622491383, 1), (1002328039319, 1), (2624747550333869278416773953, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_187019741, prime_622491383, prime_1002328039319, prime_2624747550333869278416773953⟩
    (by decide) (by decide)

end Pratt
