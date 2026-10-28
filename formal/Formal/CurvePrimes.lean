import Formal.Pratt

/-!
# Primality of the curve constants

Pratt certificates (`Formal/Pratt.lean`) for the BN254 scalar prime and the secp256k1 /
secp256r1 base primes, replacing the trusted primality axioms. Generated from the
factorizations of `p - 1` (recursively for factors above `2^24`; smaller ones by
`norm_num`). Checked by the kernel — no `native_decide`.
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

end Pratt
