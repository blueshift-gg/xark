/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Pratt

set_option linter.style.header false

/-!
# Primality of the Ed25519 constants

Pratt certificates (`Formal/Pratt.lean`) for the Ed25519 base prime `p = 2²⁵⁵ − 19` and
group order `L = 2²⁵² + 27742317777372353535851937790883648493`, generated like
`Formal/CurvePrimes.lean`s from the factorizations of `q − 1` (recursively for factors above
`2²⁴`; smaller ones by `norm_num`). Checked by the kernel — no `native_decide`.
-/

set_option linter.style.longLine false

namespace Pratt

set_option maxRecDepth 100000 in
theorem prime_31757755568855353 : Nat.Prime 31757755568855353 :=
  prime_of_certificate 31757755568855353 10
    [(2, 3), (3, 1), (31, 1), (107, 1), (223, 1), (4153, 1), (430751, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_2773320623 : Nat.Prime 2773320623 :=
  prime_of_certificate 2773320623 5
    [(2, 1), (2437, 1), (569003, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_72106336199 : Nat.Prime 72106336199 :=
  prime_of_certificate 72106336199 7
    [(2, 1), (13, 1), (2773320623, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, prime_2773320623⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_1919519569386763 : Nat.Prime 1919519569386763 :=
  prime_of_certificate 1919519569386763 2
    [(2, 1), (3, 1), (7, 1), (19, 1), (47, 2), (127, 1), (8574133, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_75445702479781427272750846543864801 : Nat.Prime 75445702479781427272750846543864801 :=
  prime_of_certificate 75445702479781427272750846543864801 7
    [(2, 5), (3, 2), (5, 2), (75707, 1), (72106336199, 1), (1919519569386763, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_72106336199, prime_1919519569386763⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 : Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 :=
  prime_of_certificate 74058212732561358302231226437062788676166966415465897661863160754340907 2
    [(2, 1), (3, 1), (353, 1), (57467, 1), (132049, 1), (1923133, 1), (31757755568855353, 1), (75445702479781427272750846543864801, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_31757755568855353, prime_75445702479781427272750846543864801⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_57896044618658097711785492504343953926634992332820282019728792003956564819949 : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 :=
  prime_of_certificate 57896044618658097711785492504343953926634992332820282019728792003956564819949 2
    [(2, 2), (3, 1), (65147, 1), (74058212732561358302231226437062788676166966415465897661863160754340907, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_74058212732561358302231226437062788676166966415465897661863160754340907⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_58964693 : Nat.Prime 58964693 :=
  prime_of_certificate 58964693 2
    [(2, 2), (14741173, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_3044861653679985063343 : Nat.Prime 3044861653679985063343 :=
  prime_of_certificate 3044861653679985063343 5
    [(2, 1), (3, 1), (11, 1), (30703, 1), (82163, 1), (132667, 1), (137849, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_198211423230930754013084525763697 : Nat.Prime 198211423230930754013084525763697 :=
  prime_of_certificate 198211423230930754013084525763697 5
    [(2, 4), (3, 1), (23, 1), (58964693, 1), (3044861653679985063343, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_58964693, prime_3044861653679985063343⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_292386187 : Nat.Prime 292386187 :=
  prime_of_certificate 292386187 2
    [(2, 1), (3, 4), (307, 1), (5879, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_213441916511 : Nat.Prime 213441916511 :=
  prime_of_certificate 213441916511 13
    [(2, 1), (5, 1), (73, 1), (292386187, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_292386187⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_1257559732178653 : Nat.Prime 1257559732178653 :=
  prime_of_certificate 1257559732178653 2
    [(2, 2), (3, 1), (7, 1), (23, 1), (531581, 1), (1224481, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_4434155615661930479 : Nat.Prime 4434155615661930479 :=
  prime_of_certificate 4434155615661930479 17
    [(2, 1), (41, 1), (43, 1), (1257559732178653, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_1257559732178653⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_172054593956031949258510691 : Nat.Prime 172054593956031949258510691 :=
  prime_of_certificate 172054593956031949258510691 2
    [(2, 1), (5, 1), (1361, 1), (2851, 1), (4434155615661930479, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_4434155615661930479⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_19757330305831588566944191468367130476339 : Nat.Prime 19757330305831588566944191468367130476339 :=
  prime_of_certificate 19757330305831588566944191468367130476339 2
    [(2, 1), (269, 1), (213441916511, 1), (172054593956031949258510691, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, prime_213441916511, prime_172054593956031949258510691⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_276602624281642239937218680557139826668747 : Nat.Prime 276602624281642239937218680557139826668747 :=
  prime_of_certificate 276602624281642239937218680557139826668747 2
    [(2, 1), (7, 1), (19757330305831588566944191468367130476339, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, prime_19757330305831588566944191468367130476339⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_7237005577332262213973186563042994240857116359379907606001950938285454250989 : Nat.Prime 7237005577332262213973186563042994240857116359379907606001950938285454250989 :=
  prime_of_certificate 7237005577332262213973186563042994240857116359379907606001950938285454250989 2
    [(2, 2), (3, 1), (11, 1), (198211423230930754013084525763697, 1), (276602624281642239937218680557139826668747, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, prime_198211423230930754013084525763697, prime_276602624281642239937218680557139826668747⟩
    (by decide) (by decide)

end Pratt
