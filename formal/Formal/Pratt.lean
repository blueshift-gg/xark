import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Tactic.NormNum.Prime

/-!
# Pratt certificates

Primality of large constants (the BN254, secp256k1 and secp256r1 field primes) from
Lucas' theorem (`lucas_primality`): `p` is prime if some `a` has `a^(p-1) ≡ 1` and
`a^((p-1)/q) ≢ 1` for every prime `q ∣ p - 1`. The prime factorization of `p - 1`
is given as a list; its large factors are proven prime the same way, small ones by
`norm_num`. The modular powers are computed by square-and-multiply (`powMod`) and
checked by the kernel (`decide`) — no `native_decide`, so no axioms beyond the
standard three.
-/

namespace Pratt

/-- Square-and-multiply: `acc · b^e mod m`, structural on `fuel` (enough for
`e < 2^fuel`). -/
def powModAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
    if e = 0 then acc
    else powModAux m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

/-- `a^e mod m` (for `e < 2^256`). -/
def powMod (a e m : ℕ) : ℕ := powModAux m 256 (a % m) e (1 % m)

theorem powModAux_modEq (m : ℕ) :
    ∀ (fuel b e acc : ℕ), e < 2 ^ fuel → powModAux m fuel b e acc ≡ acc * b ^ e [MOD m] := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e acc he
    have : e = 0 := by simpa using he
    subst this
    simp only [powModAux, pow_zero, mul_one]
    exact Nat.ModEq.refl _
  | succ fuel ih =>
    intro b e acc he
    by_cases h0 : e = 0
    · subst h0
      simp only [powModAux, pow_zero, mul_one, if_true]
      exact Nat.ModEq.refl _
    · have he2 : e / 2 < 2 ^ fuel := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        rw [pow_succ] at he
        exact he
      simp only [powModAux, h0, if_false]
      refine (ih _ _ _ he2).trans ?_
      have hsq : (b * b % m) ^ (e / 2) ≡ (b * b) ^ (e / 2) [MOD m] :=
        (Nat.mod_modEq _ _).pow _
      have hsplit : b ^ e = b ^ (e % 2) * (b * b) ^ (e / 2) := by
        rw [← pow_two, ← pow_mul, ← pow_add, Nat.mod_add_div e 2]
      rw [hsplit]
      split_ifs with hodd
      · rw [hodd, pow_one, ← mul_assoc]
        exact ((Nat.mod_modEq _ _).mul hsq)
      · have : e % 2 = 0 := by omega
        rw [this, pow_zero, one_mul]
        exact (Nat.ModEq.refl acc).mul hsq

/-- `powMod` is `a^e` in `ZMod m`. -/
theorem powMod_cast (a e m : ℕ) (he : e < 2 ^ 256) :
    ((powMod a e m : ℕ) : ZMod m) = (a : ZMod m) ^ e := by
  have h := powModAux_modEq m 256 (a % m) e (1 % m) he
  have h2 : 1 % m * (a % m) ^ e ≡ a ^ e [MOD m] := by
    have := ((Nat.mod_modEq 1 m).mul ((Nat.mod_modEq a m).pow e))
    simpa using this
  rw [← Nat.cast_pow]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (h.trans h2)

/-- Every prime divisor of `(L.map (·.1 ^ ·.2)).prod` is some `x.1` with `x ∈ L`,
when each `x.1` is prime. -/
theorem prime_dvd_of_factorization {q : ℕ} (hq : q.Prime) (L : List (ℕ × ℕ))
    (hpr : ∀ x ∈ L, x.1.Prime) (hdvd : q ∣ (L.map fun x => x.1 ^ x.2).prod) :
    ∃ x ∈ L, x.1 = q := by
  obtain ⟨y, hy, hqy⟩ := (Prime.dvd_prod_iff hq.prime).mp hdvd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have hq1 : q ∣ x.1 := hq.prime.dvd_of_dvd_pow hqy
  refine ⟨x, hx, ?_⟩
  rcases (hpr x hx).eq_one_or_self_of_dvd q hq1 with h | h
  · exact absurd h hq.one_lt.ne'
  · exact h.symm

/-- A Pratt certificate: `p - 1 = ∏ qᵢ^eᵢ` over primes `qᵢ`, and a witness `a` of
order exactly `p - 1` mod `p`. -/
theorem prime_of_certificate (p a : ℕ) (L : List (ℕ × ℕ)) (hp : 2 ≤ p)
    (hbits : p < 2 ^ 256)
    (hL : (L.map fun x => x.1 ^ x.2).prod = p - 1)
    (hpr : L.Forall fun x => x.1.Prime)
    (h1 : powMod a (p - 1) p % p = 1)
    (h2 : ∀ x ∈ L, powMod a ((p - 1) / x.1) p % p ≠ 1) : p.Prime := by
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · rw [← powMod_cast a (p - 1) p (by omega)]
    have := (ZMod.natCast_eq_natCast_iff' (powMod a (p - 1) p) 1 p).mpr (by rw [h1, h1p])
    simpa using this
  · intro q hq hqd
    obtain ⟨x, hx, rfl⟩ :=
      prime_dvd_of_factorization hq L (List.forall_iff_forall_mem.mp hpr) (hL ▸ hqd)
    rw [← powMod_cast a _ p (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
    intro hc
    apply h2 x hx
    have := (ZMod.natCast_eq_natCast_iff' (powMod a ((p - 1) / x.1) p) 1 p).mp (by simpa using hc)
    rwa [h1p] at this

/-- Sanity check of the machinery on a small prime (`65537 - 1 = 2^16`). -/
example : Nat.Prime 65537 :=
  prime_of_certificate 65537 3 [(2, 16)] (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide)
    (by decide)

end Pratt
