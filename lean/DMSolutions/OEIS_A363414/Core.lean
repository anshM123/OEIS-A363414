import Mathlib

/-!
# OEIS A363414: every prime divides some term

This file contains a verbatim copy of `OeisA363414.a` from `FormalConjectures/OEIS/363414.lean`
(formal-conjectures pull request 4946) and a proof that every prime `p` divides `a n` for some
`n > 0`: one can take `n = 3` for `p = 2` (`a 3 = -18`) and `n = p - 1` for odd `p`.

* `zp n = ∏_{k < n} (1 + 2 k i)` in `ℤ[i]`; its image in `ℂ` is the product in the definition of
  `a`, and `Im (zp n)` is even, so `2 * a n = Im (zp (n + 1))` (`two_mul_a`).
* `prod_reflect`: if `p = 0` in a commutative ring `R`, then
  `∏_{k < p} (1 + 2 k c) = ∏_{k < p} (1 - 2 k c)` for every `c : R` (substitute `k ↦ p - 1 - k`).
* With `R = ℤ[i] ⧸ (p)` and `c = i` this gives `zp p ≡ conj (zp p) (mod p)`, hence
  `p ∣ 2 Im (zp p) = 4 a (p - 1)` (`dvd_two_mul_im`). For odd `p` this gives `p ∣ a (p - 1)`.
-/

open Nat Finset Complex Real Filter Asymptotics ZMod Int

namespace A363414Core

/--
$a(n) = \frac{1}{2} \operatorname{Im}\left( \prod_{k=0}^n (1 + 2k i) \right)$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Complex :=
    Finset.prod (range (n + 1))
    (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I)

  Int.floor (P_n.im / 2)

/-- `zp n = ∏_{k < n} (1 + 2 k i)` in `ℤ[i]`. -/
def zp (n : ℕ) : GaussianInt :=
  ∏ k ∈ Finset.range n, (1 + ((2 * k : ℕ) : GaussianInt) * Zsqrtd.sqrtd)

/-- `zm n = ∏_{k < n} (1 - 2 k i)` in `ℤ[i]`. -/
def zm (n : ℕ) : GaussianInt :=
  ∏ k ∈ Finset.range n, (1 - ((2 * k : ℕ) : GaussianInt) * Zsqrtd.sqrtd)

/-- The image of `zp n` in `ℂ` is the complex product in the definition of `a`. -/
theorem toComplex_zp (n : ℕ) :
    GaussianInt.toComplex (zp n) =
      ∏ k ∈ Finset.range n, ((1 : ℂ) + ((2 * k : ℕ) : ℝ) * Complex.I) := by
  unfold zp
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hi : GaussianInt.toComplex Zsqrtd.sqrtd = Complex.I := by
    rw [GaussianInt.toComplex_def]
    simp
  rw [map_add, map_one, map_mul, map_natCast, hi, Complex.ofReal_natCast]

/-- The imaginary part of `zp n` is even. -/
theorem two_dvd_im (n : ℕ) : (2 : ℤ) ∣ (zp n).im := by
  induction n with
  | zero => simp [zp]
  | succ n ih =>
    have e : (zp (n + 1)).im = (zp n).im + 2 * ((n : ℤ) * (zp n).re) := by
      simp only [zp, Finset.prod_range_succ, Zsqrtd.im_mul, Zsqrtd.im_add, Zsqrtd.im_one,
        Zsqrtd.re_add, Zsqrtd.re_one, Zsqrtd.re_mul, Zsqrtd.im_natCast, Zsqrtd.re_natCast,
        Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd]
      push_cast
      ring
    rw [e]
    exact dvd_add ih (dvd_mul_right 2 _)

/-- `a n` is half the imaginary part of `zp (n + 1)`. -/
theorem two_mul_a (n : ℕ) : 2 * a n = (zp (n + 1)).im := by
  obtain ⟨m, hm⟩ := two_dvd_im (n + 1)
  have ha : a n = Int.floor (((zp (n + 1)).im : ℝ) / 2) := by
    rw [GaussianInt.intCast_im, toComplex_zp]
    rfl
  rw [ha, hm]
  push_cast
  rw [mul_div_cancel_left₀ _ two_ne_zero, Int.floor_intCast]

/-- Reflection `k ↦ p - 1 - k`: if `p = 0` in `R`, then
`∏_{k < p} (1 + 2 k c) = ∏_{k < p} (1 - 2 k c)`. -/
theorem prod_reflect {R : Type*} [CommRing R] (p : ℕ) (hp : (p : R) = 0) (c : R) :
    ∏ k ∈ Finset.range p, (1 + ((2 * k : ℕ) : R) * c) =
      ∏ k ∈ Finset.range p, (1 - ((2 * k : ℕ) : R) * c) := by
  have h1 : ∏ k ∈ Finset.range p, (1 + ((2 * k : ℕ) : R) * c) =
      ∏ k ∈ Finset.range p, (1 - ((2 * (k + 1) : ℕ) : R) * c) := by
    rw [← Finset.prod_range_reflect (fun k => 1 + ((2 * k : ℕ) : R) * c) p]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k < p := Finset.mem_range.mp hk
    have e : ((2 * (p - 1 - k) : ℕ) : R) + ((2 * (k + 1) : ℕ) : R) = 0 := by
      rw [← Nat.cast_add, show 2 * (p - 1 - k) + 2 * (k + 1) = 2 * p by omega, Nat.cast_mul, hp,
        mul_zero]
    rw [eq_neg_of_add_eq_zero_left e]
    ring
  have h2 : ∏ k ∈ Finset.range (p + 1), (1 - ((2 * k : ℕ) : R) * c) =
      ∏ k ∈ Finset.range p, (1 - ((2 * (k + 1) : ℕ) : R) * c) := by
    rw [Finset.prod_range_succ']
    simp
  have h3 : ∏ k ∈ Finset.range (p + 1), (1 - ((2 * k : ℕ) : R) * c) =
      ∏ k ∈ Finset.range p, (1 - ((2 * k : ℕ) : R) * c) := by
    rw [Finset.prod_range_succ]
    have hfp : (1 : R) - ((2 * p : ℕ) : R) * c = 1 := by
      rw [Nat.cast_mul, hp, mul_zero, zero_mul, sub_zero]
    rw [hfp, mul_one]
  rw [h1, ← h2, h3]

/-- `zp p ≡ zm p (mod p)` in `ℤ[i]`. -/
theorem dvd_zp_sub_zm (p : ℕ) : ((p : ℤ) : GaussianInt) ∣ zp p - zm p := by
  rw [Int.cast_natCast, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have hp : ((p : ℕ) : GaussianInt ⧸ Ideal.span {(p : GaussianInt)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : GaussianInt)})),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  simp only [zp, zm, map_prod, map_add, map_sub, map_one, map_mul, map_natCast]
  exact prod_reflect p hp _

/-- `zm n` is the conjugate of `zp n`. -/
theorem zm_eq_star (n : ℕ) : zm n = star (zp n) := by
  unfold zm zp
  rw [← starRingEnd_apply, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [starRingEnd_apply]
  ext <;> simp [Zsqrtd.re_natCast, Zsqrtd.im_natCast]

/-- `p ∣ 2 Im (zp p)` for every `p`. -/
theorem dvd_two_mul_im (p : ℕ) : (p : ℤ) ∣ 2 * (zp p).im := by
  have h := ((Zsqrtd.intCast_dvd _ _).mp (dvd_zp_sub_zm p)).2
  have e : (zp p - zm p).im = 2 * (zp p).im := by
    rw [zm_eq_star, Zsqrtd.im_sub, Zsqrtd.im_star]
    ring
  rwa [e] at h

/-- Every prime divides some `a n` with `n > 0`. -/
theorem conjecture_type1_empty_core :
    ∀ p : ℕ, p.Prime → ∃ n : ℕ, 0 < n ∧ (p : ℤ) ∣ a n := by
  intro p hp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · refine ⟨3, by norm_num, ?_⟩
    rw [show a 3 = -18 by norm_num [a, Finset.prod_range_succ]]
    norm_num
  · have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    refine ⟨p - 1, by omega, ?_⟩
    have h2a : 2 * a (p - 1) = (zp p).im := by
      have := two_mul_a (p - 1)
      rwa [Nat.sub_add_cancel (show 1 ≤ p by omega)] at this
    have h := dvd_two_mul_im p
    rw [← h2a] at h
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hnd : ¬ (p : ℤ) ∣ 2 := by
      intro h2
      have := Int.le_of_dvd (by norm_num) h2
      omega
    rcases hpz.dvd_or_dvd h with h1 | h1
    · exact absurd h1 hnd
    rcases hpz.dvd_or_dvd h1 with h1 | h1
    · exact absurd h1 hnd
    · exact h1

end A363414Core
