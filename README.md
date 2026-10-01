# Every prime divides a term of OEIS A363414

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT. **Paper:** [`paper/main.pdf`](paper/main.pdf)

`a(n) = Im(∏_{k=0..n} (1 + 2k i)) / 2` is [OEIS A363414](https://oeis.org/A363414): 0, 1, 3, −18, −190, …

Peter Bala conjectured that every prime divides some term `a(n)` with `n > 0` ("no primes of type 1"). Google
DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) states this as
`OeisA363414.conjecture_type1_empty` (`research open`) in pull request
[#4946](https://github.com/google-deepmind/formal-conjectures/pull/4946).

**Theorem.** `p ∣ a(p−1)` for every odd prime `p`, and `a(3) = −18`. So the conjecture is true.

**Proof.** Work modulo an odd prime `p`, in `ℤ[i]/(p)`.
- Reversing the factors (`k ↦ p−1−k`) turns `∏_{k<p} (1 + 2k i)` into `∏_{k<p} (1 − 2k i)`, its complex conjugate.
- So `p` divides `2i·Im(P) = 4i·a(p−1)`, and hence `p ∣ a(p−1)`.
- The exact residue is `P ≡ 1 − (−1)^((p−1)/2) (mod p)`, from `∏_{t∈F_p} (X − t) = X^p − X`.

## Lean 4 verification (`lean/`)

- `Statement.lean`: the pull-request file, byte-identical (git blob `92bbac85`), compiled with the repository's
  `leanOptions`.
- `Core.lean` (Mathlib only): the copied definition and the proof.
- `Solution.lean`: `OeisA363414.conjecture_type1_empty_solved`, with the type of the repository statement.
- `CheckAnswer.lean`: the definitions agree (`rfl`), the type equality holds (`rfl`), and it prints the axioms: only
  `propext`, `Classical.choice` and `Quot.sound`.

To reproduce, you need:
- Lean v4.33.1;
- a formal-conjectures checkout, tested at `ab0addc45f699bdd0b7cc58efa5140a72f101a9e`;
- `lake exe cache get`, run in that checkout.

Then run:

```bash
bash lean/check.sh /path/to/formal-conjectures
```

Log: `logs/lean_check.log` (exit 0, 104 s).

## Checks

`scripts/verify.py` checks with exact arithmetic:
- the residue formula for all odd primes `p < 20000`;
- `p ∣ a(p−1)` for `p < 400`.

## Prior work

The conjecture is stated in the OEIS entry (Bala, 2023), with no proof there. Search date 2026-10-01. We found no
proof in:
- Formal Conjectures issues and pull requests;
- the OEIS Open benchmark (arXiv:2608.11941);
- the-omega-institute/trureturing;
- GitHub;
- web search.

The companion conjecture `conjecture_type2_asymptotics` is not addressed.
