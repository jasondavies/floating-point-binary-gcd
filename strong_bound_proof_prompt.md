# Strong-Bound Admissibility Proof Task

I want a rigorous mathematical proof, not code, for the admissibility of a
pruning bound used in an exact reverse search for a modified binary-GCD-like
algorithm.

Please treat this as a standalone proof task. Do not assume access to any
repository. Everything relevant is stated below.

## Algorithm

Let `a >= b > 0`. Define

- `e = bitlen(a) - bitlen(b)`
- `t = 2^e * b`
- `r = |a - t|`

One forward modified-LSBGCD step maps

`(a, b) -> (max(b, r), min(b, r))`

and then normalises by dividing both entries by `gcd(max(b, r), min(b, r))`.

For bit-length arguments, normalisation can only help: dividing by a common
factor cannot increase the maximum bit-length.

Write

- `M(a, b) = max(bitlen(a), bitlen(b))`
- `bitlen(0) = 0`

## What needs to be proved

For an exact reverse search inside the `k`-bit box, define the current deficit

`delta = k - bitlen(a)`

for the current reduced reverse-search state `(a, b)` with `a >= b >= 0`.

The search uses the following strong upper bound on the number of additional
reverse steps:

- `min_drop_for_steps_strong(s) = 3 * floor(s / 5) + r(s mod 5)`
- where `r(0)=0, r(1)=0, r(2)=1, r(3)=1, r(4)=2`

Equivalently:

- `min_drop_for_steps_strong(0) = 0`
- `min_drop_for_steps_strong(1) = 0`
- `min_drop_for_steps_strong(2) = 1`
- `min_drop_for_steps_strong(3) = 1`
- `min_drop_for_steps_strong(4) = 2`
- `min_drop_for_steps_strong(5) = 3`
- and then periodic with slope `3/5`.

The admissibility statement is:

> For every forward continuation of `s` more steps from any state, the top
> bit-length drops by at least `min_drop_for_steps_strong(s)`.

If true, then the reverse search can safely prune whenever the remaining
bit-length budget `delta` is too small to support the requested remaining
depth.

## What is already rigorous

### Two-step lemma

If `e > 0`, then one step strictly decreases `M`.

Reason: `b` has smaller bit-length than `a`, and
`r = |a - 2^e b| < 2^bitlen(a)`, so the output pair has maximum bit-length at
most `M(a, b) - 1`.

If `e = 0`, then the step is

`(a, b) -> (b, a - b)`

with `a` and `b` having the same bit-length, hence `a - b` has strictly
smaller bit-length than `b`. So the next step must have `e > 0`.

Therefore:

> Every two consecutive steps reduce `M` by at least `1`.

This already gives the rigorous but weaker upper bound `2 * delta + 1`.

## Reduction of the strong bound to a local lemma

To prove the strong bound above, it is enough to prove:

> Five-step drop lemma:
> Every valid five-step forward block drops the top bit-length by at least `3`.

Indeed, combining

- `2` steps -> at least `1` bit drop
- `5` steps -> at least `3` bit drop

and taking the optimal decomposition of `s` into 5-blocks plus a short
remainder gives exactly the remainder table

- remainder `0` -> `0`
- remainder `1` -> `0`
- remainder `2` -> `1`
- remainder `3` -> `1`
- remainder `4` -> `2`

That is precisely `min_drop_for_steps_strong`.

## Combinatorial reduction of the five-step lemma

Write `M_i` for the top bit-length before step `i` in a 5-step block.

From the two-step lemma:

1. if a step has `e > 0`, it causes an immediate drop of at least `1`;
2. if a step has `e = 0`, the next step must have `e > 0`.

Therefore, if a 5-step block were to drop by at most `2` bits total, then:

- it must contain exactly three `e = 0` steps and two `e > 0` steps;
- the zero-steps cannot be adjacent.

So the only possible bad pattern is

`0, >0, 0, >0, 0`.

Hence it is enough to prove the alternating-case lemma:

> Every valid 5-step block with `e`-pattern `0, >0, 0, >0, 0` drops at least
> `3` bits in total.

## Current proof skeleton

The following argument looks correct, but I want it checked carefully and, if
possible, rewritten into a clean formal proof.

### Lemma A: normalisation only helps

If an unreduced step output is `(u, v)` and the normalised output is `(u', v')`,
then

`max(bitlen(u'), bitlen(v')) <= max(bitlen(u), bitlen(v))`.

So it is enough to prove lower bounds on bit-length drop for the unreduced
algebra.

### Lemma B: exact drop in an alternating block

Suppose a 5-step block has `e`-pattern

`0, d_1, 0, d_2, 0`

with `d_1, d_2 >= 1`.

Then the total drop in top bit-length across the block is exactly `d_1 + d_2`.

Reason: steps `1`, `3`, and `5` start from equal-bit-length pairs, so only
steps `2` and `4` contribute bit-length drop, and they contribute exactly
`d_1` and `d_2`.

Corollary: to prove the alternating-case lemma, it is enough to rule out the
minimal obstruction

`0, 1, 0, 1, 0`.

### Lemma C: algebraic normal form for `0, 1, 0, 1, 0`

Assume the pattern `0, 1, 0, 1, 0` occurs. Let the initial pair be `(A, B)`
with `A >= B`, both of bit-length `n + 1`.

Define successive unreduced residuals:

- `D = A - B`
- `E = |B - 2D|`
- `X = |D - E|`
- `Y = min(D, E)`
- `Z = |Y - 2X|`

Then:

1. `D` and `E` have bit-length `n`
2. `X` and `Z` have bit-length `n - 1`
3. exactly one of the following three algebraic cases holds:

Case I.a:

- `D > E`
- `B < 2D`
- `D = Y + X`
- `B = Y + 2X`
- `A = 2Y + 3X`

Case I.b:

- `D > E`
- `B > 2D`
- `D = Y + X`
- `B = 3Y + 2X`
- `A = 4Y + 3X`

Case II:

- `E > D`
- `Y = D`
- `B = 3Y + X`
- `A = 4Y + X`

The derivation is:

- if `D > E`, then `Y = E` and `X = D - E`, so `D = Y + X`
- if also `B < 2D`, then `E = 2D - B`, hence
  `B = 2D - E = 2(Y + X) - Y = Y + 2X`, and `A = B + D = 2Y + 3X`
- if instead `B > 2D`, then `E = B - 2D`, hence
  `B = E + 2D = Y + 2(Y + X) = 3Y + 2X`, and `A = B + D = 4Y + 3X`
- if `E > D`, then `Y = D`, and necessarily `E = B - 2D` because
  `2D - B > D` would imply `D > B`, impossible; then
  `X = E - D = B - 3D`, so `B = 3Y + X` and `A = 4Y + X`

### Lemma D: scaled inequalities

From the bit-length data:

- `2^(n-1) <= Y < 2^n`
- `2^(n-2) <= X < 2^(n-1)`
- `2^(n-2) <= Z < 2^(n-1)`

Since `Z = |Y - 2X|`, if

- `y = Y / 2^(n-2)`
- `x = X / 2^(n-2)`

then

- `2 <= y < 4`
- `1 <= x < 2`
- `1 <= |y - 2x| < 2`

### Lemma E: Case II is impossible

In Case II, `A = 4Y + X`, so after scaling

`A / 2^(n-2) = 4y + x`

But `y >= 2` and `x >= 1`, so `4y + x >= 9`.
This is impossible because `A` has bit-length `n + 1`, hence

`A < 2^(n+1) = 8 * 2^(n-2)`.

### Lemma F: Case I.b is impossible

In Case I.b, `B = 3Y + 2X`, so after scaling

`B / 2^(n-2) = 3y + 2x`

But `y >= 2` and `x >= 1`, so `3y + 2x >= 8`.
This is impossible because `B` has bit-length `n + 1`, hence

`B < 8 * 2^(n-2)`.

### Lemma G: Case I.a is impossible

In Case I.a, `A = 2Y + 3X`, so since `A` has bit-length `n + 1`,

`2y + 3x < 8`.

But from `1 <= |y - 2x|`, either

1. `y >= 2x + 1`, which gives
   `2y + 3x >= 2(2x + 1) + 3x = 7x + 2 > 8`

or

2. `y <= 2x - 1`, which together with `y >= 2` implies `x > 3/2`, hence
   `2y + 3x > 4 + 9/2 > 8`

Either way contradiction.

Therefore all three cases are impossible, so `0, 1, 0, 1, 0` cannot occur.
By Lemma B, every alternating block drops at least `3` bits.
Hence every 5-step block drops at least `3` bits.
Hence the strong bound is admissible.

## What I want from you

Please do one of the following:

1. Give a fully rigorous proof of the admissibility statement above.
2. If the proof sketch has a gap, identify the exact gap and either repair it
   or produce a counterexample.
3. If a full proof is too long, give a theorem-proof decomposition that is
   ready to formalise in Lean, with every hidden step made explicit.

Please focus especially on:

- whether Lemma B is fully justified in the presence of normalisation
- whether the case split in Lemma C is exhaustive and sign-correct
- whether Lemma G is genuinely airtight
- whether the final passage from the 2-step lemma and 5-step lemma to
  `min_drop_for_steps_strong` is complete

## Computational evidence

An exact bounded verifier on the finite reachable reduced reverse graph found:

- no five-step violations through bit cap `11`
- in the alternating case, no occurrences of the exponent pair `(1, 1)`

This is only evidence, not part of the proof.
