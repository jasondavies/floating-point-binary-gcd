import Mathlib

namespace Stein

/-!
This namespace formalizes worst-case iteration bounds for Stein's binary gcd
algorithm on inputs below `2^k`.

- The normalized odd-core phase has at most `k - 1` strict bundled reductions.
- The usual bundled outer Stein loop has at most `k` iterations, counting the
  final equality-to-zero exit.
- Both bounds are sharp, witnessed by the family `(1, 2^k - 1)`.
-/

/--
A single bundled odd-state reduction of Stein's binary gcd algorithm.

The inputs are already normalized: `x` and `y` are positive odd naturals with
`x < y`. One `CoreStep` performs exactly one subtraction, strips all factors of
`2` from the difference `y - x`, and then sorts the resulting odd pair.
-/
def CoreStep (x y x' y' : Nat) : Prop :=
  0 < x ∧
  x < y ∧
  Odd x ∧
  Odd y ∧
  ∃ t z : Nat,
    0 < t ∧
    Odd z ∧
    y - x = 2 ^ t * z ∧
    x' = min x z ∧
    y' = max x z

lemma two_le_two_pow {t : Nat} (ht : 0 < t) : 2 ≤ 2 ^ t := by
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ t := by
      exact Nat.pow_le_pow_right (by omega) (Nat.succ_le_of_lt ht)

lemma coreStep_sum_le_half {x y x' y' : Nat} (h : CoreStep x y x' y') :
    x' + y' ≤ (x + y) / 2 := by
  rcases h with ⟨hx0, hxy, hxOdd, hyOdd, t, z, ht0, hzOdd, hdiff, rfl, rfl⟩
  rcases hxOdd with ⟨a, rfl⟩
  rcases hyOdd with ⟨b, rfl⟩
  rcases hzOdd with ⟨c, rfl⟩
  have hpow : 2 ≤ 2 ^ t := two_le_two_pow ht0
  have hmul : 2 * (2 * c + 1) ≤ (2 ^ t) * (2 * c + 1) := by
    exact Nat.mul_le_mul_right (2 * c + 1) hpow
  have hdiff' : (2 * b + 1) - (2 * a + 1) = 2 ^ t * (2 * c + 1) := hdiff
  have hz_le : 2 * c + 1 ≤ ((2 * b + 1) - (2 * a + 1)) / 2 := by
    have hdiff'' : 2 ^ t * (2 * c + 1) = (2 * b + 1) - (2 * a + 1) := by
      simpa using hdiff'.symm
    have : 2 * (2 * c + 1) ≤ (2 * b + 1) - (2 * a + 1) := by
      omega
    omega
  have hminmax : min (2 * a + 1) (2 * c + 1) + max (2 * a + 1) (2 * c + 1) =
      (2 * a + 1) + (2 * c + 1) := by
    omega
  rw [hminmax]
  have hxle : 2 * a + 1 ≤ 2 * b + 1 := by
    omega
  omega

lemma coreStep_sum_lt_pow {x y x' y' m : Nat}
    (h : CoreStep x y x' y')
    (hsum : x + y < 2 ^ (m + 1)) :
    x' + y' < 2 ^ m := by
  have hhalf := coreStep_sum_le_half h
  have hdiv : (x + y) / 2 < 2 ^ m := by
    have : x + y < 2 * 2 ^ m := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
    omega
  exact lt_of_le_of_lt hhalf hdiv

/--
Two positive odd naturals with `x < y` must have sum at least `4`.

This is the final contradiction in the global core-step bound: after `k - 1`
strict bundled odd reductions the sum is already `< 4`, so no further
`CoreStep` is possible.
-/
lemma odd_strict_pair_sum_ge_four {x y : Nat}
    (hx : 0 < x) (hxy : x < y) (hxOdd : Odd x) (hyOdd : Odd y) :
    4 ≤ x + y := by
  rcases hxOdd with ⟨a, ha⟩
  rcases hyOdd with ⟨b, hb⟩
  rw [ha, hb]
  omega

/--
Strategy for the core bound:

Each `CoreStep` halves the sum of the normalized odd pair. Starting below
`2^(k+1)`, after `j` strict reductions the sum is below `2^(k+1-j)`. After
`k - 1` such steps it is below `4`, so one more strict odd reduction is
impossible.
-/
theorem no_kth_core_reduction
    {k : Nat} (hk : 0 < k) {s : Nat → Nat × Nat}
    (ha : (s 0).1 < 2 ^ k)
    (hb : (s 0).2 < 2 ^ k)
    (hsteps : ∀ i < k - 1, CoreStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2) :
    ¬ CoreStep (s (k - 1)).1 (s (k - 1)).2 (s k).1 (s k).2 := by
  have hsum :
      ∀ j ≤ k - 1, (s j).1 + (s j).2 < 2 ^ (k + 1 - j) := by
    intro j hj
    induction' j with j ih
    · have : (s 0).1 + (s 0).2 < 2 ^ (k + 1) := by
        rw [pow_succ]
        omega
      simpa using this
    · have hj' : j ≤ k - 1 := by
        omega
      have hstep : CoreStep (s j).1 (s j).2 (s (j + 1)).1 (s (j + 1)).2 := by
        apply hsteps
        omega
      have hprev : (s j).1 + (s j).2 < 2 ^ ((k - j) + 1) := by
        have := ih hj'
        have hrewrite : k + 1 - j = (k - j) + 1 := by
          omega
        simpa [hrewrite] using this
      have hnext : (s (j + 1)).1 + (s (j + 1)).2 < 2 ^ (k - j) := by
        exact coreStep_sum_lt_pow hstep hprev
      have hrewrite : k + 1 - (j + 1) = k - j := by
        omega
      simpa [hrewrite] using hnext
  have hlast : (s (k - 1)).1 + (s (k - 1)).2 < 4 := by
    have := hsum (k - 1) le_rfl
    have hrewrite : k + 1 - (k - 1) = 2 := by
      omega
    simpa [hrewrite] using this
  intro hfinal
  rcases hfinal with ⟨hx0, hxy, hxOdd, hyOdd, t, z, ht0, hzOdd, hdiff, hx', hy'⟩
  have hge : 4 ≤ (s (k - 1)).1 + (s (k - 1)).2 :=
    odd_strict_pair_sum_ge_four hx0 hxy hxOdd hyOdd
  omega

/--
For inputs below `2^k`, there are at most `k - 1` strict bundled odd
reductions before reaching an equal odd pair.
-/
theorem core_reduction_count_le
    {k n : Nat} (hk : 0 < k) {s : Nat → Nat × Nat}
    (ha : (s 0).1 < 2 ^ k)
    (hb : (s 0).2 < 2 ^ k)
    (hsteps : ∀ i < n, CoreStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2) :
    n ≤ k - 1 := by
  by_contra hcontra
  have hk_le_n : k ≤ n := by
    omega
  have hprefix :
      ∀ i < k - 1, CoreStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2 := by
    intro i hi
    have : i < n := by
      omega
    exact hsteps i this
  have hnot :=
    no_kth_core_reduction hk ha hb hprefix
  have hlast : CoreStep (s (k - 1)).1 (s (k - 1)).2 (s k).1 (s k).2 := by
    have : k - 1 < n := by
      omega
    have := hsteps (k - 1) this
    have hrewrite : (k - 1) + 1 = k := by
      omega
    simpa [hrewrite] using this
  exact hnot hlast

def stripTwos (n : Nat) : Nat :=
  if h0 : n = 0 then 0
  else if Even n then stripTwos (n / 2) else n
termination_by n

decreasing_by
  have hpos : 0 < n := Nat.pos_of_ne_zero h0
  exact Nat.div_lt_self hpos (by omega)

lemma stripTwos_le (n : Nat) : stripTwos n ≤ n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  unfold stripTwos
  split
  · omega
  · rename_i h0
    split
    · rename_i he
      have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by omega)
      exact le_trans (ih (n / 2) hlt) (Nat.div_le_self n 2)
    · omega

lemma stripTwos_pos {n : Nat} (hn : 0 < n) : 0 < stripTwos n := by
  refine Nat.strong_induction_on n ?_ hn
  intro n ih hn
  unfold stripTwos
  split
  · omega
  · rename_i h0
    split
    · rename_i he
      have hlt : n / 2 < n := Nat.div_lt_self hn (by omega)
      rcases he with ⟨m, hm⟩
      have hdivpos : 0 < n / 2 := by
        omega
      exact ih (n / 2) hlt hdivpos
    · omega

lemma stripTwos_odd {n : Nat} (hn : 0 < n) : Odd (stripTwos n) := by
  refine Nat.strong_induction_on n ?_ hn
  intro n ih hn
  unfold stripTwos
  split
  · omega
  · rename_i h0
    split
    · rename_i he
      have hlt : n / 2 < n := Nat.div_lt_self hn (by omega)
      rcases he with ⟨m, hm⟩
      have hdivpos : 0 < n / 2 := by
        omega
      exact ih (n / 2) hlt hdivpos
    · rename_i hne
      exact (Nat.not_even_iff_odd).mp hne

lemma stripTwos_lt_pow {n k : Nat} (hn : n < 2 ^ k) : stripTwos n < 2 ^ k := by
  exact lt_of_le_of_lt (stripTwos_le n) hn

/--
Normalization for Stein's algorithm: strip all factors of `2` from each input
and then sort the pair.

This does not by itself guarantee positivity: if one original input is `0`,
the corresponding normalized component is also `0`.
-/
def normalizeInput (a b : Nat) : Nat × Nat :=
  let x := stripTwos a
  let y := stripTwos b
  (min x y, max x y)

lemma normalizeInput_lt_pow {a b k : Nat}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (normalizeInput a b).1 < 2 ^ k ∧ (normalizeInput a b).2 < 2 ^ k := by
  unfold normalizeInput
  have hxa : stripTwos a < 2 ^ k := stripTwos_lt_pow ha
  have hyb : stripTwos b < 2 ^ k := stripTwos_lt_pow hb
  by_cases hle : stripTwos a ≤ stripTwos b
  · simp [hle, hxa, hyb]
  · have hge : stripTwos b ≤ stripTwos a := by
      omega
    have hmin : min (stripTwos a) (stripTwos b) = stripTwos b := by
      simp [Nat.min_def, hle]
    have hmax : max (stripTwos a) (stripTwos b) = stripTwos a := by
      simp [Nat.max_def, hle]
    constructor
    · simpa [hmin, hmax]
        using hyb
    · simpa [hmin, hmax]
        using hxa

lemma normalizeInput_pos_odd {a b : Nat}
    (ha : 0 < a) (hb : 0 < b) :
    0 < (normalizeInput a b).1 ∧ Odd (normalizeInput a b).1 ∧
    0 < (normalizeInput a b).2 ∧ Odd (normalizeInput a b).2 := by
  unfold normalizeInput
  have hxa : 0 < stripTwos a := stripTwos_pos ha
  have hya : 0 < stripTwos b := stripTwos_pos hb
  have hxo : Odd (stripTwos a) := stripTwos_odd ha
  have hyo : Odd (stripTwos b) := stripTwos_odd hb
  by_cases hle : stripTwos a ≤ stripTwos b
  · simp [hle, hxa, hya, hxo, hyo]
  · have hge : stripTwos b ≤ stripTwos a := by
      omega
    have hmin : min (stripTwos a) (stripTwos b) = stripTwos b := by
      simp [Nat.min_def, hle]
    have hmax : max (stripTwos a) (stripTwos b) = stripTwos a := by
      simp [Nat.max_def, hle]
    constructor
    · simpa [hmin, hmax] using hya
    constructor
    · simpa [hmin, hmax] using hyo
    constructor
    · simpa [hmin, hmax] using hxa
    · simpa [hmin, hmax] using hxo

/--
Normalization turns positive inputs into an ordered pair `x ≤ y` of positive
odd naturals.
-/
lemma normalizeInput_spec {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    0 < (normalizeInput a b).1 ∧
    (normalizeInput a b).1 ≤ (normalizeInput a b).2 ∧
    Odd (normalizeInput a b).1 ∧
    Odd (normalizeInput a b).2 := by
  rcases normalizeInput_pos_odd ha hb with ⟨h1pos, h1odd, h2pos, h2odd⟩
  refine ⟨h1pos, ?_, h1odd, h2odd⟩
  · unfold normalizeInput
    dsimp
    exact min_le_max

/--
For arbitrary inputs `a, b < 2^k`, the normalized odd-core phase of Stein's
algorithm performs at most `k - 1` strict reductions.

If one input is `0`, normalization may produce a zero component, in which case
no `CoreStep` is possible and the bound is trivial.
-/
theorem arbitrary_input_core_reduction_count_le
    {k n a b : Nat} (hk : 0 < k)
    (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    {s : Nat → Nat × Nat}
    (hstart : s 0 = normalizeInput a b)
    (hsteps : ∀ i < n, CoreStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2) :
    n ≤ k - 1 := by
  have hnorm := normalizeInput_lt_pow ha hb
  refine core_reduction_count_le hk ?_ ?_ hsteps
  · rw [hstart]
    exact hnorm.1
  · rw [hstart]
    exact hnorm.2

/--
User-facing name for the `k - 1` bound on strict bundled odd reductions.

This theorem is just `arbitrary_input_core_reduction_count_le` under a name
that emphasizes the iteration-count interpretation.
-/
theorem stein_core_step_count_le
    {k n a b : Nat} (hk : 0 < k)
    (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    {s : Nat → Nat × Nat}
    (hstart : s 0 = normalizeInput a b)
    (hsteps : ∀ i < n, CoreStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2) :
    n ≤ k - 1 :=
  arbitrary_input_core_reduction_count_le hk ha hb hstart hsteps

/--
One iteration of the usual bundled Stein loop on normalized states.

The state is kept as a sorted pair of odd positive numbers, except for the
terminal state `(g, 0)`. A loop iteration either performs one strictly
decreasing `CoreStep`, or exits from an equal odd pair by setting the second
component to `0`. This is the step notion used in the final `k`-step worst-case
bound.
-/
def SteinLoopStep (x y x' y' : Nat) : Prop :=
  CoreStep x y x' y' ∨ (0 < x ∧ x = y ∧ x' = x ∧ y' = 0)

lemma not_steinLoopStep_right_zero {x x' y' : Nat} :
    ¬ SteinLoopStep x 0 x' y' := by
  intro h
  rcases h with hcore | hexit
  · rcases hcore with ⟨hx0, hxy, hxOdd, hyOdd, t, z, ht0, hzOdd, hdiff, hx', hy'⟩
    omega
  · rcases hexit with ⟨hx0, hxy, hx', hy'⟩
    omega

/--
For arbitrary inputs `a, b < 2^k`, the usual bundled Stein loop performs at
most `k` iterations when the final equality-to-zero exit is counted as one
iteration.
-/
theorem stein_loop_step_count_le
    {k n a b : Nat} (hk : 0 < k)
    (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    {s : Nat → Nat × Nat}
    (hstart : s 0 = normalizeInput a b)
    (hsteps : ∀ i < n, SteinLoopStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2) :
    n ≤ k := by
  by_cases hn : n = 0
  · omega
  · have hprefix :
        ∀ i < n - 1, CoreStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2 := by
        intro i hi
        have hstep : SteinLoopStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2 := by
          exact hsteps i (by omega)
        rcases hstep with hcore | hexit
        · exact hcore
        · have hnext : SteinLoopStep (s (i + 1)).1 (s (i + 1)).2
              (s (i + 2)).1 (s (i + 2)).2 := by
            exact hsteps (i + 1) (by omega)
          have hz : (s (i + 1)).2 = 0 := by
            rcases hexit with ⟨hx0, hxy, hx', hy'⟩
            simp [hy']
          have : ¬ SteinLoopStep (s (i + 1)).1 (s (i + 1)).2
              (s (i + 2)).1 (s (i + 2)).2 := by
            rw [hz]
            exact not_steinLoopStep_right_zero
          exact False.elim (this hnext)
    have hbound : n - 1 ≤ k - 1 :=
      arbitrary_input_core_reduction_count_le hk ha hb hstart hprefix
    omega

lemma odd_two_pow_sub_one {m : Nat} (hm : 0 < m) : Odd (2 ^ m - 1) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨n, rfl⟩
  refine ⟨2 ^ n - 1, ?_⟩
  rw [pow_succ]
  have hcomm : 2 ^ n * 2 = 2 * 2 ^ n := by
    ac_rfl
  rw [hcomm]
  have hpowpos : 0 < 2 ^ n := by
    exact pow_pos (by omega) _
  omega

lemma one_le_two_pow_sub_one {m : Nat} (hm : 0 < m) : 1 ≤ 2 ^ m - 1 := by
  have hpow : 2 ≤ 2 ^ m := two_le_two_pow hm
  omega

theorem witness_step {m : Nat} (hm : 0 < m) :
    CoreStep 1 (2 ^ (m + 1) - 1) 1 (2 ^ m - 1) := by
  refine ⟨by omega, ?_, by exact ⟨0, by omega⟩, odd_two_pow_sub_one (by omega), 1, 2 ^ m - 1, by omega, odd_two_pow_sub_one hm, ?_, ?_, ?_⟩
  · have hpow : 2 ≤ 2 ^ m := two_le_two_pow hm
    omega
  · have : 2 ^ (m + 1) - 1 - 1 = 2 * (2 ^ m - 1) := by
      rw [pow_succ]
      omega
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  · exact (min_eq_left (one_le_two_pow_sub_one hm)).symm
  · exact (max_eq_right (one_le_two_pow_sub_one hm)).symm

def witnessState (k i : Nat) : Nat × Nat :=
  (1, 2 ^ (k - i) - 1)

theorem witness_path {k i : Nat} (hi : i < k - 1) :
    CoreStep (witnessState k i).1 (witnessState k i).2
      (witnessState k (i + 1)).1 (witnessState k (i + 1)).2 := by
  have hm : 0 < k - i - 1 := by
    omega
  have hsrc : k - i = (k - i - 1) + 1 := by
    omega
  have hdst : k - (i + 1) = k - i - 1 := by
    omega
  unfold witnessState
  change CoreStep 1 (2 ^ (k - i) - 1) 1 (2 ^ (k - (i + 1)) - 1)
  rw [hsrc, hdst]
  exact witness_step hm

theorem witness_terminal {k : Nat} (hk : 0 < k) :
    witnessState k (k - 1) = (1, 1) := by
  unfold witnessState
  have hrewrite : k - (k - 1) = 1 := by
    omega
  simp [hrewrite]

/--
The strict core bound `k - 1` is attained by an explicit normalized path.
-/
theorem exists_path_attaining_core_bound {k : Nat} (hk : 0 < k) :
    ∃ s : Nat → Nat × Nat,
      (∀ i < k - 1, CoreStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2) ∧
      s (k - 1) = (1, 1) := by
  refine ⟨witnessState k, ?_, ?_⟩
  · intro i hi
    exact witness_path hi
  · exact witness_terminal hk

/--
The worst-case witness inputs satisfy the ambient `< 2^k` size bound whenever
`k > 0`.
-/
lemma witness_inputs_lt_pow {k : Nat} (hk : 0 < k) :
    1 < 2 ^ k ∧ 2 ^ k - 1 < 2 ^ k := by
  have hpow : 2 ≤ 2 ^ k := two_le_two_pow hk
  constructor
  · omega
  · omega

/--
Worst-case family for the bundled Stein loop: it follows
`(1, 2^k - 1) → (1, 2^(k-1) - 1) → ... → (1, 1) → (1, 0)`.
-/
def loopWitnessState (k i : Nat) : Nat × Nat :=
  if i < k then witnessState k i else (1, 0)

theorem loopWitness_path {k i : Nat} (hk : 0 < k) (hi : i < k) :
    SteinLoopStep (loopWitnessState k i).1 (loopWitnessState k i).2
      (loopWitnessState k (i + 1)).1 (loopWitnessState k (i + 1)).2 := by
  by_cases hlt : i < k - 1
  · unfold loopWitnessState
    have hip1 : i + 1 < k := by
      omega
    simp [hi, hip1, SteinLoopStep]
    exact Or.inl (witness_path hlt)
  · have heq : i = k - 1 := by
      omega
    subst heq
    have hkm1 : k - 1 < k := by
      omega
    have hkfalse : ¬ k < k := by
      omega
    have hsucc : k - 1 + 1 = k := by
      omega
    unfold loopWitnessState
    rw [if_pos hkm1, hsucc, if_neg hkfalse, witness_terminal hk]
    right
    omega

theorem loopWitness_terminal (k : Nat) :
    loopWitnessState k k = (1, 0) := by
  unfold loopWitnessState
  simp

/--
The `k`-step bound for bundled Stein iterations is sharp.

The explicit worst-case family is `loopWitnessState k`, corresponding to the
inputs `(1, 2^k - 1)`.
-/
theorem stein_loop_exact_bound {k : Nat} (hk : 0 < k) :
    (∀ i < k,
        SteinLoopStep (loopWitnessState k i).1 (loopWitnessState k i).2
          (loopWitnessState k (i + 1)).1 (loopWitnessState k (i + 1)).2) ∧
    loopWitnessState k k = (1, 0) := by
  refine ⟨?_, loopWitness_terminal k⟩
  intro i hi
  exact loopWitness_path hk hi

/--
There exists a bundled Stein-loop execution of length exactly `k`, ending at
`(1, 0)`, so the upper bound `stein_loop_step_count_le` is sharp.
-/
theorem exists_path_attaining_stein_loop_bound {k : Nat} (hk : 0 < k) :
    ∃ s : Nat → Nat × Nat,
      (∀ i < k, SteinLoopStep (s i).1 (s i).2 (s (i + 1)).1 (s (i + 1)).2) ∧
      s k = (1, 0) := by
  refine ⟨loopWitnessState k, ?_, ?_⟩
  · intro i hi
    exact loopWitness_path hk hi
  · exact loopWitness_terminal k

end Stein
