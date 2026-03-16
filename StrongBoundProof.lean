import Mathlib

set_option autoImplicit false

/-!
# StrongBoundProof

This is a single-file Lean 4 draft formalization of the argument in
`strong_bound_proof.md`.

It is intentionally written as a proof-checker handoff draft:

- the definitions are explicit;
- the theorem decomposition matches the English proof.

This file has been checked against Axle's `lean-4.28.0` environment: it parses
and elaborates cleanly. The goal is to give a third-party checker a precise
formalization of the strong-bound argument used by exact-threshold search.
-/

namespace StrongBound

open Nat

def bitlen (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

def M (a b : Nat) : Nat :=
  max (bitlen a) (bitlen b)

def expGap (a b : Nat) : Nat :=
  bitlen a - bitlen b

structure State where
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def Valid (s : State) : Prop :=
  s.a ≥ s.b ∧ 0 < s.b

def Reduced (s : State) : Prop :=
  Nat.Coprime s.a s.b

def residual (s : State) : Nat :=
  Nat.dist s.a ((2 ^ expGap s.a s.b) * s.b)

def step0 (s : State) : State :=
  let r := residual s
  { a := max s.b r, b := min s.b r }

def normalize (s : State) : State :=
  let g := Nat.gcd s.a s.b
  { a := s.a / g, b := s.b / g }

def step (s : State) : State :=
  normalize (step0 s)

def Admits : Nat → State → Prop
  | 0, _ => True
  | n + 1, s => Valid s ∧ Reduced s ∧ Admits n (step s)

def iterStep : Nat → State → State
  | 0, s => s
  | n + 1, s => iterStep n (step s)

@[simp] lemma admits_zero (s : State) : Admits 0 s := trivial

@[simp] lemma admits_succ_iff (n : Nat) (s : State) :
    Admits (n + 1) s ↔ Valid s ∧ Reduced s ∧ Admits n (step s) := Iff.rfl

lemma admits_tail {n : Nat} {s : State} (h : Admits (n + 1) s) :
    Admits n (step s) := h.2.2

lemma admits_take {m n : Nat} {s : State} (hmn : m ≤ n) (h : Admits n s) :
    Admits m s := by
  induction n generalizing m s with
  | zero =>
      have hm0 : m = 0 := by omega
      simpa [hm0] using admits_zero s
  | succ n ih =>
      cases m with
      | zero =>
          exact admits_zero s
      | succ m =>
          rcases h with ⟨hvalid, hred, htail⟩
          exact ⟨hvalid, hred, ih (Nat.le_of_succ_le_succ hmn) htail⟩

@[simp] lemma iterStep_zero (s : State) : iterStep 0 s = s := rfl

@[simp] lemma iterStep_succ (n : Nat) (s : State) :
    iterStep (n + 1) s = iterStep n (step s) := rfl

def topDrop (s : State) (n : Nat) : Nat :=
  M s.a s.b - M (iterStep n s).a (iterStep n s).b

def rho : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 2

def minDropStrong (n : Nat) : Nat :=
  3 * (n / 5) + rho (n % 5)

/-!
## Basic bit-length facts

These are the arithmetic facts the rest of the file needs. A checker may wish
to replace some of these by existing Mathlib lemmas if preferred.
-/

lemma bitlen_zero : bitlen 0 = 0 := by
  simp [bitlen]

lemma bitlen_pos {n : Nat} (hn : 0 < n) : 0 < bitlen n := by
  simp [bitlen, Nat.ne_of_gt hn]

lemma bitlen_eq_zero {n : Nat} : bitlen n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact hn
    · simp [bitlen, hn] at h
  · intro h
    simp [bitlen, h]

lemma bitlen_monotone {m n : Nat} (h : m ≤ n) : bitlen m ≤ bitlen n := by
  by_cases hm : m = 0
  · simp [bitlen, hm]
  · by_cases hn : n = 0
    · omega
    · rw [bitlen, if_neg hm, bitlen, if_neg hn, Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.succ_le_succ (Nat.log_mono_right h)

lemma bitlen_lt_of_lt_pow {n x : Nat} (h : x < 2 ^ n) : bitlen x ≤ n := by
  by_cases hx : x = 0
  · simp [bitlen, hx]
  · rw [bitlen, if_neg hx, Nat.log2_eq_log_two]
    exact Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow hx h)

lemma pow_lt_of_bitlen_lt {n x : Nat} (h : bitlen x < n) : x < 2 ^ n := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [bitlen, if_neg hx, Nat.log2_eq_log_two] at h
    have hpow : x < 2 ^ (Nat.log 2 x).succ := by
      exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
    have hle : 2 ^ (Nat.log 2 x).succ ≤ 2 ^ n := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt h)
    exact lt_of_lt_of_le hpow hle

lemma same_bitlen_sub_smaller
    {a b : Nat}
    (hab : a ≥ b)
    (hb : 0 < b)
    (hbits : bitlen a = bitlen b) :
    bitlen (a - b) < bitlen b := by
  let k := bitlen b
  have hkpos : 0 < k := by
    dsimp [k]
    exact bitlen_pos hb
  have ha0 : 0 < a := lt_of_lt_of_le hb hab
  have hAupperA : a < 2 ^ bitlen a := by
    simpa [bitlen, Nat.ne_of_gt ha0, Nat.log2_eq_log_two] using
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) a)
  have hAupper : a < 2 ^ k := by
    dsimp [k]
    simpa [hbits] using hAupperA
  have hBlower : 2 ^ (k - 1) ≤ b := by
    dsimp [k]
    simpa [bitlen, Nat.ne_of_gt hb, Nat.log2_eq_log_two] using
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt hb))
  have hAupper' : a < 2 ^ ((k - 1) + 1) := by
    have hk : (k - 1) + 1 = k := by
      omega
    simpa [hk] using hAupper
  have hAupper'' : a < 2 ^ (k - 1) * 2 := by
    simpa [pow_succ] using hAupper'
  have hsub : a - b < 2 ^ (k - 1) := by
    have : a < 2 * 2 ^ (k - 1) := by
      simpa [Nat.mul_comm] using hAupper''
    omega
  have hlen : bitlen (a - b) ≤ k - 1 := bitlen_lt_of_lt_pow hsub
  have : bitlen (a - b) < k := by
    omega
  simpa [k] using this

lemma lt_pow_bitlen {x : Nat} (hx : 0 < x) : x < 2 ^ bitlen x := by
  simpa [bitlen, Nat.ne_of_gt hx, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) x)

lemma pow_bitlen_pred_le {x : Nat} (hx : 0 < x) : 2 ^ (bitlen x - 1) ≤ x := by
  simpa [bitlen, Nat.ne_of_gt hx, Nat.log2_eq_log_two] using
    (Nat.pow_log_le_self 2 (Nat.ne_of_gt hx))

lemma bitlen_eq_of_zeroGap
    {a b : Nat}
    (hab : a ≥ b)
    (hgap : expGap a b = 0) :
    bitlen a = bitlen b := by
  have hmono : bitlen b ≤ bitlen a := bitlen_monotone hab
  unfold expGap at hgap
  omega

lemma bitlen_max_min_eq
    {x y n : Nat}
    (hmax : bitlen (max x y) = n)
    (hmin : bitlen (min x y) = n) :
    bitlen x = n ∧ bitlen y = n := by
  by_cases hxy : x ≤ y
  · simp [max_eq_right hxy, min_eq_left hxy, hxy] at hmax hmin
    exact ⟨hmin, hmax⟩
  · have hyx : y ≤ x := by omega
    simp [max_eq_left hyx, min_eq_right hyx, hyx] at hmax hmin
    exact ⟨hmax, hmin⟩

lemma dist_eq_max_sub_min (x y : Nat) :
    Nat.dist x y = max x y - min x y := by
  by_cases hxy : x ≤ y
  · simp [Nat.dist_eq_sub_of_le hxy, max_eq_right hxy, min_eq_left hxy]
  · have hyx : y ≤ x := by omega
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx, max_eq_left hyx, min_eq_right hyx]

/-!
## Normalization is trivial on reduced states

This is the key simplification relative to the original proof sketch.
-/

theorem step0_coprime_of_reduced
    {s : State}
    (_hvalid : Valid s)
    (hred : Reduced s) :
    Reduced (step0 s) := by
  let t := (2 ^ expGap s.a s.b) * s.b
  let d := s.b.gcd (residual s)
  have hdb : d ∣ s.b := by
    dsimp [d]
    exact Nat.gcd_dvd_left _ _
  have hdr : d ∣ residual s := by
    dsimp [d]
    exact Nat.gcd_dvd_right _ _
  have hdt : d ∣ t := by
    dsimp [t]
    exact Nat.dvd_mul_left_of_dvd hdb _
  have hda : d ∣ s.a := by
    by_cases hta : t ≤ s.a
    · have hres : residual s = s.a - t := by
        simpa [residual, t, Nat.dist_comm] using
          (Nat.dist_eq_sub_of_le hta : Nat.dist t s.a = s.a - t)
      rw [hres] at hdr
      have : d ∣ (s.a - t) + t := Nat.dvd_add hdr hdt
      simpa [Nat.sub_add_cancel hta] using this
    · have has : s.a ≤ t := by
        omega
      have hres : residual s = t - s.a := by
        simpa [residual, t] using (Nat.dist_eq_sub_of_le has : Nat.dist s.a t = t - s.a)
      rw [hres] at hdr
      have : d ∣ t - (t - s.a) := Nat.dvd_sub hdt hdr
      simpa [Nat.sub_sub_self has] using this
  have hg : d = 1 := by
    exact Nat.eq_one_of_dvd_coprimes hred hda hdb
  have hcop : Nat.Coprime s.b (residual s) := by
    exact (Nat.coprime_iff_gcd_eq_one).2 (by simpa [d] using hg)
  by_cases hbr : s.b ≤ residual s
  · have hstep : step0 s = { a := residual s, b := s.b } := by
      simp [step0, hbr]
    rw [hstep]
    simpa [Reduced] using hcop.symm
  · have hrb : residual s ≤ s.b := by
      omega
    have hstep : step0 s = { a := s.b, b := residual s } := by
      simp [step0, hrb]
    rw [hstep]
    simpa [Reduced] using hcop

theorem normalize_eq_of_reduced
    {s : State}
    (hred : Reduced s) :
    normalize s = s := by
  rcases s with ⟨a, b⟩
  have hg : Nat.gcd a b = 1 := by
    simpa [Reduced, Nat.coprime_iff_gcd_eq_one] using hred
  simp [normalize, hg]

theorem step_eq_step0_of_reduced
    {s : State}
    (hvalid : Valid s)
    (hred : Reduced s) :
    step s = step0 s := by
  have hcop : Reduced (step0 s) := step0_coprime_of_reduced hvalid hred
  simp [step, normalize_eq_of_reduced hcop]

lemma step_eq_sub_of_zeroGap
    {s : State}
    (hvalid : Valid s)
    (hred : Reduced s)
    (hgap : expGap s.a s.b = 0) :
    step s = { a := s.b, b := s.a - s.b } := by
  have hbits : bitlen s.a = bitlen s.b := bitlen_eq_of_zeroGap hvalid.1 hgap
  have hsubbit : bitlen (s.a - s.b) < bitlen s.b :=
    same_bitlen_sub_smaller hvalid.1 hvalid.2 hbits
  have hnot : ¬ s.b ≤ s.a - s.b := by
    intro hle
    have hmono : bitlen s.b ≤ bitlen (s.a - s.b) := bitlen_monotone hle
    omega
  have hle : s.a - s.b ≤ s.b := by
    omega
  rw [step_eq_step0_of_reduced hvalid hred]
  have hres : residual s = s.a - s.b := by
    simpa [residual, hgap, Nat.dist_comm] using
      (Nat.dist_eq_sub_of_le hvalid.1 : Nat.dist s.b s.a = s.a - s.b)
  simp [step0, hres, hle]

/-!
## Two-step lemma
-/

theorem one_step_drop_of_posGap
    {s : State}
    (hvalid : Valid s)
    (hred : Reduced s)
    (hgap : 0 < expGap s.a s.b) :
    M (step s).a (step s).b + 1 ≤ M s.a s.b := by
  let n := bitlen s.a
  let m := bitlen s.b
  let t := (2 ^ expGap s.a s.b) * s.b
  have hbpos : 0 < s.b := hvalid.2
  have hapos : 0 < s.a := lt_of_lt_of_le hbpos hvalid.1
  have hmpos : 0 < m := by
    dsimp [m]
    exact bitlen_pos hbpos
  have hmn : m < n := by
    dsimp [m, n, expGap] at hgap ⊢
    omega
  have hmle : m ≤ n - 1 := by
    omega
  have ha_upper : s.a < 2 ^ n := by
    dsimp [n]
    exact lt_pow_bitlen hapos
  have ha_lower : 2 ^ (n - 1) ≤ s.a := by
    dsimp [n]
    exact pow_bitlen_pred_le hapos
  have hb_upper : s.b < 2 ^ m := by
    dsimp [m]
    exact lt_pow_bitlen hbpos
  have hb_lower : 2 ^ (m - 1) ≤ s.b := by
    dsimp [m]
    exact pow_bitlen_pred_le hbpos
  have ht_upper : t < 2 ^ n := by
    have hmul : 2 ^ expGap s.a s.b * s.b < 2 ^ expGap s.a s.b * 2 ^ m := by
      exact Nat.mul_lt_mul_of_pos_left hb_upper (pow_pos (by decide : 0 < 2) _)
    have hsum : expGap s.a s.b + m = n := by
      dsimp [m, n, expGap]
      omega
    dsimp [t]
    rwa [← pow_add, hsum] at hmul
  have ht_lower : 2 ^ (n - 1) ≤ t := by
    have hmul : 2 ^ expGap s.a s.b * 2 ^ (m - 1) ≤ 2 ^ expGap s.a s.b * s.b := by
      exact Nat.mul_le_mul_left _ hb_lower
    have hsum : expGap s.a s.b + (m - 1) = n - 1 := by
      dsimp [m, n, expGap]
      omega
    dsimp [t]
    rwa [← pow_add, hsum] at hmul
  have hb_lt : s.b < 2 ^ (n - 1) := by
    exact lt_of_lt_of_le hb_upper (Nat.pow_le_pow_right (by decide : 0 < 2) hmle)
  have hres_lt : residual s < 2 ^ (n - 1) := by
    by_cases hta : t ≤ s.a
    · have hres : residual s = s.a - t := by
        simpa [residual, t, Nat.dist_comm] using
          (Nat.dist_eq_sub_of_le hta : Nat.dist t s.a = s.a - t)
      rw [hres]
      have hsub_le : s.a - t ≤ s.a - 2 ^ (n - 1) := Nat.sub_le_sub_left ht_lower s.a
      have hupper2 : s.a < 2 * 2 ^ (n - 1) := by
        have hk : n = (n - 1) + 1 := by
          omega
        have hpow_eq : 2 ^ n = 2 ^ ((n - 1) + 1) := by
          exact congrArg (fun k => 2 ^ k) hk
        calc
          s.a < 2 ^ n := ha_upper
          _ = 2 ^ ((n - 1) + 1) := hpow_eq
          _ = 2 * 2 ^ (n - 1) := by rw [pow_succ, Nat.mul_comm]
      have hsub_lt : s.a - 2 ^ (n - 1) < 2 ^ (n - 1) := by
        omega
      exact lt_of_le_of_lt hsub_le hsub_lt
    · have hat : s.a ≤ t := by
        omega
      have hres : residual s = t - s.a := by
        simpa [residual, t] using
          (Nat.dist_eq_sub_of_le hat : Nat.dist s.a t = t - s.a)
      rw [hres]
      have hsub_le : t - s.a ≤ t - 2 ^ (n - 1) := Nat.sub_le_sub_left ha_lower t
      have hupper2 : t < 2 * 2 ^ (n - 1) := by
        have hk : n = (n - 1) + 1 := by
          omega
        have hpow_eq : 2 ^ n = 2 ^ ((n - 1) + 1) := by
          exact congrArg (fun k => 2 ^ k) hk
        calc
          t < 2 ^ n := ht_upper
          _ = 2 ^ ((n - 1) + 1) := hpow_eq
          _ = 2 * 2 ^ (n - 1) := by rw [pow_succ, Nat.mul_comm]
      have hsub_lt : t - 2 ^ (n - 1) < 2 ^ (n - 1) := by
        omega
      exact lt_of_le_of_lt hsub_le hsub_lt
  have hmax_lt : max s.b (residual s) < 2 ^ (n - 1) := by
    exact max_lt_iff.mpr ⟨hb_lt, hres_lt⟩
  have hmin_lt : min s.b (residual s) < 2 ^ (n - 1) := by
    exact lt_of_le_of_lt (min_le_left _ _) hb_lt
  have hstep_a : bitlen (step0 s).a ≤ n - 1 := by
    change bitlen (max s.b (residual s)) ≤ n - 1
    exact bitlen_lt_of_lt_pow hmax_lt
  have hstep_b : bitlen (step0 s).b ≤ n - 1 := by
    change bitlen (min s.b (residual s)) ≤ n - 1
    exact bitlen_lt_of_lt_pow hmin_lt
  have hMstep : M (step0 s).a (step0 s).b ≤ n - 1 := by
    unfold M
    exact max_le hstep_a hstep_b
  have hMs : M s.a s.b = n := by
    dsimp [n]
    unfold M
    exact max_eq_left (bitlen_monotone hvalid.1)
  rw [step_eq_step0_of_reduced hvalid hred, hMs]
  omega

theorem one_step_nonincrease
    {s : State}
    (hvalid : Valid s)
    (hred : Reduced s) :
    M (step s).a (step s).b ≤ M s.a s.b := by
  by_cases hgap : expGap s.a s.b = 0
  · have hbits : bitlen s.a = bitlen s.b := bitlen_eq_of_zeroGap hvalid.1 hgap
    have hsubbit : bitlen (s.a - s.b) < bitlen s.b :=
      same_bitlen_sub_smaller hvalid.1 hvalid.2 hbits
    rw [step_eq_sub_of_zeroGap hvalid hred hgap]
    unfold M
    rw [max_eq_left (le_of_lt hsubbit), hbits]
    simp
  · have hdrop := one_step_drop_of_posGap hvalid hred (Nat.pos_of_ne_zero hgap)
    omega

theorem one_step_eq_of_zeroGap
    {s : State}
    (hvalid : Valid s)
    (hred : Reduced s)
    (hgap : expGap s.a s.b = 0) :
    M (step s).a (step s).b = M s.a s.b := by
  have hbits : bitlen s.a = bitlen s.b := bitlen_eq_of_zeroGap hvalid.1 hgap
  have hsubbit : bitlen (s.a - s.b) < bitlen s.b :=
    same_bitlen_sub_smaller hvalid.1 hvalid.2 hbits
  rw [step_eq_sub_of_zeroGap hvalid hred hgap]
  unfold M
  rw [max_eq_left (le_of_lt hsubbit), hbits]
  simp

theorem next_posGap_of_zeroGap
    {s : State}
    (hvalid : Valid s)
    (hred : Reduced s)
    (hgap : expGap s.a s.b = 0) :
    0 < expGap (step s).a (step s).b := by
  have hbits : bitlen s.a = bitlen s.b := bitlen_eq_of_zeroGap hvalid.1 hgap
  have hsubbit : bitlen (s.a - s.b) < bitlen s.b :=
    same_bitlen_sub_smaller hvalid.1 hvalid.2 hbits
  rw [step_eq_sub_of_zeroGap hvalid hred hgap, expGap]
  exact Nat.sub_pos_of_lt hsubbit

theorem two_step_drop
    {s : State}
    (hsteps : Admits 2 s) :
    M (iterStep 2 s).a (iterStep 2 s).b + 1 ≤ M s.a s.b := by
  /-
    If the first step has positive exponent gap, it already drops `M` by at
    least `1`, and `one_step_nonincrease` handles the second step.

    If the first step has zero exponent gap, `next_posGap_of_zeroGap` shows the
    second step starts with positive exponent gap, so the second step drops by
    at least `1`.
  -/
  rcases hsteps with ⟨hvalid, hred, htail⟩
  have hvalid1 : Valid (step s) := htail.1
  have hred1 : Reduced (step s) := htail.2.1
  by_cases hgap : expGap s.a s.b = 0
  · have hdrop1 : M (iterStep 2 s).a (iterStep 2 s).b + 1 ≤ M (step s).a (step s).b := by
      simpa [iterStep] using
        one_step_drop_of_posGap hvalid1 hred1 (next_posGap_of_zeroGap hvalid hred hgap)
    have hmono0 : M (step s).a (step s).b ≤ M s.a s.b :=
      one_step_nonincrease hvalid hred
    omega
  · have hdrop0 : M (step s).a (step s).b + 1 ≤ M s.a s.b :=
      one_step_drop_of_posGap hvalid hred (Nat.pos_of_ne_zero hgap)
    have hmono1 : M (iterStep 2 s).a (iterStep 2 s).b ≤ M (step s).a (step s).b := by
      simpa [iterStep] using one_step_nonincrease hvalid1 hred1
    omega

/-!
## Obstruction block `0,1,0,1,0`

This section packages the local algebra used in the five-step argument.
The definitions match the English proof.
-/

namespace Obstruction

def D (A B : Nat) : Nat := A - B
def E (A B : Nat) : Nat := Nat.dist B (2 * D A B)
def X (A B : Nat) : Nat := Nat.dist (D A B) (E A B)
def Y (A B : Nat) : Nat := min (D A B) (E A B)
def Z (A B : Nat) : Nat := Nat.dist (Y A B) (2 * X A B)

theorem normal_form_cases
    {A B n : Nat}
    (hA : bitlen A = n + 1)
    (hB : bitlen B = n + 1)
    (hD : bitlen (D A B) = n)
    (hE : bitlen (E A B) = n)
    (hX : bitlen (X A B) = n - 1)
    (hZ : bitlen (Z A B) = n - 1) :
    ((D A B > E A B) ∧ (B < 2 * D A B) ∧
        D A B = Y A B + X A B ∧
        B = Y A B + 2 * X A B ∧
        A = 2 * Y A B + 3 * X A B) ∨
    ((D A B > E A B) ∧ (B > 2 * D A B) ∧
        D A B = Y A B + X A B ∧
        B = 3 * Y A B + 2 * X A B ∧
        A = 4 * Y A B + 3 * X A B) ∨
    ((E A B > D A B) ∧
        Y A B = D A B ∧
        B = 3 * Y A B + X A B ∧
        A = 4 * Y A B + X A B) := by
  have hAne : A ≠ 0 := by
    intro hAz
    simp [bitlen, hAz] at hA
  have hBne : B ≠ 0 := by
    intro hBz
    simp [bitlen, hBz] at hB
  have hApos : 0 < A := Nat.pos_of_ne_zero hAne
  have hBpos : 0 < B := Nat.pos_of_ne_zero hBne
  have hAupper : A < 2 ^ (n + 1) := by
    simpa [hA] using lt_pow_bitlen hApos
  have hBlower : 2 ^ n ≤ B := by
    simpa [hB] using pow_bitlen_pred_le hBpos
  have hA_lt_twoB : A < 2 * B := by
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
      rw [pow_succ, Nat.mul_comm]
    have h2pow_le : 2 * 2 ^ n ≤ 2 * B := Nat.mul_le_mul_left _ hBlower
    rw [hpow] at hAupper
    exact lt_of_lt_of_le hAupper h2pow_le
  have hD_lt_B : D A B < B := by
    unfold D
    omega
  have hAgeB : A ≥ B := by
    by_contra hlt
    have hDzero : D A B = 0 := by
      unfold D
      omega
    have hn0 : n = 0 := by
      have : bitlen (D A B) = 0 := by simpa [hDzero] using bitlen_zero
      omega
    have hEeqB : E A B = B := by
      unfold E
      simp [hDzero, Nat.dist]
    have hEzero : E A B = 0 := by
      apply (bitlen_eq_zero).mp
      simpa [hn0] using hE
    have hBzero : B = 0 := by
      simpa [hEeqB] using hEzero
    exact hBne hBzero
  have hA_from_D : A = B + D A B := by
    unfold D
    omega
  have hD_ne_E : D A B ≠ E A B := by
    intro hDEeq
    have hXzero : X A B = 0 := by
      unfold X
      simpa [hDEeq]
    have hZeq : Z A B = D A B := by
      unfold Z Y
      rw [hDEeq, min_self, hXzero]
      simp [Nat.dist]
    have hbit : bitlen (D A B) = n - 1 := by
      simpa [hZeq] using hZ
    have hn0 : n = 0 := by
      omega
    have hDzero : D A B = 0 := by
      apply (bitlen_eq_zero).mp
      simpa [hn0] using hD
    have hBzero : B = 0 := by
      have hEzero : E A B = 0 := by
        simpa [hDEeq] using hDzero
      unfold E at hEzero
      have : Nat.dist B 0 = 0 := by simpa [hDzero] using hEzero
      simpa [Nat.dist] using this
    exact hBne hBzero
  have hcmp : D A B > E A B ∨ E A B > D A B := by
    omega
  rcases hcmp with hDE | hED
  · have hYeq : Y A B = E A B := by
      unfold Y
      simp [Nat.le_of_lt hDE]
    have hXeq : X A B = D A B - E A B := by
      unfold X
      simpa [Nat.dist_comm] using
        (Nat.dist_eq_sub_of_le (Nat.le_of_lt hDE) :
          Nat.dist (E A B) (D A B) = D A B - E A B)
    have hBneq : B ≠ 2 * D A B := by
      intro hB2
      have h2D : 2 * D A B = B := hB2.symm
      have hEzero : E A B = 0 := by
        calc
          E A B = Nat.dist B (2 * D A B) := by rfl
          _ = Nat.dist B B := by rw [h2D]
          _ = 0 := by simp [Nat.dist]
      have hn0 : n = 0 := by
        have : bitlen (E A B) = 0 := by simpa [hEzero] using bitlen_zero
        omega
      have hDzero : D A B = 0 := by
        apply (bitlen_eq_zero).mp
        simpa [hn0] using hD
      have hBzero : B = 0 := by
        have : B = 2 * D A B := hB2
        rw [hDzero] at this
        omega
      exact hBne hBzero
    by_cases hBlt : B < 2 * D A B
    · have hEeq : E A B = 2 * D A B - B := by
        unfold E
        simpa using
          (Nat.dist_eq_sub_of_le (Nat.le_of_lt hBlt) :
            Nat.dist B (2 * D A B) = 2 * D A B - B)
      left
      refine ⟨hDE, hBlt, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
    · have hBgt : B > 2 * D A B := by
        omega
      have hEeq : E A B = B - 2 * D A B := by
        unfold E
        simpa [Nat.dist_comm] using
          (Nat.dist_eq_sub_of_le (Nat.le_of_lt hBgt) :
            Nat.dist (2 * D A B) B = B - 2 * D A B)
      right
      left
      refine ⟨hDE, hBgt, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
  · have hYeq : Y A B = D A B := by
      unfold Y
      simp [Nat.le_of_lt hED]
    have hXeq : X A B = E A B - D A B := by
      unfold X
      simpa using
        (Nat.dist_eq_sub_of_le (Nat.le_of_lt hED) :
          Nat.dist (D A B) (E A B) = E A B - D A B)
    have hBgt : B > 2 * D A B := by
      by_cases hBlt : B < 2 * D A B
      · have hEeq : E A B = 2 * D A B - B := by
          unfold E
          simpa using
            (Nat.dist_eq_sub_of_le (Nat.le_of_lt hBlt) :
              Nat.dist B (2 * D A B) = 2 * D A B - B)
        omega
      · by_cases hB2 : B = 2 * D A B
        · have hEzero : E A B = 0 := by
            have h2D : 2 * D A B = B := hB2.symm
            calc
              E A B = Nat.dist B (2 * D A B) := by rfl
              _ = Nat.dist B B := by rw [h2D]
              _ = 0 := by simp [Nat.dist]
          omega
        · omega
    have hEeq : E A B = B - 2 * D A B := by
      unfold E
      simpa [Nat.dist_comm] using
        (Nat.dist_eq_sub_of_le (Nat.le_of_lt hBgt) :
          Nat.dist (2 * D A B) B = B - 2 * D A B)
    right
    right
    refine ⟨hED, hYeq, ?_, ?_⟩
    · omega
    · omega

theorem caseII_impossible
    {A B n : Nat}
    (hA : bitlen A = n + 1)
    (hY : 2 ^ (n - 1) ≤ Y A B ∧ Y A B < 2 ^ n)
    (hX : 2 ^ (n - 2) ≤ X A B ∧ X A B < 2 ^ (n - 1))
    (hcase : E A B > D A B ∧
      Y A B = D A B ∧
      B = 3 * Y A B + X A B ∧
      A = 4 * Y A B + X A B) :
    False := by
  rcases hY with ⟨hYlo, hYhi⟩
  rcases hX with ⟨hXlo, _hXhi⟩
  rcases hcase with ⟨_hED, _hYD, _hB, hAeq⟩
  cases n with
  | zero =>
      omega
  | succ k =>
      have hXpos : 0 < X A B := lt_of_lt_of_le (pow_pos (by decide : 0 < 2) _) hXlo
      have hApos : 0 < A := by
        rw [hAeq]
        omega
      have hAupper : A < 2 ^ (k + 2) := by
        simpa [hA] using lt_pow_bitlen hApos
      have hpow4 : 4 * 2 ^ k = 2 ^ (k + 2) := by
        calc
          4 * 2 ^ k = 2 ^ 2 * 2 ^ k := by norm_num
          _ = 2 ^ (2 + k) := by rw [← pow_add]
          _ = 2 ^ (k + 2) := by rw [Nat.add_comm]
      have hAlower : 2 ^ (k + 2) < A := by
        rw [← hpow4, hAeq]
        have h4le : 4 * 2 ^ k ≤ 4 * Y A B := Nat.mul_le_mul_left _ hYlo
        exact lt_of_le_of_lt h4le (Nat.lt_add_of_pos_right hXpos)
      exact (not_lt_of_ge (Nat.le_of_lt hAlower)) hAupper

theorem caseIb_impossible
    {A B n : Nat}
    (hB : bitlen B = n + 1)
    (hY : 2 ^ (n - 1) ≤ Y A B ∧ Y A B < 2 ^ n)
    (hX : 2 ^ (n - 2) ≤ X A B ∧ X A B < 2 ^ (n - 1))
    (hcase : D A B > E A B ∧ B > 2 * D A B ∧
      D A B = Y A B + X A B ∧
      B = 3 * Y A B + 2 * X A B ∧
      A = 4 * Y A B + 3 * X A B) :
    False := by
  rcases hY with ⟨hYlo, hYhi⟩
  rcases hX with ⟨hXlo, _hXhi⟩
  rcases hcase with ⟨_hDE, _hBgt, _hD, hBeq, _hA⟩
  cases n with
  | zero =>
      omega
  | succ k =>
      have hBpos : 0 < B := by
        rw [hBeq]
        omega
      have hBupper : B < 2 ^ (k + 2) := by
        simpa [hB] using lt_pow_bitlen hBpos
      cases k with
      | zero =>
          have hBlower : 2 ^ 2 < B := by
            rw [hBeq]
            omega
          exact (not_lt_of_ge (Nat.le_of_lt hBlower)) hBupper
      | succ l =>
          have htwo : 2 ^ (l + 1) = 2 * 2 ^ l := by
            rw [pow_succ, Nat.mul_comm]
          have hcalc : 3 * 2 ^ (l + 1) + 2 * 2 ^ l = 8 * 2 ^ l := by
            rw [htwo]
            omega
          have hpow8 : 8 * 2 ^ l = 2 ^ (l + 3) := by
            calc
              8 * 2 ^ l = 2 ^ 3 * 2 ^ l := by norm_num
              _ = 2 ^ (3 + l) := by rw [← pow_add]
              _ = 2 ^ (l + 3) := by rw [Nat.add_comm]
          have hsum_le : 3 * 2 ^ (l + 1) + 2 * 2 ^ l ≤ 3 * Y A B + 2 * X A B := by
            exact Nat.add_le_add (Nat.mul_le_mul_left _ hYlo) (Nat.mul_le_mul_left _ hXlo)
          have hBlower : 2 ^ (l + 3) ≤ B := by
            rw [hBeq, ← hpow8, ← hcalc]
            exact hsum_le
          exact (not_lt_of_ge hBlower) hBupper

theorem caseIa_impossible
    {A B n : Nat}
    (hA : bitlen A = n + 1)
    (hY : 2 ^ (n - 1) ≤ Y A B ∧ Y A B < 2 ^ n)
    (hX : 2 ^ (n - 2) ≤ X A B ∧ X A B < 2 ^ (n - 1))
    (hZ : 2 ^ (n - 2) ≤ Z A B ∧ Z A B < 2 ^ (n - 1))
    (hcase : D A B > E A B ∧ B < 2 * D A B ∧
      D A B = Y A B + X A B ∧
      B = Y A B + 2 * X A B ∧
      A = 2 * Y A B + 3 * X A B) :
    False := by
  rcases hY with ⟨hYlo, _hYhi⟩
  rcases hX with ⟨hXlo, _hXhi⟩
  rcases hZ with ⟨hZlo, _hZhi⟩
  rcases hcase with ⟨_hDE, _hBlt, _hD, _hB, hAeq⟩
  cases n with
  | zero =>
      omega
  | succ k =>
      cases k with
      | zero =>
          have hApos : 0 < A := by
            rw [hAeq]
            omega
          have hAupper : A < 2 ^ 2 := by
            simpa [hA] using lt_pow_bitlen hApos
          have hAlower : 2 ^ 2 < A := by
            rw [hAeq]
            omega
          exact (not_lt_of_ge (Nat.le_of_lt hAlower)) hAupper
      | succ l =>
          let p : Nat := 2 ^ l
          have hp : 0 < p := by
            dsimp [p]
            exact pow_pos (by decide : 0 < 2) _
          have hYlo' : 2 * p ≤ Y A B := by
            dsimp [p]
            simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hYlo
          have hXlo' : p ≤ X A B := by
            dsimp [p]
            simpa using hXlo
          have hZlo' : p ≤ Z A B := by
            dsimp [p]
            simpa using hZlo
          have hpow8 : 8 * p = 2 ^ (l + 3) := by
            dsimp [p]
            calc
              8 * 2 ^ l = 2 ^ 3 * 2 ^ l := by norm_num
              _ = 2 ^ (3 + l) := by rw [← pow_add]
              _ = 2 ^ (l + 3) := by rw [Nat.add_comm]
          have hApos : 0 < A := by
            rw [hAeq]
            omega
          have hAupper : A < 8 * p := by
            have hlt : A < 2 ^ (l + 3) := by
              simpa [hA] using lt_pow_bitlen hApos
            simpa [hpow8] using hlt
          by_cases hXY : 2 * X A B ≤ Y A B
          · have hdist : Z A B = Y A B - 2 * X A B := by
              unfold Z
              simpa [Nat.dist_comm] using
                (Nat.dist_eq_sub_of_le hXY : Nat.dist (2 * X A B) (Y A B) = Y A B - 2 * X A B)
            have hZlo'' : p ≤ Y A B - 2 * X A B := by
              simpa [hdist] using hZlo'
            have hAlower : 8 * p < A := by
              rw [hAeq]
              omega
            exact (not_lt_of_ge (Nat.le_of_lt hAlower)) hAupper
          · have hXYlt : Y A B < 2 * X A B := by
              omega
            have hdist : Z A B = 2 * X A B - Y A B := by
              unfold Z
              simpa using
                (Nat.dist_eq_sub_of_le (Nat.le_of_lt hXYlt) :
                  Nat.dist (Y A B) (2 * X A B) = 2 * X A B - Y A B)
            have hZlo'' : p ≤ 2 * X A B - Y A B := by
              simpa [hdist] using hZlo'
            have hAlower : 8 * p < A := by
              rw [hAeq]
              omega
            exact (not_lt_of_ge (Nat.le_of_lt hAlower)) hAupper

theorem pattern01010_impossible
    {A B n : Nat}
    (hA : bitlen A = n + 1)
    (hB : bitlen B = n + 1)
    (hD : bitlen (D A B) = n)
    (hE : bitlen (E A B) = n)
    (hX : bitlen (X A B) = n - 1)
    (hZ : bitlen (Z A B) = n - 1) :
    False := by
  rcases normal_form_cases hA hB hD hE hX hZ with hIa | hIb | hII
  · rcases hIa with ⟨hDE, hBlt, hDYX, hBYX, hAYX⟩
    have hYeq : Y A B = E A B := by
      unfold Y
      simp [Nat.le_of_lt hDE]
    have hXpos : 0 < X A B := by
      omega
    have hEpos : 0 < E A B := by
      apply Nat.pos_of_ne_zero
      intro hE0
      have hn0 : n = 0 := by
        simp [hE0] at hE
        omega
      have hDzero : D A B = 0 := by
        apply (bitlen_eq_zero).mp
        simpa [hn0] using hD
      omega
    have hbitXpos : 0 < bitlen (X A B) := bitlen_pos hXpos
    have hn_ge_two : 2 ≤ n := by
      omega
    have hZpos : 0 < Z A B := by
      apply Nat.pos_of_ne_zero
      intro hZ0
      simp [bitlen, hZ0] at hZ
      omega
    have hYbounds : 2 ^ (n - 1) ≤ Y A B ∧ Y A B < 2 ^ n := by
      constructor
      · simpa [hYeq, hE] using pow_bitlen_pred_le hEpos
      · simpa [hYeq, hE] using lt_pow_bitlen hEpos
    have hXbounds : 2 ^ (n - 2) ≤ X A B ∧ X A B < 2 ^ (n - 1) := by
      constructor
      · simpa [hX] using pow_bitlen_pred_le hXpos
      · simpa [hX] using lt_pow_bitlen hXpos
    have hZbounds : 2 ^ (n - 2) ≤ Z A B ∧ Z A B < 2 ^ (n - 1) := by
      constructor
      · simpa [hZ] using pow_bitlen_pred_le hZpos
      · simpa [hZ] using lt_pow_bitlen hZpos
    exact caseIa_impossible hA hYbounds hXbounds hZbounds ⟨hDE, hBlt, hDYX, hBYX, hAYX⟩
  · rcases hIb with ⟨hDE, hBgt, hDYX, hBYX, hAYX⟩
    have hYeq : Y A B = E A B := by
      unfold Y
      simp [Nat.le_of_lt hDE]
    have hXpos : 0 < X A B := by
      omega
    have hEpos : 0 < E A B := by
      apply Nat.pos_of_ne_zero
      intro hE0
      have hn0 : n = 0 := by
        simp [hE0] at hE
        omega
      have hDzero : D A B = 0 := by
        apply (bitlen_eq_zero).mp
        simpa [hn0] using hD
      omega
    have hYbounds : 2 ^ (n - 1) ≤ Y A B ∧ Y A B < 2 ^ n := by
      constructor
      · simpa [hYeq, hE] using pow_bitlen_pred_le hEpos
      · simpa [hYeq, hE] using lt_pow_bitlen hEpos
    have hXbounds : 2 ^ (n - 2) ≤ X A B ∧ X A B < 2 ^ (n - 1) := by
      constructor
      · simpa [hX] using pow_bitlen_pred_le hXpos
      · simpa [hX] using lt_pow_bitlen hXpos
    exact caseIb_impossible hB hYbounds hXbounds ⟨hDE, hBgt, hDYX, hBYX, hAYX⟩
  · rcases hII with ⟨hED, hYD, hBYX, hAYX⟩
    have hXpos : 0 < X A B := by
      apply Nat.pos_of_ne_zero
      intro hX0
      unfold X at hX0
      have hpair : D A B - E A B = 0 ∧ E A B - D A B = 0 := by
        simpa [Nat.dist] using hX0
      have : D A B = E A B := by
        omega
      omega
    have hDpos : 0 < D A B := by
      apply Nat.pos_of_ne_zero
      intro hD0
      have hn0 : n = 0 := by
        simp [bitlen, hD0] at hD
        omega
      have hEzero : E A B = 0 := by
        apply (bitlen_eq_zero).mp
        simpa [hn0] using hE
      omega
    have hYbounds : 2 ^ (n - 1) ≤ Y A B ∧ Y A B < 2 ^ n := by
      constructor
      · simpa [hYD, hD] using pow_bitlen_pred_le hDpos
      · simpa [hYD, hD] using lt_pow_bitlen hDpos
    have hXbounds : 2 ^ (n - 2) ≤ X A B ∧ X A B < 2 ^ (n - 1) := by
      constructor
      · simpa [hX] using pow_bitlen_pred_le hXpos
      · simpa [hX] using lt_pow_bitlen hXpos
    exact caseII_impossible hA hYbounds hXbounds ⟨hED, hYD, hBYX, hAYX⟩

end Obstruction

/-!
## Five-step lemma

The next theorem is the algorithm-specific heart of the argument.

Its intended proof is exactly the English proof:

1. if a five-step block drops by at most `2`, its exponent-gap pattern must be
   alternating `0, >0, 0, >0, 0`;
2. in an alternating block the total drop is exactly `d₁ + d₂`;
3. therefore the only possible bad pattern is `0,1,0,1,0`;
4. Section `Obstruction` rules that pattern out.
-/

theorem five_step_drop
    {s : State}
    (hsteps : Admits 5 s) :
    M (iterStep 5 s).a (iterStep 5 s).b + 3 ≤ M s.a s.b := by
  let s0 := s
  let s1 := step s0
  let s2 := step s1
  let s3 := step s2
  let s4 := step s3
  let s5 := step s4
  have hs1 : Admits 4 s1 := by
    simpa [s0, s1] using admits_tail hsteps
  have hs2 : Admits 3 s2 := by
    simpa [s1, s2] using admits_tail hs1
  have hs3 : Admits 2 s3 := by
    simpa [s2, s3] using admits_tail hs2
  have hs4 : Admits 1 s4 := by
    simpa [s3, s4] using admits_tail hs3
  have hvalid0 : Valid s0 := by
    simpa [s0] using hsteps.1
  have hred0 : Reduced s0 := by
    simpa [s0] using hsteps.2.1
  have hvalid1 : Valid s1 := hs1.1
  have hred1 : Reduced s1 := hs1.2.1
  have hvalid2 : Valid s2 := hs2.1
  have hred2 : Reduced s2 := hs2.2.1
  have hvalid3 : Valid s3 := hs3.1
  have hred3 : Reduced s3 := hs3.2.1
  have hvalid4 : Valid s4 := hs4.1
  have hred4 : Reduced s4 := hs4.2.1
  have h02adm : Admits 2 s0 := by
    simpa [s0] using admits_take (m := 2) (n := 5) (s := s0) (by omega) hsteps
  have h12adm : Admits 2 s1 := admits_take (m := 2) (n := 4) (s := s1) (by omega) hs1
  have h22adm : Admits 2 s2 := admits_take (m := 2) (n := 3) (s := s2) (by omega) hs2
  by_cases hgap0 : expGap s0.a s0.b = 0
  · have h01eq : M s1.a s1.b = M s0.a s0.b := one_step_eq_of_zeroGap hvalid0 hred0 hgap0
    have hgap1 : 0 < expGap s1.a s1.b := next_posGap_of_zeroGap hvalid0 hred0 hgap0
    by_cases hgap2 : expGap s2.a s2.b = 0
    · have h23eq : M s3.a s3.b = M s2.a s2.b := one_step_eq_of_zeroGap hvalid2 hred2 hgap2
      have hgap3 : 0 < expGap s3.a s3.b := next_posGap_of_zeroGap hvalid2 hred2 hgap2
      by_cases hgap4 : expGap s4.a s4.b = 0
      · have h45eq : M s5.a s5.b = M s4.a s4.b := one_step_eq_of_zeroGap hvalid4 hred4 hgap4
        have h02 : M s2.a s2.b + 1 ≤ M s0.a s0.b := by
          simpa [s0, s1, s2] using two_step_drop h02adm
        have h24 : M s4.a s4.b + 1 ≤ M s2.a s2.b := by
          simpa [s2, s3, s4] using two_step_drop h22adm
        by_contra hlt
        have hnot3 : ¬ M s5.a s5.b + 3 ≤ M s0.a s0.b := by
          simpa [s0, s5] using hlt
        have hle2 : M s5.a s5.b + 2 ≤ M s0.a s0.b := by
          omega
        have hm0eq : M s0.a s0.b = M s5.a s5.b + 2 := by
          omega
        have hm2eq : M s2.a s2.b + 1 = M s0.a s0.b := by
          omega
        have hm4eq : M s4.a s4.b + 1 = M s2.a s2.b := by
          omega
        let n := M s2.a s2.b
        have hM0n : M s0.a s0.b = n + 1 := by
          dsimp [n] at hm2eq ⊢
          omega
        have hM4n : M s4.a s4.b = n - 1 := by
          dsimp [n] at hm4eq ⊢
          omega
        have hbits0 : bitlen s0.a = bitlen s0.b := bitlen_eq_of_zeroGap hvalid0.1 hgap0
        have hA : bitlen s0.a = n + 1 := by
          simpa [M, hbits0] using hM0n
        have hB : bitlen s0.b = n + 1 := by
          simpa [hbits0] using hA
        have hs1shape : s1 = { a := s0.b, b := s0.a - s0.b } := by
          simpa [s0, s1] using step_eq_sub_of_zeroGap hvalid0 hred0 hgap0
        have hs1a : s1.a = s0.b := by
          simpa [hs1shape]
        have hs1b : s1.b = Obstruction.D s0.a s0.b := by
          simpa [hs1shape, Obstruction.D]
        have hs2step : s2 = step0 s1 := by
          rw [show s2 = step s1 by rfl, step_eq_step0_of_reduced hvalid1 hred1]
        have hs2shape :
            s2 = { a := max (Obstruction.D s0.a s0.b) (residual s1)
                 , b := min (Obstruction.D s0.a s0.b) (residual s1) } := by
          rw [hs2step]
          simp [step0, hs1b]
        have hbits2 : bitlen s2.a = bitlen s2.b := bitlen_eq_of_zeroGap hvalid2.1 hgap2
        have hs2abit : bitlen s2.a = n := by
          simp [n, M, hbits2]
        have hs2bbit : bitlen s2.b = n := by
          simpa [hbits2] using hs2abit
        have hDres :
            bitlen (Obstruction.D s0.a s0.b) = n ∧ bitlen (residual s1) = n := by
          have hmax : bitlen (max (Obstruction.D s0.a s0.b) (residual s1)) = n := by
            simpa [hs2shape] using hs2abit
          have hmin : bitlen (min (Obstruction.D s0.a s0.b) (residual s1)) = n := by
            simpa [hs2shape] using hs2bbit
          exact bitlen_max_min_eq hmax hmin
        have hD : bitlen (Obstruction.D s0.a s0.b) = n := hDres.1
        have hres1 : bitlen (residual s1) = n := hDres.2
        have hgap1eq1 : expGap s1.a s1.b = 1 := by
          unfold expGap
          rw [hs1a, hs1b, hB, hD]
          omega
        have hgapBD : expGap s0.b (Obstruction.D s0.a s0.b) = 1 := by
          simpa [hs1a, hs1b] using hgap1eq1
        have hres1E : residual s1 = Obstruction.E s0.a s0.b := by
          unfold residual Obstruction.E
          rw [hs1a, hs1b, hgapBD]
          simp [Obstruction.D, pow_one, Nat.mul_comm]
        have hE : bitlen (Obstruction.E s0.a s0.b) = n := by
          simpa [hres1E] using hres1
        have hs2shapeDE :
            s2 = { a := max (Obstruction.D s0.a s0.b) (Obstruction.E s0.a s0.b)
                 , b := min (Obstruction.D s0.a s0.b) (Obstruction.E s0.a s0.b) } := by
          simpa [hres1E] using hs2shape
        have hs3shape : s3 = { a := s2.b, b := s2.a - s2.b } := by
          simpa [s2, s3] using step_eq_sub_of_zeroGap hvalid2 hred2 hgap2
        have hs3aY : s3.a = Obstruction.Y s0.a s0.b := by
          rw [hs3shape, hs2shapeDE]
          unfold Obstruction.Y
          simp
        have hs3bX : s3.b = Obstruction.X s0.a s0.b := by
          rw [hs3shape, hs2shapeDE]
          unfold Obstruction.X
          rw [dist_eq_max_sub_min]
        have hs3abit : bitlen s3.a = n := by
          rw [hs3shape]
          exact hs2bbit
        have hY : bitlen (Obstruction.Y s0.a s0.b) = n := by
          rw [← hs3aY]
          exact hs3abit
        have hs4step : s4 = step0 s3 := by
          rw [show s4 = step s3 by rfl, step_eq_step0_of_reduced hvalid3 hred3]
        have hs4shape :
            s4 = { a := max (Obstruction.X s0.a s0.b) (residual s3)
                 , b := min (Obstruction.X s0.a s0.b) (residual s3) } := by
          rw [hs4step]
          simp [step0, hs3bX]
        have hbits4 : bitlen s4.a = bitlen s4.b := bitlen_eq_of_zeroGap hvalid4.1 hgap4
        have hs4abit : bitlen s4.a = n - 1 := by
          simpa [M, hbits4] using hM4n
        have hs4bbit : bitlen s4.b = n - 1 := by
          simpa [hbits4] using hs4abit
        have hXres :
            bitlen (Obstruction.X s0.a s0.b) = n - 1 ∧ bitlen (residual s3) = n - 1 := by
          have hmax : bitlen (max (Obstruction.X s0.a s0.b) (residual s3)) = n - 1 := by
            simpa [hs4shape] using hs4abit
          have hmin : bitlen (min (Obstruction.X s0.a s0.b) (residual s3)) = n - 1 := by
            simpa [hs4shape] using hs4bbit
          exact bitlen_max_min_eq hmax hmin
        have hX : bitlen (Obstruction.X s0.a s0.b) = n - 1 := hXres.1
        have hres3 : bitlen (residual s3) = n - 1 := hXres.2
        have hgap3eq1 : expGap s3.a s3.b = 1 := by
          unfold expGap
          rw [hs3aY, hs3bX, hY, hX]
          omega
        have hgapYX : expGap (Obstruction.Y s0.a s0.b) (Obstruction.X s0.a s0.b) = 1 := by
          simpa [hs3aY, hs3bX] using hgap3eq1
        have hres3Z : residual s3 = Obstruction.Z s0.a s0.b := by
          unfold residual Obstruction.Z
          rw [hs3aY, hs3bX, hgapYX]
          simp [Nat.mul_comm, pow_one]
        have hZ : bitlen (Obstruction.Z s0.a s0.b) = n - 1 := by
          simpa [hres3Z] using hres3
        exact False.elim (Obstruction.pattern01010_impossible hA hB hD hE hX hZ)
      · have h02 : M s2.a s2.b + 1 ≤ M s0.a s0.b := by
          simpa [s0, s1, s2] using two_step_drop h02adm
        have h24 : M s4.a s4.b + 1 ≤ M s2.a s2.b := by
          simpa [s2, s3, s4] using two_step_drop h22adm
        have h45 : M s5.a s5.b + 1 ≤ M s4.a s4.b := by
          exact one_step_drop_of_posGap hvalid4 hred4 (Nat.pos_of_ne_zero hgap4)
        have : M s5.a s5.b + 3 ≤ M s0.a s0.b := by
          omega
        simpa [s0, s1, s2, s3, s4, s5, iterStep] using this
    · have h02 : M s2.a s2.b + 1 ≤ M s0.a s0.b := by
        simpa [s0, s1, s2] using two_step_drop h02adm
      have h23 : M s3.a s3.b + 1 ≤ M s2.a s2.b := by
        exact one_step_drop_of_posGap hvalid2 hred2 (Nat.pos_of_ne_zero hgap2)
      have h35 : M s5.a s5.b + 1 ≤ M s3.a s3.b := by
        simpa [s3, s4, s5] using two_step_drop hs3
      have : M s5.a s5.b + 3 ≤ M s0.a s0.b := by
        omega
      simpa [s0, s1, s2, s3, s4, s5, iterStep] using this
  · have h01 : M s1.a s1.b + 1 ≤ M s0.a s0.b := by
      exact one_step_drop_of_posGap hvalid0 hred0 (Nat.pos_of_ne_zero hgap0)
    have h13 : M s3.a s3.b + 1 ≤ M s1.a s1.b := by
      simpa [s1, s2, s3] using two_step_drop h12adm
    have h35 : M s5.a s5.b + 1 ≤ M s3.a s3.b := by
      simpa [s3, s4, s5] using two_step_drop hs3
    have : M s5.a s5.b + 3 ≤ M s0.a s0.b := by
      omega
    simpa [s0, s1, s2, s3, s4, s5, iterStep] using this

/-!
## Arithmetic assembly of the strong bound
-/

lemma rho_bound_small : ∀ r : Nat, r < 5 → rho r ≤ 2
  | 0, _ => by simp [rho]
  | 1, _ => by simp [rho]
  | 2, _ => by simp [rho]
  | 3, _ => by simp [rho]
  | 4, _ => by simp [rho]
  | r + 5, hr => by omega

lemma iterStep_add (m n : Nat) (s : State) :
    iterStep (m + n) s = iterStep n (iterStep m s) := by
  induction m generalizing s with
  | zero =>
      simp [iterStep]
  | succ m ih =>
      simp [Nat.succ_add, iterStep, ih]

lemma admits_iterStep {m n : Nat} {s : State} (h : Admits (m + n) s) :
    Admits n (iterStep m s) := by
  induction m generalizing s with
  | zero =>
      simpa [iterStep] using h
  | succ m ih =>
      have htail : Admits (m + n) (step s) := by
        have : Admits (Nat.succ (m + n)) s := by
          simpa [Nat.succ_add] using h
        exact admits_tail this
      simpa [iterStep] using ih htail

lemma M_iterStep_le {n : Nat} {s : State} (h : Admits n s) :
    M (iterStep n s).a (iterStep n s).b ≤ M s.a s.b := by
  induction n generalizing s with
  | zero =>
      simp [iterStep]
  | succ n ih =>
      rcases h with ⟨hvalid, hred, htail⟩
      have h1 : M (step s).a (step s).b ≤ M s.a s.b :=
        one_step_nonincrease hvalid hred
      have h2 : M (iterStep n (step s)).a (iterStep n (step s)).b ≤ M (step s).a (step s).b :=
        ih htail
      simpa [iterStep] using le_trans h2 h1

lemma minDropStrong_add_five (n : Nat) :
    minDropStrong (5 + n) = 3 + minDropStrong n := by
  let q := n / 5
  let r := n % 5
  have hr : r < 5 := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  have hn : n = r + q * 5 := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.mod_add_div n 5).symm
  rw [hn]
  have hfive : 5 + (r + q * 5) = r + (q + 1) * 5 := by
    omega
  rw [hfive, minDropStrong, minDropStrong]
  rw [Nat.add_mul_div_right r (q + 1) (by omega), Nat.add_mul_mod_self_right]
  rw [Nat.add_mul_div_right r q (by omega), Nat.add_mul_mod_self_right]
  rw [Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
  interval_cases r <;> simp [rho] <;> omega

theorem strong_bound
    {s : State}
    {n : Nat}
    (hsteps : Admits n s) :
    minDropStrong n ≤ topDrop s n := by
  have hmain : ∀ n : Nat, ∀ s : State, Admits n s → minDropStrong n ≤ topDrop s n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih s hsteps
    by_cases hsmall : n < 5
    · interval_cases n
      · simp [minDropStrong, topDrop, rho]
      · simp [minDropStrong, topDrop, rho]
      · have h2drop : M (iterStep 2 s).a (iterStep 2 s).b + 1 ≤ M s.a s.b := two_step_drop hsteps
        have : 1 ≤ topDrop s 2 := by
          unfold topDrop
          omega
        simpa [minDropStrong, rho] using this
      · have h2adm : Admits 2 s := admits_take (m := 2) (n := 3) (s := s) (by omega) hsteps
        have h1adm : Admits 1 (iterStep 2 s) := by
          simpa [iterStep_add] using (admits_iterStep (m := 2) (n := 1) hsteps)
        have h2 : M (iterStep 2 s).a (iterStep 2 s).b + 1 ≤ M s.a s.b := two_step_drop h2adm
        have hmono : M (iterStep 3 s).a (iterStep 3 s).b ≤ M (iterStep 2 s).a (iterStep 2 s).b := by
          exact M_iterStep_le h1adm
        have : 1 ≤ topDrop s 3 := by
          unfold topDrop
          omega
        simpa [minDropStrong, rho] using this
      · have h2adm : Admits 2 s := admits_take (m := 2) (n := 4) (s := s) (by omega) hsteps
        have h2tail : Admits 2 (iterStep 2 s) := by
          simpa [iterStep_add] using (admits_iterStep (m := 2) (n := 2) hsteps)
        have h02 : M (iterStep 2 s).a (iterStep 2 s).b + 1 ≤ M s.a s.b := two_step_drop h2adm
        have h24 : M (iterStep 2 (iterStep 2 s)).a (iterStep 2 (iterStep 2 s)).b + 1 ≤
            M (iterStep 2 s).a (iterStep 2 s).b := two_step_drop h2tail
        have hiter : iterStep 4 s = iterStep 2 (iterStep 2 s) := by
          simpa using (iterStep_add 2 2 s)
        have : 2 ≤ topDrop s 4 := by
          unfold topDrop
          rw [hiter]
          omega
        simpa [minDropStrong, rho] using this
    · have hge : 5 ≤ n := by
        omega
      rcases Nat.exists_eq_add_of_le hge with ⟨m, rfl⟩
      have h5adm : Admits 5 s := admits_take (m := 5) (n := 5 + m) (s := s) (by omega) hsteps
      have hrest : Admits m (iterStep 5 s) := by
        simpa [iterStep_add] using (admits_iterStep (m := 5) (n := m) hsteps)
      have hind : minDropStrong m ≤ topDrop (iterStep 5 s) m := by
        exact ih m (by omega) (iterStep 5 s) hrest
      have h5drop : M (iterStep 5 s).a (iterStep 5 s).b + 3 ≤ M s.a s.b := five_step_drop h5adm
      have hmono : M (iterStep m (iterStep 5 s)).a (iterStep m (iterStep 5 s)).b ≤
          M (iterStep 5 s).a (iterStep 5 s).b := M_iterStep_le hrest
      have hrestdrop :
          minDropStrong m ≤
            M (iterStep 5 s).a (iterStep 5 s).b - M (iterStep m (iterStep 5 s)).a
              (iterStep m (iterStep 5 s)).b := by
        simpa [topDrop] using hind
      have hcombine :
          3 + minDropStrong m ≤
            M s.a s.b - M (iterStep m (iterStep 5 s)).a (iterStep m (iterStep 5 s)).b := by
        omega
      rw [minDropStrong_add_five]
      simpa [topDrop, iterStep_add, Nat.add_comm] using hcombine
  exact hmain n s hsteps

/-!
## Admissibility statement

This is the form needed by the reverse search.

Let `current` be a reverse-search node and `start` a hypothetical ancestor
at reverse distance `n`. If there were such an ancestor inside the `k`-bit
box, then there would be a forward trajectory `start -> ... -> current` of
length `n`.

The strong bound says that every such trajectory drops by at least
`minDropStrong n`. But if `M start.a start.b ≤ k` and `current.a ≥ current.b`,
then the total drop is at most `k - bitlen current.a`.

Therefore, if `k - bitlen current.a < minDropStrong n`, no such ancestor can
exist. Equivalently, reverse search may prune `current` at depth `n`.
-/

theorem admissible_prune
    {start current : State}
    {k n : Nat}
    (hsteps : Admits n start)
    (hend : iterStep n start = current)
    (hbox : M start.a start.b ≤ k)
    (hcurrent : current.a ≥ current.b)
    (hdelta : k - bitlen current.a < minDropStrong n) :
    False := by
  have hstrong : minDropStrong n ≤ topDrop start n := strong_bound hsteps
  have hdrop : minDropStrong n ≤ M start.a start.b - M current.a current.b := by
    simpa [topDrop, hend] using hstrong
  have hcurM : M current.a current.b = bitlen current.a := by
    unfold M
    exact max_eq_left (bitlen_monotone hcurrent)
  have hupper : M start.a start.b - M current.a current.b ≤ k - bitlen current.a := by
    rw [hcurM]
    omega
  have : minDropStrong n ≤ k - bitlen current.a := le_trans hdrop hupper
  omega

end StrongBound
