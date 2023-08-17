import Mathlib.Tactic

#check RatFunc

-- this is a random comment

-- wrote Kloosterman stuff

-- inductive
-- valuation ring
-- mathlib4/mathlib/numbertheory/lucasprimality.lean
open Complex

noncomputable section

def eZMod (q : ℕ) (x : ZMod q) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x.val / q)

variable (q : ℕ) (x : ZMod q) (y : ℤ)

lemma eZMod_def : eZMod q x = Complex.exp (2 * Real.pi * Complex.I * x.val / q) := rfl

example (a : ℤ) : a / 0 = 0 := by exact Int.ediv_zero a

lemma intToComplex (r : ℤ) : ((r : ℝ) : ℂ) = r := rfl

lemma bar (a b : ℕ) (q : ℕ) (hq : q ≠ 0) (ha : a < q) (hab : a ≡ b [MOD q]) :
    ∃ n, b = a + n * q := by
  simp [Nat.ModEq] at hab
  rw [Nat.mod_eq_of_lt ha] at hab
  rw [hab]
  use b / q
  exact Eq.symm (Nat.mod_add_div' b q)

lemma foo (a b : ℕ) (q : ℕ) (hq : q ≠ 0) (ha : a < q) (hb : b < q + q)
    (hcong : a ≡ b [MOD q]) : b = a ∨ b = a + q := by
  obtain ⟨n, hn⟩ := bar a b q hq ha hcong
  rcases n with (rfl | rfl | n)
  · left
    simpa using hn
  · right
    simp [show Nat.succ 0 = 1 by rfl] at hn
    simpa using hn
  · exfalso
    change b = a + (n + 2) * q at hn
    rw [add_mul, two_mul] at hn
    subst hn
    rw [← add_assoc] at hb
    have foo : q + q ≤ a + n * q + (q + q) := by exact Nat.le_add_left (q + q) (a + n * q) 
    linarith
    done    

lemma ZMod.val_add_val (x y : ZMod q) [NeZero q] : x.val + y.val = (x+y).val ∨ x.val + y.val = (x+y).val + q := by
  apply foo
  · exact NeZero.ne q
  · exact val_lt (x + y)
  · apply add_lt_add
    · apply val_lt
    · apply val_lt 
  · suffices (val (x + y) : ZMod q) = ((val x + val y : ℕ) : ZMod q) by
      exact Iff.mp (nat_cast_eq_nat_cast_iff (val (x + y)) (val x + val y) q) this
    simp
  done

/- originally had `lemma eZMod_add (x y : ZMod q) : eZMod q (x + y) = eZMod q x * eZMod q y`
but erased `x` because the lemma took in two x 

-/
lemma eZMod_add (y : ZMod q) : eZMod q (x + y) = eZMod q x * eZMod q y := by
  simp only [eZMod_def]
  rw [← Complex.exp_add]
  rw [exp_eq_exp_iff_exists_int]
  by_cases hq : q = 0
  · subst hq
    simp
  · have : NeZero q := ⟨hq⟩
    cases' ZMod.val_add_val q x y with h1 h2
    · change q ≠ 0 at hq
      use 0
      rw [← h1]
      simp
      field_simp [hq] 
      ring
    · use -1
      change q ≠ 0 at hq
      clear this
      field_simp [hq]
      rw [← mul_add]
      norm_cast
      rw [h2]
      push_cast
      ring

instance (q : ℕ) : Fintype (ZMod q)ˣ := by
  cases q
  · change Fintype (ℤ)ˣ
    infer_instance
  · infer_instance 

open BigOperators

def kloostermanSum (a : ℤ) (b : ℤ) (q : ℕ) : ℂ :=
  ∑ x : (ZMod q)ˣ, eZMod q (a*x + b*x⁻¹)

--@[simp] lemma GaussianInt.toComplex_eq_cast (a : ZMod q) :
--    GaussianInt.toComplex (a : GaussianInt) = ZMod.cast a := sorry

section Elementary
-- depends only on the residue class of a and b modulo m
lemma zmod_eq_kloostermanSum (a : ℤ) (b : ℤ) (q : ℕ) : kloostermanSum a b q = kloostermanSum (a + q) (b + q) q := by
  simp only [kloostermanSum]
  apply congr_arg
  apply funext
  intro x
  simp

-- as x goes through the complete residue system mod p^α, x⁻¹ goes through the complete residue system mod p^α 
-- lemma lemma_2_1 (α : ℕ) (p : ℕ) [Fact p.Prime] : Set (ZMod (p^α : ℕ))ˣ = {x⁻¹ | x ∈ (ZMod (p^α : ℕ)ˣ)} := by
-- generalized version of lemma1_1
lemma congr_eq_kloostermanSum (a₁ : ℤ) (b₁ : ℤ) (a₂ : ℤ) (b₂ : ℤ) (q : ℕ) (ha₁a₂ : a₁ ≡ a₂ [ZMOD q]) (hb₁b₂ : b₁ ≡ b₂ [ZMOD q]) : kloostermanSum a₁ b₁ q = kloostermanSum a₂ b₂ q := by
  simp only [kloostermanSum]
  apply congr_arg
  apply funext
  intro x
  rw [← ZMod.int_cast_eq_int_cast_iff] at ha₁a₂ hb₁b₂
  rw [ha₁a₂, hb₁b₂]

theorem abSwitch (a : ℤ) (b : ℤ) (q : ℕ) : kloostermanSum a b q = kloostermanSum b a q := by
  simp only [kloostermanSum]
  -- sends x to x⁻¹ in the sum
  apply Finset.sum_bij (fun i _ ↦ i⁻¹)
  · simp
  · intro 
    norm_num
    ring
  · intro a₁ a₂ _ _
    field_simp
  · intro b _
    use b⁻¹
    norm_num

-- link ℤ → ℕ via congruence ZMod q
lemma congr_IntToNat {q : ℕ} (a : ℤ) (haq : ((a : ZMod q).val).gcd q = 1) [NeZero q]: ∃(a₁ : ℕ), (a₁.coprime q) ∧ (a ≡ a₁ [ZMOD q]) := by
  use (a : ZMod q).val
  apply And.intro
  · exact haq
  · rw [← ZMod.int_cast_eq_int_cast_iff]
    simp

-- (haq : a.gcd q = 1)
-- link ℤ → ℕ → (ZMod q)ˣ via congruence ZMod q
lemma congr_IntToUnitZMod {q : ℕ} (a : ℤ) (haq : ((a : ZMod q).val).gcd q = 1) [h: NeZero q] : ∃(a' : (ZMod q)ˣ), a ≡ a' [ZMOD q] := by
  have toNatural := congr_IntToNat a haq
  rcases toNatural with ⟨a₁, a₁_coprime_q, congr_a₁⟩
  use ZMod.unitOfCoprime a₁ a₁_coprime_q
  simp only [ZMod.coe_unitOfCoprime]
  rw [← ZMod.int_cast_eq_int_cast_iff] at *
  simp at *
  assumption

-- changed plan and decided to make `a' b' : (ZMod q)ˣ` instead `a' b' : ℕ`
-- I'm sticking to this plan
theorem metamorphosis {q : ℕ} (a : ℤ) (b : ℤ) (haq : ((a : ZMod q).val).gcd q = 1) (hbq : ((b : ZMod q).val).gcd q = 1) [h: NeZero q] : 
    kloostermanSum a b q = kloostermanSum 1 (a*b) q  := by
  have a_toUnitZmod := congr_IntToUnitZMod a haq
  cases' a_toUnitZmod with a' congr_a
  have b_toUnitZmod := congr_IntToUnitZMod b hbq
  cases' b_toUnitZmod with b' congr_b
  
  rw [congr_eq_kloostermanSum a b a' b' q]
  rw [congr_eq_kloostermanSum 1 (a*b) 1 (a'*b') q]
  simp only [kloostermanSum]
  apply Finset.sum_bij (fun i _ ↦ a'*i)
  · intro _ _
    simp only [Finset.mem_univ]
  · intro c _
    norm_num
    rw [← mul_assoc]
    simp [mul_comm, mul_assoc] -- `rw [mul_comm]` doesn't work somehow
  · intro a₁ a₂ _ _ ha
    simp only [mul_right_inj] at ha 
    exact ha
  · intro c _
    have ha'c : a'⁻¹ * c ∈ Finset.univ := by simp only [Finset.mem_univ]
    use (a'⁻¹*c)
    use ha'c
    simp only [mul_inv_cancel_left]
  · rfl
  · exact Int.ModEq.mul congr_a congr_b
  · assumption
  · assumption

end Elementary
/- 
 -- K(ac, b; m) = K(a, bc; m) if gcd(c, m) = 1
lemma lemma3_2 (a : ℤ) (b : ℤ) (q : ℕ) (gcd_cq : c.gcd q = 1) : kloostermanSum (a*c) b q = kloostermanSum a (b*c) q  := by
  simp only [kloostermanSum]
  simp
  -- sends x to (c⁻¹*x⁻¹) in the sum
  sorry

-- Kloosterman sum is multiplicative
theorem theorem1 (a : ℤ) (b : ℤ) (q : ℕ) (b₁ : ℤ) (b₂ : ℤ) (q₁ : ℕ) (q₂ : ℕ) (hb : b = b₁*q₂^2 + b₂*q₁^2) (hq : q = q₁ * q₂) (gcd_q : q₁.gcd q₂ = 1): kloostermanSum a b m = (kloostermanSum a b m₁) * (kloostermanSum a b m₂) := by 
  sorry

-/

-- proper Iwaniec and Kowalski proof starts from here

/- Questions to Kevin
1. Whenever I change the name for the theorems, is it possible to make a corresponding change in the remaining bits of the code?
2. 



-/