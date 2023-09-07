import Mathlib.Tactic
import Kloosterman.def2_v3_kloosterman

/- makeshift for the last line of the proof of `ofunity` before we fix the bug in power notation in mathlib -/
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-!
## Main declarations

* theorem `MulChar_additive` : additive property of the character χ (1 + z * p ^ α) modulo p ^ (2 * α)
* theorem `MulChar_additive_eq_exp_for_all` which is the proof to the following statement : 
Clearly χ(1+z*p^α) is an additive character to modulus p^α, so there exists an integer b (uniquely determined modulo p ^ α) such that 
(12.27) χ (1 + z * p ^ α) = eZMod (p ^ α : ℕ) (b * z)

-/

open Complex

noncomputable section

variable {p : ℕ} {α : ℕ} (z : ZMod (p ^ α)) (χ : MulChar (ZMod (p ^ (2 * α))) ℂ)

/- defines an additive character χ' from multiplicative character χ -/
def χ' : ZMod (p ^ α) → ℂ :=
  fun z => χ (1 + z * (p ^ α : ZMod (p ^ (2 * α)))) 

/- checks whether the character χ' is well-defined -/ 
-- tried out `z.val` -- which turned out to be a bad choice 
theorem chi_prime_well_defined : χ' χ z = χ (1 + z * (p ^ α : ZMod (p ^ (2 * α)))) := rfl

/- previous version
lemma primePow_add_eq_coe_add (z₁ z₂ : ZMod (p ^ α)) :
    (p : ZMod (p ^ (2 * α))) ^ α * (z₁ : ZMod (p ^ (2 * α))) + (p : ZMod (p ^ (2 * α))) ^ α * (z₂ : ZMod (p ^ (2 * α))) 
    = (p: ZMod (p ^ (2 * α))) ^ α * ((z₁ + z₂ : ZMod (p ^ α)) : ZMod (p ^ (2 * α))) := by
  rw [← ZMod.int_cast_cast (z₁ + z₂)]
  rw [ZMod.coe_add_eq_ite]
  split
  · rw [Nat.cast_pow, Int.cast_sub, Int.cast_add, ZMod.int_cast_cast, Int.cast_pow, Int.cast_ofNat, 
    mul_sub, mul_add, ← pow_add, ← two_mul]
    norm_cast
    rw [ZMod.nat_cast_self]
    simp
  · push_cast
    simp only [ZMod.int_cast_cast]
    ring
-/

lemma primePow_add_eq_coe_add (z₁ z₂ : ZMod (p ^ α)) :
    (p ^ α : ZMod (p ^ (2 * α))) * ((z₁ : ZMod (p ^ (2 * α))) + (z₂ : ZMod (p ^ (2 * α))))
    = (p ^ α : ZMod (p ^ (2 * α))) * ((z₁ + z₂ : ZMod (p ^ α)) : ZMod (p ^ (2 * α))) := by
  rw [← ZMod.int_cast_cast (z₁ + z₂)]
  rw [ZMod.coe_add_eq_ite]
  split
  · rw [Nat.cast_pow, Int.cast_sub, Int.cast_add, Int.cast_ofNat]
    simp only [ZMod.int_cast_cast]
    rw [mul_sub, Nat.cast_pow, ← pow_two, ← pow_mul, mul_comm α 2]
    norm_cast
    rw [ZMod.nat_cast_self, sub_zero]
  · push_cast
    simp only [ZMod.int_cast_cast]

-- Clearly χ(1+z*p^α) is an additive character to modulus p^α
lemma MulChar_additive (z₁ z₂ : ZMod (p ^ α)) :
    χ' χ z₁ * χ' χ z₂ = χ' χ (z₁ + z₂) := by
  simp only [chi_prime_well_defined, Nat.cast_pow]
  rw [← map_mul]
  apply congr_arg
  rw [add_mul]
  simp only [mul_add, mul_one]
  rw [one_mul]
  nth_rw 2 [mul_comm (z₂ : ZMod (p ^ (2 * α)))]
  rw [mul_assoc, ← mul_assoc ((p : ZMod (p ^ (2 * α))) ^ α), ← pow_two, ← pow_mul, mul_comm α 2]
  norm_cast
  rw [ZMod.nat_cast_self, zero_mul, mul_zero, add_zero, add_assoc, add_comm ((z₂ : ZMod (p ^ (2 * α))) * (p ^ α : ZMod (p ^ (2 * α)))), ← add_mul]
  simp only [mul_comm]
  rw [primePow_add_eq_coe_add z₁ z₂]

/- when evaluated at 0, χ' is equal to 1 -/
theorem MulChar_zero : χ' χ 0 = 1 := by
  rw [chi_prime_well_defined]
  norm_num

-- feel like there's something in the mathlib for this
theorem MulChar_additive_pow (n : ℕ) :
    (χ' χ z) ^ n = (χ' χ (n * z)) := by
  induction' n with n ihn
  · norm_num
    exact Eq.symm (MulChar_zero χ)
  · norm_num
    norm_cast
    rw [pow_add (χ' χ z) n 1, ihn, pow_one, Nat.cast_add, Nat.cast_one, MulChar_additive]
    push_cast
    ring

theorem MulChar_equal_one : (χ' χ z) ^ (p ^ α) = 1 := by
  rw [MulChar_additive_pow]
  rw [chi_prime_well_defined]
  norm_num

variable [pp : Fact p.Prime]

instance : NeZero (p ^ α) := by exact NeZero.pow
  
-- need `[NeZero (p^α : ℕ)]`
theorem MulChar_additive_pow_val :
    (χ' χ 1) ^ z.val = χ' χ z := by
  rw [MulChar_additive_pow]
  apply congr_arg
  norm_num

/- χ is nonzero when a is coprime to p -/
lemma MulChar_nonZero {a : ZMod (p^(2*α) : ℕ)} (h : IsUnit a) : χ a ≠ 0 := by
  rw [← isUnit_iff_ne_zero]
  -- apply Iff.mp isUnit_iff_ne_zero
  exact IsUnit.map χ h

/- χ' is nonzero when evaluated at 1 -/
lemma MulChar_one_nonZero : χ' χ 1 ≠ 0 := by
  rw [chi_prime_well_defined]
  have h : IsUnit ((1 + (1 : ZMod (p^α : ℕ)) * ↑(p ^ α)) : ZMod (p^(2*α) : ℕ))
  { rw [isUnit_iff_exists_inv]
    use (1 - (1 : ZMod (p ^ α)) * p ^ α)
    rw [add_mul]
    simp only [mul_sub, mul_one]
    nth_rw 4 [mul_comm ((1 : ZMod (p ^ α)) : ZMod (p ^ (2 * α))) (p ^ α : ZMod (p ^ (2 * α)))]
    rw [mul_assoc ((1 : ZMod (p ^ α)) : ZMod (p ^ (2 * α))) (p ^ α : ZMod (p ^ (2 * α)))]
    rw [← mul_assoc (p ^ α : ZMod (p ^ (2 * α)))]
    rw [← pow_two]
    push_cast
    rw [← pow_mul, mul_comm α 2]
    norm_cast
    rw [ZMod.nat_cast_self, zero_mul, mul_zero, sub_zero, one_mul, sub_add_cancel] }
  exact MulChar_nonZero χ h

/- χ' evaluated at 1 is an unit -/
lemma MulChar_one_Unit : IsUnit (χ' χ 1 : ℂ) := by
  apply Ne.isUnit
  exact MulChar_one_nonZero χ

lemma congr_val (q : ℕ) (x₁ x₂ : ZMod q) : 
    (x₁ * x₂).val ≡ x₁.val * x₂.val [MOD q] := by
  rw [ZMod.val_mul x₁ x₂]
  exact Nat.mod_modEq (x₁.val * x₂.val) q

lemma complex_eq_congr (q : ℕ) (x₁ x₂ : ℕ) (congr_h : x₁ ≡ x₂ [ZMOD q]) : 
    ∃(c : ℤ), (x₁ : ℂ) = (x₂ : ℂ) + c * (q : ℤ) := by
    rw [Int.cast_ofNat]
    rw [Int.modEq_iff_add_fac] at congr_h
    cases' congr_h with t ht
    use (- t)
    norm_cast
    simp only [neg_mul]
    apply eq_sub_of_add_eq
    rw [mul_comm]
    symm
    exact ht  

-- NeZero q
-- change the code if possible
lemma cexp_congr_eq (q : ℕ) (x₁ x₂ : ℕ) (h_congr : x₁ ≡ x₂ [ZMOD q]) [NeZero q]: 
    Complex.exp (2 * Real.pi * Complex.I * x₁ / q) = Complex.exp (2 * Real.pi * Complex.I * x₂ / q) := by
  -- apply congr_arg
  -- originally, we had (c : ℕ)
  -- originally, we had (q : ℕ)
  -- rewrite this part: use the lemma above 
  have h : ∃(c : ℤ), (x₁ : ℂ) = (x₂ : ℂ) + c * (q : ℤ)
  { simp only [Int.cast_ofNat]
    have exist_const := Iff.mp Int.modEq_iff_add_fac h_congr
    cases' exist_const with t ht
    use (-t)
    norm_cast
    simp only [neg_mul]
    apply eq_sub_of_add_eq
    rw [mul_comm]
    symm
    exact ht  }
  cases' h with c hc
  rw [hc]
  rw [Int.cast_ofNat]
  rw [mul_div_assoc]
  rw [add_div]
  rw [mul_div_assoc]
  have complex_ne_q : (q : ℂ) ≠ 0 := by exact Iff.mpr Nat.cast_ne_zero (NeZero.ne q)
  rw [div_self complex_ne_q]
  rw [mul_one]
  rw [mul_add]
  rw [Complex.exp_add]
  rw [mul_comm (2 * Real.pi * Complex.I) (c : ℂ)]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  ring

-- need to change it I think
lemma complex_pow (n : ℕ) {a : ℂ} {b : ℂ} (h : a = b) : a^n = b^n := by
  exact congrFun (congrArg HPow.hPow h) n

-- need to decide how to capitalize it
-- need to show that `χ' (χ) (z)` is equal to a root of unity
/- I don't think I need this anymore 
theorem MulChar_additive_eq_exp (p : ℕ) (hp : Prime p) (α : ℕ) (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    ∃(b : ℕ), b < p ^ α ∧ χ' (χ) (z) = eZMod (p^α : ℕ) (b*z) := by
  have : NeZero (p^α) := ⟨pow_ne_zero α <| Prime.ne_zero hp⟩
  rw [← MulChar_additive_pow_val]
  have newExpression : ∃(ζ : ℂˣ), (ζ : ℂˣ) = (χ' (χ) (1) : ℂ)
  { have H := MulChar_one_Unit χ
    rw [IsUnit] at H
    exact H }
  have primepow_pos : ∃(q : ℕ+), q = p^α
  { apply CanLift.prf (p^α)
    exact Fin.size_positive' }
  cases' newExpression with ζ hζ
  cases' primepow_pos with q hq
  -- why do both ζ and q : ?m.1264417
  have ofunity : ζ ∈ rootsOfUnity q ℂ ↔ ((ζ : ℂˣ) : ℂ) ^ ((q : ℕ+) : ℕ) = 1 := by
    simp only [mem_rootsOfUnity']
    -- simp [Units.ext_iff] -- fixed after the bug in power notation in mathlib was found
  have root : ζ ∈ rootsOfUnity q ℂ
  { rw [ofunity, hζ, hq, MulChar_additive_pow, ZMod.nat_cast_self, mul_one]
    exact MulChar_zero χ  }
  rw [Complex.mem_rootsOfUnity, hq, hζ] at root
  have pow (n : ℕ) {a : ℂ} {b : ℂ} : a = b → a^n = b^n
  { intro h
    norm_cast
    exact congrFun (congrArg HPow.hPow h) n }
  cases' root with b hb
  have hb_pow := pow (z.val) (hb.right)
  norm_cast at hb_pow
  rw [← Complex.exp_nat_mul] at hb_pow

  simp only [eZMod]
  use b
  apply And.intro
  exact hb.left
  have congr_val : ((b : ZMod (p^α : ℕ)) * z).val ≡ (b : ZMod (p^α)).val * z.val [ZMOD (p^α)]
  { rw [ZMod.val_mul (↑b) z]
    exact Int.mod_modEq ((b : ZMod (p^α)).val * ZMod.val z) (p ^ α) }

  have new_NeZero : p^α ≠ 0 := by exact NeZero.ne (p^α)
  have val_b : (b : ZMod (p^α)).val ≡ b [ZMOD (p^α)]
  { simp only [Nat.cast_pow, ZMod.nat_cast_val]
    norm_cast
    rw [← ZMod.int_cast_eq_int_cast_iff]
    simp  }
  rw [cexp_congr_eq (p^α : ℕ) (((b : ZMod (p^α : ℕ)) * z).val) ((b : ZMod (p^α)).val * z.val)]
  · have congr_b : (b : ZMod (p^α)).val * z.val ≡ b * z.val [ZMOD (p^α)] := by gcongr
    -- simp at congr_b ⊢
    rw [cexp_congr_eq (p^α : ℕ) ((b : ZMod (p^α)).val * z.val) (b * z.val)]
    · push_cast at hb_pow ⊢
      norm_cast
      symm at hb_pow
      rw [hb_pow]
      push_cast
      ring
    · exact congr_b
    · exact new_NeZero
  · exact congr_val
  · exact new_NeZero
  done
  -/

  /- change the name later 
  I don't think I need the previous version of the lemma
  -/

  -- (hp : Prime p)
/- main theorem in this file 
-/
theorem MulChar_additive_eq_exp_for_all :
    ∃(b : ℕ), b < p ^ α ∧ ∀(z : ZMod (p ^ α)), χ' χ z = eZMod (p ^ α) (b * z) := by
  -- have : NeZero (p^α) := ⟨pow_ne_zero α <| Prime.ne_zero hp⟩
  have newExpression : ∃(ζ : ℂˣ), (ζ : ℂˣ) = (χ' χ 1 : ℂ)
  { have := MulChar_one_Unit χ
    rw [IsUnit] at this
    exact this }
  have primepow_pos : ∃(q : ℕ+), q = p ^ α
  { apply CanLift.prf (p ^ α)
    exact Fin.size_positive' }
  cases' newExpression with ζ hζ
  cases' primepow_pos with q hq
  -- why do both ζ and q : ?m.1264417
  /-
  have ofunity : ζ ∈ rootsOfUnity q ℂ ↔ ((ζ : ℂˣ) : ℂ) ^ ((q : ℕ+) : ℕ) = 1 := by
    simp only [mem_rootsOfUnity'] -/ 
    -- simp [Units.ext_iff] -- fixed after the bug in power notation in mathlib was found
  have root : ζ ∈ rootsOfUnity q ℂ
  { rw [mem_rootsOfUnity', hζ, hq, MulChar_additive_pow, ZMod.nat_cast_self, mul_one]
    exact MulChar_zero χ  }
  rw [Complex.mem_rootsOfUnity, hq, hζ] at root
  cases' root with b hb
  use b
  apply And.intro hb.left
  intro z
  rw [← MulChar_additive_pow_val]
  have hb_pow := complex_pow z.val hb.right
  norm_cast at hb_pow
  rw [← Complex.exp_nat_mul] at hb_pow
  unfold eZMod
  -- have new_NeZero : p ^ α ≠ 0 := by exact NeZero.ne (p ^ α)
  /-
  have val_b : (b : ZMod (p ^ α)).val ≡ b [ZMOD (p ^ α)]
  { simp only [Nat.cast_pow, ZMod.nat_cast_val]
    norm_cast
    rw [← ZMod.int_cast_eq_int_cast_iff]
    simp  }
  -/ 
  rw [cexp_congr_eq (p ^ α : ℕ) (((b : ZMod (p^α : ℕ)) * z).val) ((b : ZMod (p^α)).val * z.val)]
  · have congr_b : (b : ZMod (p^α)).val * z.val ≡ b * z.val [ZMOD (p^α)]
    { gcongr
      simp only [Nat.cast_pow, ZMod.nat_cast_val]
      norm_cast
      rw [← ZMod.int_cast_eq_int_cast_iff]
      simp  }
    -- simp at congr_b ⊢
    rw [cexp_congr_eq (p^α : ℕ) ((b : ZMod (p^α)).val * z.val) (b * z.val) congr_b]
    push_cast at hb_pow ⊢
    norm_cast
    symm at hb_pow
    rw [hb_pow]
    push_cast
    ring
  · rw [ZMod.val_mul (↑b) z]
    exact Int.mod_modEq ((b : ZMod (p^α)).val * ZMod.val z) (p ^ α)
  done

/- # Questions to Kevin
1. How to make 
2. I loathe how I wrote down theorem `MulChar_one_rootOfUnity`. Is there a way to make it better?
3. 


-/

/- # Note to myself
1. need to learn how to capitalize the names of the theorems
2. I abuse have tactic too much especially since I don't know how to use fancy tactics

-/