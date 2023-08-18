import Mathlib

-- tried out `x ; ℝ` to see whether it'll work out. But it seems lemmas won't work out well

#check RatFunc

-- wrote Kloosterman stuff

-- inductive
-- valuation ring
-- mathlib4/mathlib/numbertheory/lucasprimality.lean
open Complex

noncomputable section

def eZMod (q : ℕ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x / q)

variable (q : ℕ) (x : ℝ)

lemma eZMod_def : eZMod q x = Complex.exp (2 * Real.pi * Complex.I * x / q) := rfl

example (a : ℤ) : a / 0 = 0 := by exact Int.ediv_zero a

-- needs Kevin's approval
lemma eZMod_add (x y : ZMod q) (zero_ne_hq : q ≠ 0) : eZMod q (x + y) = eZMod q x * eZMod q y := by
  simp only [eZMod_def]
  rw [← Complex.exp_add]
  rw [exp_eq_exp_iff_exists_int]
  -- needs Kevin's approval from this point
  have czero_ne_hq : (q : ℂ) ≠ 0 := by exact Iff.mpr Nat.cast_ne_zero zero_ne_hq
  -- have cancel_q : (q : ℂ) * (q⁻¹ : ℂ) = 1
  -- rwa [Complex.mul_inv_cancel]
  -- (remainder of x + y mod q) * 1/q
  -- use ((x + y).val* 1/q - x.val* 1/q - y.val* 1/q) 
  use ((x + y).val - x.val - y.val)* 1/q
  field_simp
  -- norm_cast isn't the one
  simp only [Int.cast_id]
  
  -- rw [Complex.of_real_sub]

  /- my plan A
  simp [Complex.ofReal_div]
  simp [← Complex.ofReal_neg] -- for int
  simp [Complex.ofReal_add]

  simp [← Complex.ofReal_neg]

  Then let q in the denominator and the one multiplied on the right cancel out each other
  After the above steps, I think it will be easy to prove unless coercion makes problems

  plan B
  coercion from int to reals. Then try to use plan A.

  plan C
  No idea. help

  Problem: we can use the above theorems for real variables
  but `↑(ZMod.val (x + y)` `↑(ZMod.val x)` `↑(ZMod.val y)` are coerced to be an integer. 
  So cannot apply the above theorems. 

  Question: Is there similar theorems targeted for integer variables? 
  If not, 
  -/
  sorry


  /- various attempts
  simp [Complex.ofReal_div]
  simp_rw [← Complex.ofReal_neg]
  
  
  rw [← Int.ofNat_add_out]


  -- rw [Num.add_of_nat]



  rw [Real.has_int_cast]
  rw [← Complex.ofReal_neg]


  rw [← Complex.ofReal_add]

  -- complex.ofReal_add

  -- complex.of_real_div
  rw [← Complex.ofReal_div]

  
  




  rw [mul_assoc (2 * ↑Real.pi * I) ↑q]



  
  simp [Complex.ofReal_int_cast]
  rw [Nat.cast_add] 
  -- norm_num




  rw [← mul_left_inj' czero_ne_hq]
  field_simp

  --rw [mul_comm (2 * ↑Real.pi * I) (↑q)]



  rw [mul_comm]
  rw [mul_comm (2 * ↑Real.pi * I) ↑(ZMod.val x)]

  
  
  
  rw [mul_assoc]
  -/
  
  

  /-
  norm_num
  -- have ne_pi : (2 * Real.pi * I : ℂ) ≠ 0
  -- simp [Real.pi_pos.ne.symm, I_ne_zero]
  have czero_ne_hq : (q : ℂ) ≠ 0 := by exact Iff.mpr Nat.cast_ne_zero zero_ne_hq
  have cancel_q : (q : ℂ) * (q⁻¹ : ℂ) = 1
  rwa [Complex.mul_inv_cancel]
  rw [← mul_left_inj' czero_ne_hq]
  field_simp
  rw [← mul_add]
  norm_cast
  have H : ZMod.val (x + y) = ZMod.val x + ZMod.val y 
  haveI := NeZero.mk zero_ne_hq
  rw [ZMod.val_add]
  -- easier way?
  -- rw [Nat.mod_eq_iff_lt]
  have hxy_le_q : x + y < q
  simp_rw [Ordinal.mod_eq_of_lt]

  sorry
  -/

  -- symm
  -- rw [← mul_add (2 * Real.pi * I : ℂ) ]


    /- first attempt
  simp only [eZMod_def]
  rw [← Complex.exp_add]
  rw [exp_eq_exp_iff_exists_int]
  use (x.val + y.val) / q
  rcases eq_or_ne q 0 with (rfl | hq)
  { simp only [CharP.cast_eq_zero]
    -- simp times out!!
    simp only [div_zero]
    simp only [Int.ediv_zero]
    ring }
  { have ne_pi : (2 * Real.pi * I : ℂ) ≠ 0
    simp [Real.pi_pos.ne.symm, I_ne_zero]
    sorry }
    -/

    /- second attempt
  simp only [eZMod_def]
  rw [← Complex.exp_add]
  rw [exp_eq_exp_iff_exists_int]
  -- needs Kevin's approval from this point
  use 0
  norm_num
  -- have ne_pi : (2 * Real.pi * I : ℂ) ≠ 0
  -- simp [Real.pi_pos.ne.symm, I_ne_zero]
  have czero_ne_hq : (q : ℂ) ≠ 0 := by exact Iff.mpr Nat.cast_ne_zero zero_ne_hq
  have cancel_q : (q : ℂ) * (q⁻¹ : ℂ) = 1
  rwa [Complex.mul_inv_cancel]
  rw [← mul_left_inj' czero_ne_hq]
  field_simp
  rw [← mul_add]
  norm_cast
  have H : ZMod.val (x + y) = ZMod.val x + ZMod.val y 
  haveI := NeZero.mk zero_ne_hq
  rw [ZMod.val_add]
  -- easier way?
  -- rw [Nat.mod_eq_iff_lt]
  -- the goal is false since (ZMod.val x + ZMod.val y) can be larger than q
  have hxy_le_q : x + y < q
  simp_rw [Ordinal.mod_eq_of_lt]
    


  -- Ordinal.mod_eq_of_lt is the one!!!!
  
  -- simp [ZMod.nat_cast_mod]


  -- simp [ZMod.nat_cast_toNat]
  
  
  -- ZMod.val_add
  -- apply_fun ZMod.val at *
  
  
  -- dec_trivial
  -- rw [← ZMod.cast_eq_val]
    
    -/

  /- third attempt
  simp only [eZMod_def]
  rw [← Complex.exp_add]
  rw [exp_eq_exp_iff_exists_int]
  -- needs Kevin's approval from this point
  have czero_ne_hq : (q : ℂ) ≠ 0 := by exact Iff.mpr Nat.cast_ne_zero zero_ne_hq
  -- have cancel_q : (q : ℂ) * (q⁻¹ : ℂ) = 1
  -- rwa [Complex.mul_inv_cancel]
  -- (remainder of x + y mod q) * 1/q
  use ((x.val + y.val) % q) * 1/q
  rw [← mul_left_inj' czero_ne_hq]
  -/

  /- fourth attempt
  simp only [eZMod_def]
  rw [← Complex.exp_add]
  rw [exp_eq_exp_iff_exists_int]
  -- needs Kevin's approval from this point
  have czero_ne_hq : (q : ℂ) ≠ 0 := by exact Iff.mpr Nat.cast_ne_zero zero_ne_hq
  -- have cancel_q : (q : ℂ) * (q⁻¹ : ℂ) = 1
  -- rwa [Complex.mul_inv_cancel]
  -- (remainder of x + y mod q) * 1/q
  use (x + y : ZMod q) * 1/q
  norm_num
  -- rw [← mul_left_inj' czero_ne_hq]
  field_simp
  
  --rw [mul_comm (2 * ↑Real.pi * I) (↑q)]



  rw [mul_comm]
  rw [mul_comm (2 * ↑Real.pi * I) ↑(ZMod.val x)]
  
  -/
/-good examples to look at 

lemma zmod_pow_val_nat {m : ℕ} (n e : ℕ)
: ((↑n : ZMod m) ^ e) = (n ^ e : ZMod m) := by
  by_cases h : m = 0
  · simp
  · haveI := NeZero.mk h
    apply ZMod.val_injective
    simp

 lemma zmod_pow_val_nat' {m : ℕ} (n e : ℕ) : ZMod.val ((↑n : ZMod m) ^ e) = ZMod.val (n ^ e : ZMod m) := by
  induction' e with e ih
  · rw [pow_zero, pow_zero]
    rw [Nat.cast_one]
  · rw [pow_succ, pow_succ]
    rw [ZMod.val_mul]
    rw [ih]
    rw [ZMod.val_nat_cast]
    rw [ZMod.val_nat_cast]
    rw [ZMod.val_nat_cast]
    rw [←Nat.mul_mod]   



lemma zmod_val_pow_nat' {m : ℕ} (n e : ℕ)
: ZMod.val ((b : ZMod m) ^ e) = b ^ e % m := by
  rw [zmod_pow_val_nat]
  exact ZMod.val_nat_cast _

-/

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

section elementary
-- depends only on the residue class of a and b modulo m
lemma lemma1_1 (a : ℤ) (b : ℤ) (q : ℕ) : kloostermanSum a b q = kloostermanSum (a + q) (b + q) q := by
  simp only [kloostermanSum]
  apply congr_arg
  apply funext
  intro x
  simp

-- as x goes through the complete residue system mod p^α, x⁻¹ goes through the complete residue system mod p^α 
-- lemma lemma_2_1 (α : ℕ) (p : ℕ) [Fact p.Prime] : Set (ZMod (p^α : ℕ))ˣ = {x⁻¹ | x ∈ (ZMod (p^α : ℕ)ˣ)} := by

lemma lemma1_2 (a₁ : ℤ) (b₁ : ℤ) (a₂ : ℤ) (b₂ : ℤ) (q : ℕ) (ha₁a₂ : a₁ ≡ a₂ [ZMOD q]) (hb₁b₂ : b₁ ≡ b₂ [ZMOD q]) : kloostermanSum a₁ b₁ q = kloostermanSum a₂ b₂ q := by
  simp only [kloostermanSum]
  apply congr_arg
  apply funext
  intro x
  rw [← ZMod.int_cast_eq_int_cast_iff] at ha₁a₂ hb₁b₂
  rw [ha₁a₂, hb₁b₂]

  -- ← ZMod.int_cast_eq_int_cast_iff 

lemma lemma2 (a : ℤ) (b : ℤ) (q : ℕ) : kloostermanSum a b q = kloostermanSum b a q := by
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

lemma lemma3_1 (a : ℤ) (b : ℤ) (q : ℕ) (gcd_aq : a.Coprime q) : kloostermanSum a b q = kloostermanSum 1 (a*b) q  := by
  simp only [kloostermanSum]
  simp
  -- sends x to (a⁻¹*x⁻¹) in the sum
  -- let a_inv := (ZMod q)ˣ : a⁻¹ 
  apply Finset.sum_bij (fun i _ ↦ i⁻¹)
  sorry

  -- a.Coprime q


 -- K(ac, b; m) = K(a, bc; m) if gcd(c, m) = 1
lemma lemma3_2 (a : ℤ) (b : ℤ) (q : ℕ) (gcd_cq : c.gcd q = 1) : kloostermanSum (a*c) b q = kloostermanSum a (b*c) q  := by
  simp only [kloostermanSum]
  simp
  -- sends x to (c⁻¹*x⁻¹) in the sum
  sorry


  #exit
-- Kloosterman sum is multiplicative
theorem theorem1 (a : ℤ) (b : ℤ) (q : ℕ) (b₁ : ℤ) (b₂ : ℤ) (q₁ : ℕ) (q₂ : ℕ) (hb : b = b₁*q₂^2 + b₂*q₁^2) (hq : q = q₁ * q₂) (gcd_q : q₁.gcd q₂ = 1): kloostermanSum a b m = (kloostermanSum a b m₁) * (kloostermanSum a b m₂) := by 
  
  
  sorry

end elementary

-- proper Iwaniec and Kowalski proof starts from here
lemma lemma_4 