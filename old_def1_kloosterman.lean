import Mathlib

#check RatFunc

-- wrote Kloosterman stuff

-- inductive
-- valuation ring
-- mathlib4/mathlib/numbertheory/lucasprimality.lean
open Complex

noncomputable section

def kloostermanSum (a : ℤ) (b : ℤ) (q : ℕ) : ℂ := 
  ∑' x : (ZMod q)ˣ, Complex.exp (2 * Real.pi * Complex.I * (a*x + b*x⁻¹)/q)

section elementary
-- depends only on the residue class of a and b modulo m

@[simp] lemma GaussianInt.toComplex_eq_cast (a : ZMod q) : 
    GaussianInt.toComplex (a : GaussianInt) = ZMod.cast a := by sorry

lemma lemma_1 (a : ℤ) (b : ℤ) (q : ℕ) (zero_ne_hq : (q : ℂ) ≠ 0) : kloostermanSum a b q = kloostermanSum (a + q) (b + q) q := by
  simp only [kloostermanSum]
  apply congr_arg
  apply funext
  intro x
  
  rw [exp_eq_exp_iff_exists_int]
  use (- x - x⁻¹)
  push_cast
  -- norm_cast
  have ne_pi : (2 * Real.pi * I : ℂ) ≠ 0
  simp [Real.pi_pos.ne.symm, I_ne_zero]
  -- rw [mul_comm (2 * (Real.pi : ℂ) * I), ((a : ℂ) * (x : ℂ) + (b : ℂ) * (x⁻¹ : ℂ))]
  have cancel_q : (q : ℂ) * (q⁻¹ : ℂ) = 1
  rwa [Complex.mul_inv_cancel]
  have cancel_q' : ∀ z : ℂ, z * (q : ℂ) * (q⁻¹ : ℂ) = z := by
    intro z
    rw [mul_assoc, cancel_q, mul_one]
  
  simp [GaussianInt.toComplex_eq_cast]
  
  rw [← mul_add]
  rw [mul_comm (-↑↑x - ↑↑x⁻¹) (2 * ↑Real.pi * I)]


  ring
  rw [cancel_q']


  




  




  ring
  rw [cancel_q', cancel_q']
  ring
  field_simp
  ring
  -- does ring tactic consider the conditions zero_ne_hq and ne_pi when applied?
  -- if not, WHY?



 /- previous attempt
  rw [zero_ne_hq]
  push_cast
  ring
  norm_cast
  have hq : (q : ℂ) * (q - 1) = 1
  rw [hq]
  ring
-/
  

  
  -- lemma


  -- apply congr_fun
  -- norm_num
  -- norm_cast
  -- ring_nf
  
  #exit
  
-- K(a, b; m) = K(b, a; m)
lemma lemma_2 (a : ℤ) (b : ℤ) (p : ℕ) [Fact p.Prime] (α : ℕ) : kloostermanSum a b (p^α) = kloostermanSum b a (p^α) := by
  simp only [kloostermanSum]
  by_cases ha : a = 0
  rw [ha]
  { by_cases hb : b = 0
    rw [hb]
    
    let φ : 


  }
  
  
  norm_num
  

  
  
-- K(ac, b; m) = K(a, bc; m) if gcd(c, m) = 1
lemma lemma_3 (a : ℤ) (b : ℤ) (q : ℕ) (gcd_cq : c.gcd q = 1) : kloostermanSum (a*c) b q = kloostermanSum a (b*c) q  := by
  sorry

-- Kloosterman sum is multiplicative
theorem theorem_1 (a : ℤ) (b : ℤ) (q : ℕ) (b₁ : ℤ) (b₂ : ℤ) (q₁ : ℕ) (q₂ : ℕ) (hb : b = b₁*q₂^2 + b₂*q₁^2) (hq : q = q₁ * q₂) (gcd_q : q₁.gcd q₂ = 1): kloostermanSum a b m = (kloostermanSum a b m₁) * (kloostermanSum a b m₂) := by 
  sorry

end elementary

-- proper Iwaniec and Kowalski proof starts from here
lemma lemma_4 