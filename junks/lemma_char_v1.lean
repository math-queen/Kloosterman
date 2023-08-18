import Mathlib
-- import def2_v2_kloosterman

#check RatFunc
-- import Desktop.UCL.mary_lister.kloosterman.def2_v2_kloosterman.lean

-- wrote Kloosterman stuff

-- inductive
-- valuation ring
-- mathlib4/mathlib/numbertheory/lucasprimality.lean

open Complex

-- need to build up the definition
/- 
So I think that this condition about f0 and f1 and f0(x) being coprime to q boils down to the following. 
You have a rational function f : RatFunc \Q and the condition you want is that firstly f.denom x isn't zero 
and secondly that the rational number f(x) is "coprime to q" in the sense that the denominator is coprime to q

Then you can "reduce f(x) mod q" by inverting the denominator mod q and multiplying by the numerator
-/

-- (haq : ((a : ZMod q).val).gcd q = 1)

noncomputable section

def eZMod (q : ℕ) (x : ZMod q) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x.val / q)

variable {p : ℕ} {α : ℕ} (z : ZMod (p^(2*α) : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) (ζ : ℂˣ)
-- (q : ℕ) (x : ZMod q) (y : ℤ) (z : ZMod q)

-- Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean
-- Mathlib/NumberTheory/LegendreSymbol/MulCharacter.lean

def χ' : ZMod (p^(2*α) : ℕ) → ℂ :=
  fun z => χ (1 + z*(p^α : ZMod (p^(2*α) : ℕ))) 

-- the character χ' is well-defined
theorem well_defined : χ' (χ) (z) = χ (1 + z*(p^α : ZMod (p^(2*α) : ℕ))) := rfl

-- Clearly χ(1+z*p^α) is an additive character to modulus p^α
lemma MulChar_additive (p : ℕ) (α : ℕ) (z₁ z₂ : ZMod (p^(2*α) : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    χ' (χ) (z₁) * χ' (χ) (z₂) = χ' (χ) (z₁ + z₂) := by
  simp [well_defined]
  rw [← map_mul]
  refine FunLike.congr_arg χ ?h₂
  ring
  norm_cast
  have hpα : p^(α * 2) = p^(2 * α) := by ring
  rw [hpα]
  rw [ZMod.nat_cast_self]
  ring
  
/- Previous version
lemma MulChar_additive' (p : ℕ) (α : ℕ) (z₁ z₂ : ZMod (p^(2*α) : ℕ))(χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    χ (1 + z₁*(p^α : ZMod (p^(2*α) : ℕ))) * χ (1 + z₂*(p^α : ZMod (p^(2*α) : ℕ))) = χ (1 + (z₁ + z₂)*(p^α : ZMod (p^(2*α) : ℕ))) := by
  rw [← map_mul]
  refine FunLike.congr_arg χ ?h₂
  ring
  norm_cast
  have hpα : (p^α)^2 = p^(2 * α) := by ring
  rw [hpα]
  rw [ZMod.nat_cast_self]
  ring
-/


-- erase this lemma later
lemma MulChar_zmod (p : ℕ) (α : ℕ) (z₁ : ZMod (p^(2*α) : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    χ (z₁ + (p^(2*α) : ℕ)) = χ (z₁) := by
  refine FunLike.congr_arg χ ?h₂
  rw [ZMod.nat_cast_self]
  exact add_zero z₁




-- look for the proof that 

-- primitive root
-- AddChar.zmodChar
-- Mathlib/RingTheory/RootsOfUnity/Complex.lean
-- Mathlib/RingTheory/RootsOfUnity/Basic.lean
-- which mentions something about the `exp (2 * pi * I / n)` is a primitive `n`-th root of unity
-- `theorem isPrimitiveRoot_iff` from Mathlib/RingTheory/RootsOfUnity/Complex.lean

-- prove χ' is zmodChar

-- set_option maxHeartBeats 1800000 in -- would like to avoid if possible

/- 
theorem is_primitive_root.iff_def

theorem is_primitive_root.mk_of_lt 

theorem is_primitive_root.iff

-/
lemma MulChar_additive_eq_exp' 
    -- AddChar.zmodChar (p) (hξ) := by
  sorry


/- previous version
lemma pastVersion_MulChar_additive_eq_exp (p : ℕ) (α : ℕ) (ζ : ℂˣ) (hζ : ζ^(p^α : ℕ) = 1) : 
    χ' (χ) (z) = AddChar.zmodChar (p^α : ℕ+) (hζ) := by
  sorry
-/

theorem MulChar_zero : χ' (χ) (0) = 1 := by
  rw [well_defined]
  ring
  exact MulChar.map_one χ

-- 

-- need to decide how to capitalize it
-- need to show that `χ' (χ) (z)` is equal to primitive root
lemma MulChar_additive_eq_PrimitiveRoot (p : ℕ) (hp : Prime p) (α : ℕ) (z : ZMod (p^(2*α) : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    ∃(b : ZMod (p^(2*α) : ℕ)), χ' (χ) (z) = eZMod (p^(2*α) : ℕ) (b*z) := by
  sorry

-- feels like there's something in the mathlib for this
theorem MulChar_additive_pow (n : ℕ) (α : ℕ) (z : ZMod (p^(2*α) : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    (χ' (χ) (z))^(n : ℕ) = (χ' (χ) (n*z)) := by
  induction' n with n ihn
  · norm_num
    exact Eq.symm (MulChar_zero χ)
  · norm_num
    norm_cast at *
    rw [pow_add (χ' (χ) (z)) (n) 1]
    rw [ihn]
    ring
    rw [MulChar_additive]
    push_cast
    ring


lemma ofOrderMulChar : orderOf (χ' (χ) (z)) = p^α := by
  have H : (χ' (χ) (z))^(p^(2*α) : ℕ) = 1 ∧ ∀ (m : ℕ), m < p^(2*α) → 0 < m → (χ' (χ) (z))^m ≠ 1
  apply And.intro
  · rw [MulChar_additive_pow]
    rw [ZMod.nat_cast_self]
    ring
    exact MulChar_zero χ
  · intro m hmp hm
    norm_cast 
    rw [MulChar_additive_pow]
    
    
    
    /- 
    induction' m with m ihm
    · norm_num at *
    · norm_num
    -/
  · sorry

  -- rw [orderOf_eq_iff]


-- theorem Complex.mem_rootsOfUnity
-- theorem Complex.mem_rootsOfUnity_iff_mem_nthRoots
theorem MulChar_additive_rootsOfUnity (p : ℕ) (hp : Prime p) (α : ℕ) (z : ZMod (p^(2*α) : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    IsPrimitiveRoot (χ' (χ) (z)) (p^(2*α) : ℕ) := by
  -- to use the theorem IsPrimitiveRoot.iff_def
  
  
  






/- # Questions to Kevin
1. How to make 




-/


/- # Note to myself
1. need to learn how to capitalize the names of the theorems


-/