import Mathlib
-- import def2_v2_kloosterman

#check RatFunc
-- import Desktop.UCL.mary_lister.kloosterman.def2_v2_kloosterman.lean

-- wrote Kloosterman stuff

-- inductive
-- valuation ring
-- mathlib4/mathlib/numbertheory/lucasprimality.lean

open Complex

-- (haq : ((a : ZMod q).val).gcd q = 1)

noncomputable section

def eZMod (q : ℕ) (x : ZMod q) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x.val / q)

variable {p : ℕ} {α : ℕ} (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ)
-- (q : ℕ) (x : ZMod q) (y : ℤ) (z : ZMod q)

-- Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean
-- Mathlib/NumberTheory/LegendreSymbol/MulCharacter.lean

def χ' : ZMod (p^α : ℕ) → ℂ :=
  fun z => χ (1 + z*(p^α : ZMod (p^(2*α) : ℕ))) 

-- the character χ' is well-defined
-- tried out `z.val`
theorem well_defined : χ' (χ) (z) = χ (1 + z*(p^α : ZMod (p^(2*α) : ℕ))) := rfl

example (n m : ℕ) (x : ZMod n) : (x : ZMod m) = (x : ℤ) := by simp only [ZMod.int_cast_cast]

lemma foo (p : ℕ) (α : ℕ) (z₁ z₂ : ZMod (p^α : ℕ)) :
    (p : ZMod (p^(2*α)))^α * (z₁ : ZMod (p^(2*α))) + (p : ZMod (p^(2*α)))^α * (z₂ : ZMod (p^(2*α) : ℕ)) =
    (p: ZMod (p^(2*α)))^α * ((z₁ + z₂ : ZMod (p^α)) : ZMod (p^(2*α))) := by
  rw [← ZMod.int_cast_cast (z₁ + z₂)]
  rw [ZMod.coe_add_eq_ite]
  split
  · simp [mul_sub, mul_add]
    rw [← pow_add, ← two_mul]
    norm_cast
    rw [ZMod.nat_cast_self]
    simp
  · push_cast
    simp only [ZMod.int_cast_cast]
    ring

-- Clearly χ(1+z*p^α) is an additive character to modulus p^α
lemma MulChar_additive (p : ℕ) (α : ℕ) (z₁ z₂ : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    χ' (χ) (z₁) * χ' (χ) (z₂) = χ' (χ) (z₁ + z₂) := by
  simp only [well_defined, Nat.cast_pow]
  rw [← map_mul]
  apply congr_arg
  ring_nf -- still kind of evil
  norm_cast
  rw [mul_comm α 2, ZMod.nat_cast_self]
  simp only [Nat.cast_pow, mul_zero, zero_mul, add_zero]
  rw [← foo]
  ring
  done

-- Clearly χ(1+z*p^α) is an additive character to modulus p^α
lemma MulChar_additive' (p : ℕ) (α : ℕ) (z₁ z₂ : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    χ' (χ) (z₁) * χ' (χ) (z₂) = χ' (χ) (z₁ + z₂) := by
  simp [well_defined]
  rw [← map_mul]
  apply congr_arg
  ring
  norm_cast
  have hpα : p^(α * 2) = p^(2 * α) := by ring
  rw [hpα]
  rw [ZMod.nat_cast_self]
  ring
  have H : (z₁ : ZMod (p^(2*α) : ℕ)) + (z₂ : ZMod (p^(2*α) : ℕ)) = ((z₁ + z₂ : ZMod (p^α : ℕ)) : ZMod (p^(2*α) : ℕ)) ∨ 
  sorry 
  sorry
  sorry
  done
  /- 
  have coe_add_z₁z₂ : ((z₁ + z₂) : ZMod (p^(2*α) : ℕ)) ≡ (z₁: ZMod (p^(2*α) : ℕ)) + (z₂: ZMod (p^(2*α) : ℕ)) [ZMOD (p^(2*α) : ℕ)]
  -/
  
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
  -- refine FunLike.congr_arg χ ?h₂
  rw [ZMod.nat_cast_self]
  ring

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


/- previous version
lemma pastVersion_MulChar_additive_eq_exp (p : ℕ) (α : ℕ) (ζ : ℂˣ) (hζ : ζ^(p^α : ℕ) = 1) : 
    χ' (χ) (z) = AddChar.zmodChar (p^α : ℕ+) (hζ) := by
  sorry
-/

theorem MulChar_zero : χ' (χ) (0) = 1 := by
  rw [well_defined]
  norm_num
-- 

-- feels like there's something in the mathlib for this
theorem MulChar_additive_pow (n : ℕ) (α : ℕ) (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
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

theorem MulChar_equal_one : (χ' (χ) (z))^(p^α : ℕ) = 1 := by
  rw [MulChar_additive_pow]
  rw [well_defined]
  norm_num

-- need `[NeZero (p^α : ℕ)]`
theorem MulChar_additive_pow_val (α : ℕ) [NeZero (p^α : ℕ)] (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    (χ' (χ) 1)^z.val = (χ' (χ) (z)) := by
  rw [MulChar_additive_pow]
  apply congr_arg
  norm_num
  
-- I don't like how I have written down the proof
-- can I change it? 

-- theorem mem_roots_of_unity
-- theorem Complex.mem_rootsOfUnity
-- has the exponential form 

-- every non-zero element of ℂ is unit

-- instance (ℂ \ {0}) == ℂˣ := rfl 

/- overall proof
need to prove `χ' (χ) (1) ≠ 0 `
then change ℂ to ℂˣ
then we can have χ' (χ) (1) to be an unit i.e., ℂˣ

figure out to make p^α ℕ+ -- problematic part
then we can use the theorems mem_roots_of_unity and Complex.mem_rootsOfUnity

-/

/- 
lemma MulChar_nonZero (n : ZMod (p^α : ℕ)) (n.gcd (p^α) = 1) : χ' (χ) (n) ≠ 0 
  sorry
-/

lemma MulChar_nonZero {a : ZMod (p^(2*α) : ℕ)} (h : IsUnit a) : χ a ≠ 0 := by
  apply Iff.mp isUnit_iff_ne_zero
  exact IsUnit.map χ h

/-
lemma MulChar_nonIsUnit (a : ZMod (p^(2*α) : ℕ)) (h : χ a = 0) : ¬IsUnit a := by
  sorry
-/

-- theorem mul_char.map_nonunit
lemma MulChar_one_nonZero : χ' (χ) (1) ≠ 0 := by
  rw [well_defined]
  have h : IsUnit ((1 + (1 : ZMod (p^α : ℕ))  * ↑(p ^ α)) : ZMod (p^(2*α) : ℕ))
  { apply Iff.mpr isUnit_iff_exists_inv
    use (1 - (1 : ZMod (p^α : ℕ))*(p^α : ℕ))
    ring
    norm_cast
    have hpαPow : (p^α)^ 2 = p^(2 * α) := by ring
    rw [hpαPow]
    rw [ZMod.nat_cast_self]
    ring
    /- fake statement
    have Nat_coe_ZMod : ((1 : ZMod (p^α : ℕ)) : ZMod (p^(2*α) : ℕ)) = (((1 : ℕ) : ZMod (p^α : ℕ)) : ZMod (p^(2*α) : ℕ)) := by ring
    -- have Nat_coe_ZModPowOne : ((1 : ℕ) : ZMod (p^α : ℕ)) = (1 : ZMod (p^α : ℕ)) := by ring
    have hpDiv : p^α ∣ p^(2*α) := by
      simp [dvd_iff_exists_eq_mul_left]
      use p^α
      ring
    have Ring_ZMod : Ring (ZMod (p^(2*α) : ℕ)) := by exact CommRing.toRingCommRing.toRing
    have Char_ZMod : CharP (ZMod (p^(2*α) : ℕ)) (p^(2*α)) := by exact ZMod.charP (p ^ (2 * α))
    have Nat_coe_ZModPow : ((1 : ZMod (p^α : ℕ)) : ZMod (p^(2*α) : ℕ)) = ((1 : ℕ) : ZMod (p^(2*α) : ℕ)) := by
      simp
      rw [ZMod.cast_one hpDiv]
     -/

      -- zmod.cast_one
      -- need to make coercion 
      
      
      
      -- simp [← ZMod.cast_id]
      -- refine (?_ (id (Eq.symm hpαPow))).out
    

    /-
    have hpα : ((1 : ZMod (p^α : ℕ))  * ↑(p ^ α) : ZMod (p^(2*α) : ℕ)) = (↑(p ^ α) : ZMod (p^(2*α) : ℕ))
    apply?

    norm_num
    ring
    
    norm_num
    push_cast
    norm_num
    ring
    have hpα : (p^α)^ 2 = p^(2 * α) := by ring
    sorry
    -- rw [hpα]
    -- rw [ZMod.nat_cast_self]
    -/
  } 
  exact MulChar_nonZero χ h



  /- first attempt 
  rw [well_defined]
  have h : IsUnit ((1 + ↑1 * ↑(p ^ α)) : ZMod (p^(2*α) : ℕ))
  { refine Iff.mpr isUnit_iff_exists_inv ?h.a
    use (1 - (p^α : ℕ))
    ring
    have hp : ((p^α) : ZMod (p^(2*α) : ℕ))^2 = ((p^α)^2 : ZMod (p^(2*α) : ℕ))
    have hpα : (p^α)^ 2 = p^(2 * α) := by ring
    sorry
    -- rw [hpα]
    -- rw [ZMod.nat_cast_self]
  } 
  refine isUnit_of_dvd_one ?h.h
  -/


  /- 
  show that 1 + ↑1 * ↑(p ^ α) is an unit
  -/






  -- more of a definition
  /-
  simp
  -- norm_cast
  have H : (1+ p^α).gcd (p^(2*α)) = 1 := by sorry 
  -- refine Nat.coprime.pow_right (2 * α) ?H.H1
  -- refine Nat.coprime_of_dvd' ?H.H1.H
  -/ 

lemma MulChar_one_Unit : IsUnit (χ' (χ) (1) : ℂ) := by
  apply Ne.isUnit
  exact MulChar_one_nonZero χ

/- 
lemma MulChar_one_rootOfUnity' (ζ : ℂˣ) (hchar: ζ = χ' (χ) 1) (q : ℕ+) (hpq : q = p^α) :
    (χ' (χ) (1)) ∈ rootsOfUnity (q) ℂ := by
  rw [hchar]
  have H : 
  apply ← mem_roots_of_unity
-/


lemma congr_IntToNat' {q : ℕ} (a : ℤ) (haq : ((a : ZMod q).val).gcd q = 1) [NeZero q]: ∃(a₁ : ℕ), (a₁.coprime q) ∧ (a ≡ a₁ [ZMOD q]) := by
  use (a : ZMod q).val
  apply And.intro
  · exact haq
  · rw [← ZMod.int_cast_eq_int_cast_iff]
    simp


/-
-- def eZMod (q : ℕ) (x : ZMod q) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x.val / q)
lemma congr_eZMod (x₁ x₂ : ℕ) (h : x₁ ≡ x₂ [MOD (p^α)]): 
    eZMod (p^α : ℕ) (x₁) = eZMod (p^α : ℕ) (x₂) := by
  sorry

-/


  /-
  def eZMod (q : ℕ) (x : ZMod q) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x.val / q)

  def kloostermanSum (a : ℤ) (b : ℤ) (q : ℕ) : ℂ :=
  ∑ x : (ZMod q)ˣ, eZMod q (a*x + b*x⁻¹)
  -/

lemma congr_val (q : ℕ) (x₁ x₂ : ZMod q) : 
    (x₁ * x₂).val ≡ x₁.val * x₂.val [MOD q] := by
  rw [ZMod.val_mul x₁ x₂]
  exact Nat.mod_modEq (x₁.val * x₂.val) (q)

-- NeZero q
-- change the code if possible
lemma cexp_congr_eq (q : ℕ) (x₁ x₂ : ℕ) {congr_h : x₁ ≡ x₂ [ZMOD q]} {h : q ≠ 0}: 
    Complex.exp (2 * Real.pi * Complex.I * x₁/q) = Complex.exp (2 * Real.pi * Complex.I * x₂/q) := by
  -- apply congr_arg
  -- originally, we had (c : ℕ)
  -- originally, we had (q : ℕ)
  have H : ∃(c : ℤ), (x₁ : ℂ) = (x₂ : ℂ) + c * (q : ℤ)
  { simp
    have exist_const := Iff.mp Int.modEq_iff_add_fac (congr_h)
    cases' exist_const with t ht
    use (-t)
    norm_cast
    ring
    apply eq_sub_of_add_eq
    rw [mul_comm]
    symm
    exact ht  }
  cases' H with c Hc
  rw [Hc]
  simp
  have complex_ne_q : (q : ℂ) ≠ 0 := by exact Iff.mpr Nat.cast_ne_zero h
  have cancel_q : (q : ℂ)*(q : ℂ)⁻¹ = 1 := by rwa [Complex.mul_inv_cancel]
  have cancel_q' : ∀ z : ℂ, z * (q : ℂ) * (q⁻¹ : ℂ) = z
  { intro z
    rw [mul_assoc, cancel_q, mul_one] }
  have newExpression : 2 * Real.pi * Complex.I * ((x₂ : ℂ) + c * q)/q = 2 * Real.pi * Complex.I * (x₂ : ℂ)/q + 2 * Real.pi * Complex.I * c 
  { field_simp
    ring }
  rw [newExpression]
  rw [Complex.exp_add]
  have useful : 2 * Real.pi * Complex.I * c = c * (2 * Real.pi * Complex.I) := by ring
  rw [useful]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  ring
  -- exp_int_mul_two_pi_mul_I
  -- apply congr_arg
  
/- 
lemma mul_val' (q : ℕ) (x₁ x₂ : ZMod q) : 
    Complex.exp (2 * Real.pi * Complex.I * (x₁*x₂).val/q) = Complex.exp (2 * Real.pi * Complex.I * (x₁.val * x₂.val)/q) := by
  have congrVal := congr_val (q) (x₁) (x₂)
  -- originally, we had (c : ℕ)
  have H : ∃(c : ℕ), (x₁*x₂).val = (x₁.val * x₂.val) - c * (p^α)
  { sorry

  }
  cases' H with c Hc
  rw [Hc]
-/  
  
  

  /-
  have valMul : ((b : ZMod (p^α : ℕ)) * z).val = (b : ZMod (p^α)).val * z.val % (p^α) := by exact ZMod.val_mul (↑b) z
  rw [valMul]
  have H : ∃(c : ℕ), (b : ZMod (p^α)).val * z.val % (p^α) = (b : ZMod (p^α)).val * z.val - c * (p^α) := by sorry
  cases' H with c Hc
  rw [Hc]
  have HH : ∃(c₁ : ℤ), ↑(((b : ZMod (p^α)).val * z.val - c * (p^α))) = (((b : ZMod (p^α)).val : ℂ)  * (z.val : ℂ) - c₁ * (p^α)) 
  -/

/- 
lemma ZMod_b (b : ℕ) (p : ℕ) (hp : Prime p) (α : ℕ) [NeZero (p^α : ℕ)] :
    (b : ZMod (p^α)) ≡ b [ZMOD (p^α)] := by 
  sorry

lemma ZMod_exists_const (b : ℕ) (p : ℕ) (hp : Prime p) (α : ℕ) [NeZero (p^α : ℕ)] :
    ∃(c : ℤ), (b : ZMod (p^α)) = b - c * (p^α : ℕ) := by
  sorry



-- final goal
lemma congr_b_val (b : ℕ) (p : ℕ) (hp : Prime p) (α : ℕ) [NeZero (p^α : ℕ)] :
    (b : ZMod (p^α)).val ≡ b [ZMOD (p^α)] := by
  rw [Int.modEq_iff_add_fac]
  sorry
-/

-- need to decide how to capitalize it
-- need to show that `χ' (χ) (z)` is equal to a root of unity
theorem MulChar_additive_eq_exp (p : ℕ) (hp : Prime p) (α : ℕ) (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    ∃(b : ℕ), b < p^α ∧ χ' (χ) (z) = eZMod (p^α : ℕ) (b*z) := by
  have : NeZero (p^α) := ⟨pow_ne_zero α $ Prime.ne_zero hp⟩
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
  -- have zeta_pow : (ζ : ℂ)^(q : ℕ) = 1
  have ZetaOne : (ζ : ℂ)^(q : ℕ) = 1 := by
    rw [hζ, hq, MulChar_equal_one]
  -- why do both ζ and q : ?m.1264417
  have ofunity : ζ ∈ rootsOfUnity q ℂ ↔ ((ζ : ℂˣ) : ℂ) ^ ((q : ℕ+) : ℕ) = 1 := by
    simp [mem_rootsOfUnity']
    simp [Units.ext_iff]
  have root : ζ ∈ rootsOfUnity q ℂ
  { rw [ofunity, hζ, hq, MulChar_additive_pow, ZMod.nat_cast_self]
    ring
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
  /- previous version
  we have `MOD` instead of `ZMOD`
  have congr_val : ((b : ZMod (p^α : ℕ)) * z).val ≡ (b : ZMod (p^α)).val * z.val [MOD (p^α)]
  { rw [ZMod.val_mul (↑b) z]
    exact Nat.mod_modEq ((b : ZMod (p^α)).val * ZMod.val z) (p ^ α) }
  -/

  have new_NeZero : p^α ≠ 0 := by exact NeZero.ne (p^α)
  have val_b : (b : ZMod (p^α)).val ≡ b [ZMOD (p^α)]
  { simp
    simp [hb.1]
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
    -- have b ≡ (b : ZMod (p^α)) [ZMOD (p^α)]
  · exact congr_val
  · exact new_NeZero
  done


 





  




  /-
  have valMul : ((b : ZMod (p^α : ℕ)) * z).val = (b : ZMod (p^α)).val * z.val % (p^α) := by exact ZMod.val_mul (↑b) z
  rw [valMul]
  have H : ∃(c : ℕ), (b : ZMod (p^α)).val * z.val % (p^α) = (b : ZMod (p^α)).val * z.val - c * (p^α) := by sorry
  cases' H with c Hc
  rw [Hc]
  have HH : ∃(c₁ : ℤ), ↑(((b : ZMod (p^α)).val * z.val - c * (p^α))) = (((b : ZMod (p^α)).val : ℂ)  * (z.val : ℂ) - c₁ * (p^α)) 
  -/

  



  /- 
  step 1 : 
  ↑b.val + z.val % p^α = ↑b.val + z.val + c * p^α where c is an integer 

  step 2 :
  deal with the coercion to the complex. 
  make ↑(↑b.val + z.val + c * p^α) to ↑↑b.val + ↑z.val + ↑c * p^α

  step 3 :
  inside the exponential, it reduces to 
  ↑b.val + z.val since (c * p^α) is an integer

  step 4 : 
  try out ring 
  -/

  

  
  
  

  /- 
  ↑(↑b * z) = ↑↑b * ↑z
  or
  ↑(↑b * z) = ↑↑b * ↑z + multiples of p^α
  
  
  
  -/


  /- 
  rw [ofunity]
    rw [hζ, hq]
    rw [MulChar_additive_pow]
    rw [ZMod.nat_cast_self]
  
  
  -/
  


  -- complex.exp_int_mul

  -- have H : Complex.exp (↑(2 * Real.pi) * I * (↑b / ↑(p ^ α)))^z.val = Complex.exp (↑(2 * Real.pi) * I * (↑b/ ↑(p ^ α))*z.val) := by
    

  -- have H := hb.right
  -- rw [ZMod.val_mul]
  -- rw [ZMod.val_mul (↑b) z]
  -- have H (b : ℕ): (b * z).val = (b : ZMod (p^α)).val * z.val % (p^α) := by exact ZMod.val_mul (↑b) z
  


  -- `theorem zmod.val_mul`

  -- `theorem zmod.cast_eq_val`
  -- `theorem zmod.nat_cast_zmod_val`
  -- `theorem zmod.nat_cast_val`



  -- rw [ZMod.val_mul']


  -- `theorem complex.exp_nat_mul`
  -- `theorem complex.exp_int_mul`



  /-
  rw [powpow z.val] at root
  simp only [powpow z.val] at root
  -/


  /- first attempt
  rw [← MulChar_additive_pow_val]
  have newExpression : ∃(ζ : ℂˣ), (ζ : ℂˣ) = (χ' (χ) (1) : ℂ)
  { have H := MulChar_one_Unit χ
    rw [IsUnit] at H
    exact H }
  have primepow_pos : ∃(q : ℕ+), q = p^α
  { refine CanLift.prf (p ^ α) ?primepow_pos.a
    exact Fin.size_positive' }
  cases' newExpression with ζ hζ
  cases' primepow_pos with q hq
  -- have zeta_pow : (ζ : ℂ)^(q : ℕ) = 1
  have ZetaOne : (ζ : ℂ)^(q : ℕ) = 1
  { rw [hζ, hq]
    rw [MulChar_equal_one]  }
  have ZetaOne_coe : ((ζ : ℂˣ)^(q : ℕ) : ℂ) = 1 → (ζ : ℂˣ)^(q : ℕ) = 1
  { apply?
    
    intro h
    -- rw [Units.eq_iff]
    simp at h

    


  }
  have root : ζ ∈ rootsOfUnity q ℂ
  { simp [mem_rootsOfUnity']


    
    
    sorry
    -- refine Iff.mpr (mem_rootsOfUnity' q ζ) (id (Eq.symm hζ)))
    -- theorem mem_rootsOfUnity
  }
  rw [Complex.mem_rootsOfUnity, hq, hζ] at root
  have power : ∃(i₁ : ℕ), i₁ < p^α ∧ (Complex.exp (2 * Real.pi * Complex.I * (i₁ / (p^α : ℂ))))^z.val = χ' (χ) (1)^z.val
  { sorry

  }
  simp only [eZMod]
  rw [ZMod.val_mul]

  sorry
  -/

  /- second attempt
  rw [← MulChar_additive_pow_val]
  have newExpression : ∃(ζ : ℂˣ), (ζ : ℂˣ) = (χ' (χ) (1) : ℂ)
  { have H := MulChar_one_Unit χ
    rw [IsUnit] at H
    exact H }
  have primepow_pos : ∃(q : ℕ+), q = p^α
  { refine CanLift.prf (p ^ α) ?primepow_pos.a
    exact Fin.size_positive' }
  cases' newExpression with ζ hζ
  cases' primepow_pos with q hq
  -- have zeta_pow : (ζ : ℂ)^(q : ℕ) = 1
  have ZetaOne : (ζ : ℂ)^(q : ℕ) = 1
  { rw [hζ, hq]
    rw [MulChar_equal_one]  }
  have ZetaOne_coe : ((ζ : ℂˣ)^(q : ℕ) : ℂ) = 1 → (ζ : ℂˣ)^(q : ℕ) = 1
  { 
    
    intro h
    -- rw [Units.eq_iff]
    simp at h

    


  }
  -- why do both ζ and q : ?m.1264417
  have ofunity : ζ ∈ rootsOfUnity q ℂ ↔ ((ζ : ℂˣ) : ℂ) ^ ((q : ℕ+) : ℕ) = 1 := by
    exact iff_of_true (ZetaOne_coe ZetaOne) ZetaOne
    
  have root : ζ ∈ rootsOfUnity q ℂ
  { rw [ofunity]



    
    
    sorry
    -- refine Iff.mpr (mem_rootsOfUnity' q ζ) (id (Eq.symm hζ)))
    -- theorem mem_rootsOfUnity
  }
  rw [Complex.mem_rootsOfUnity, hq, hζ] at root
  have power : ∃(i₁ : ℕ), i₁ < p^α ∧ (Complex.exp (2 * Real.pi * Complex.I * (i₁ / (p^α : ℂ))))^z.val = χ' (χ) (1)^z.val
  { sorry

  }
  simp only [eZMod]
  rw [ZMod.val_mul]
  sorry
  
  
  -/
















/-
  -- theorem mem_roots_of_unity
  -- theorem Complex.mem_rootsOfUnity
  -- has the exponential form 
theorem MulChar_additive_eq_exp' (p : ℕ) (hp : Prime p) (α : ℕ) (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    (χ' (χ) (z)) ∈ rootsOfUnity (p^α : ℕ) ℂ  := by
  -- to use the theorem IsPrimitiveRoot.iff_def
  have iff_def : (χ' (χ) (z))^(p^α : ℕ) = 1 ∧ ∀ (l : ℕ), (χ' (χ) (z))^l = 1 → (p^α : ℕ) ∣ l 
  apply And.intro
  · exact MulChar_equal_one z χ
  · intro l hl
    sorry
    -- order_of_dvd_of_pow_eq_one
    -- order_of_eq_iff 
  sorry
    
    /- induction' l with l ihl
    · norm_num
    · simp [exists_eq_mul_right_of_dvd]
      -- dvd for ∣
      norm_num at *
      sorry
    -/
  -- apply Is.PrimitiveRoot.iff_def






  -- rw [← is_primitive_root.iff_def]


  -- zmodChar
  -- `theorem isPrimitiveRoot_iff` from Mathlib/RingTheory/RootsOfUnity/Complex.lean

-/



/- # Questions to Kevin
1. How to make 
2. I loathe how I wrote down theorem `MulChar_one_rootOfUnity`. Is there a way to make it better?
3. 


-/


/- # Note to myself
1. need to learn how to capitalize the names of the theorems
2. I abuse have tactic too much especially since I don't know how to use fancy tactics

-/