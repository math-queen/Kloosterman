import Mathlib.Tactic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Taylor
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Deprecated.Subgroup
import Kloosterman.lemma_char_v4
import Kloosterman.def2_v3_kloosterman
import Kloosterman.rationalfunc_v4

set_option autoImplicit false

open Complex BigOperators Set IsGroupHom

noncomputable section

-- open IsSubmonoid IsSubgroup

variable {p α : ℕ} (z : ZMod (p ^ (α + 1))) 

variable (hα : 0 < α) [pp : Fact p.Prime] -- (hp : p.Prime)
-- I don't think `Fact p.prime` is a good idea. The system doesn't recognize it 

/-
First isomorphism theorem :
https://github.com/leanprover-community/mathlib4/blob/93e2bebd1c0c0d94148ac996cd438d00a4042c74/Mathlib/GroupTheory/QuotientGroup.lean#L400 

https://leanprover-community.github.io/mathlib_docs/group_theory/quotient_group.html#quotient_group.quotient_ker_equiv_range 

-/

/- 
might be proven useful 
Theorem that shows that kernel of the group homomorphism is a normal subgroup
`is_group_hom.is_normal_subgroup_ker`


is_group_hom.mem_ker 

-/


instance : NeZero (p ^ α) := NeZero.pow

instance : NeZero (p ^ (2 * α + 1)) := NeZero.pow

instance : Fact (1 < p ^ (2 * α + 1)) := by
  have hp : 1 < p := Nat.Prime.one_lt (Fact.out (p := p.Prime))
  exact { out := (Nat.one_lt_pow (2 * α + 1) p (Nat.succ_pos (2 * α)) hp) }

lemma pPow_dvd_pTwoaddOnePow : p ^ α ∣ p ^ (2 * α + 1) := ⟨p ^ (α + 1), by ring⟩

lemma pPow_lt_pTwoaddOnePow : p ^ α < p ^ (2 * α + 1) := by
  apply pow_lt_pow
  · exact Nat.Prime.one_lt (Fact.out (p := p.Prime)) -- takes out the variable from the inside of Fact
  · linarith

lemma ZModptwoPow_to_ZModpPow_isUnit (r : (ZMod (p ^ (2 * α + 1)))ˣ) : IsUnit (r : ZMod (p ^ α)) := by
  have : IsUnit r := by exact Group.isUnit r
  rw [isUnit_iff_exists_inv] at *
  cases' this with b hb
  use (b : ZMod (p ^ α))
  
  
  rw [← ZMod.int_cast_zmod_cast (r : ZMod (p ^ (2 * α + 1)))]
  rw [ZMod.cast_int_cast pPow_dvd_pTwoaddOnePow]
  sorry


  /-
  rw [isUnit_iff_exists_inv] at *
  cases' this with b hb
  use (b : ZMod (p ^ α))
  -/

lemma unit_exists_for_isUnit (r : (ZMod (p ^ (2 * α + 1)))ˣ) : ∃(n : (ZMod (p ^ α))ˣ), n = (r : ZMod (p ^ α)) := by 
  have := ZModptwoPow_to_ZModpPow_isUnit r 
  rw [IsUnit] at this
  exact this
-- choose_spec the above instance. Then have it as the image for def φ below

def unit_exists_for_isUnit_r (r : (ZMod (p ^ (2 * α + 1)))ˣ) : (ZMod (p ^ α))ˣ := (unit_exists_for_isUnit r).choose

theorem unit_exists_for_isUnit_r_spec (r : (ZMod (p ^ (2 * α + 1)))ˣ) :
  (unit_exists_for_isUnit_r r) = (r : ZMod (p ^ α)) := (unit_exists_for_isUnit r).choose_spec

-- instance IsGroup (ZMod (p ^ (2 * α + 1)))ˣ := by sorry

def φ : (ZMod (p ^ (2 * α + 1)))ˣ → (ZMod (p ^ α))ˣ :=
  fun r => unit_exists_for_isUnit_r r

/- for the theorem `ZModptwoPow_to_ZModpPow_isHom` -/
instance : Group (ZMod (p ^ (2 * α + 1)))ˣ := Units.instGroupUnits

instance : CommGroup (ZMod (p ^ (2 * α + 1)))ˣ := Units.instCommGroupUnitsToMonoid

/- for the theorem `ZModptwoPow_to_ZModpPow_isHom` -/
instance : Group (ZMod (p ^ α))ˣ := by exact Units.instGroupUnits

theorem zmod_units_castHom_IsGroupHom : IsGroupHom (φ (p := p) (α := α)) := by 
  have hφ : ∀(x y : (ZMod (p ^ (2 * α + 1)))ˣ), φ (x * y) = φ x * φ y 
  { intro x y
    unfold φ
    ext
    rw [Units.val_mul]
    simp only [unit_exists_for_isUnit_r_spec]
    rw [← ZMod.cast_mul pPow_dvd_pTwoaddOnePow (x : ZMod (p ^ (2 * α + 1))) (y : ZMod (p ^ (2 * α + 1)))]
    rfl }
  exact IsGroupHom.mk' hφ 

def G : Set (ZMod (p ^ (2 * α + 1)))ˣ := {r : (ZMod (p ^ (2 * α + 1)))ˣ | (r : ZMod (p ^ α)) = 1}

theorem ker_ofphi_eq_G : ker (φ (p := p) (α := α)) = G := by
  ext r
  rw [mem_ker]
  unfold G
  unfold φ
  simp only [mem_setOf_eq]
  rw [Units.ext_iff]
  rw [unit_exists_for_isUnit_r_spec r]
  rw [Units.val_one]

theorem ZModptwoPow_to_ZModpPow_isHom : IsNormalSubgroup (G := (ZMod (p ^ (2 * α + 1)))ˣ) G := by
  convert isNormalSubgroup_ker zmod_units_castHom_IsGroupHom
  exact Eq.symm ker_ofphi_eq_G

/- defines the subgroup G of the group (ZMod (p ^ (2 * α + 1)))ˣ -/
def Subgroup_G : Subgroup (ZMod (p ^ (2 * α + 1)))ˣ := Subgroup.of (ZModptwoPow_to_ZModpPow_isHom (p := p) (α := α)).toIsSubgroup

lemma zmod_iff_int_coe (a b : ZMod (p ^ (2 * α + 1))) : (a : ℤ) = (b : ℤ) ↔ a = b := by 
  constructor
  · intro h
    rw [← ZMod.int_cast_zmod_cast a]
    rw [← ZMod.int_cast_zmod_cast b]
    rw [h]
  · intro h
    rw [h]

/- for the below lemma `ZMod_int_cast_add` -/
lemma ZMod_val_cast_add (q : ℕ) (a b : ZMod q) [NeZero q] (h : a.val + b.val < q) :
    (a + b : ZMod q).val = a.val + b.val := by
  rw [ZMod.val_add]
  exact Nat.mod_eq_of_lt h

lemma ZMod_int_cast_add (q : ℕ) (a b : ZMod q) [NeZero q] (h : (a + b : ℤ) < q) :
    ((a + b : ZMod q) : ℤ) = (a + b : ℤ) := by
  suffices ((a + b : ZMod q).val) = (a.val + b.val) by
    repeat rw [← ZMod.nat_cast_val]
    rw [this]
    rfl 
  have hval : a.val + b.val < q
  { repeat rw [← ZMod.nat_cast_val] at h
    exact Iff.mp Int.ofNat_lt h }
  exact ZMod_val_cast_add q a b hval

lemma zmod_int_one (q : ℕ) [Fact (1 < q)] : ((1 : ZMod q) : ℤ) = 1 := by 
  suffices (1 : ZMod q).val = 1 by
    rw [← ZMod.nat_cast_val]
    simp only [this]
  exact ZMod.val_one q

lemma valZModLarger_eq_ZModSmaller'' {a b : ℕ} (h : b ≤ a) [NeZero b] (n : ZMod b) : 
    (n : ZMod a).val = n.val := by
  rw [ZMod.cast_eq_val]
  rw [ZMod.val_cast_of_lt]
  suffices n.val < b by
    exact Nat.lt_of_lt_of_le this h
  exact ZMod.val_lt n

lemma IntZModLarger_eq_ZModSmaller {a b : ℕ} (h : b ≤ a) [NeZero b] (n : ZMod b) : 
    ((n : ZMod a) : ℤ) = (n : ℤ) := by
  suffices (n : ZMod a).val = n.val by
    have hb : 0 < b := by exact Fin.size_positive'
    have ha : NeZero a := ⟨by linarith⟩
    rw [← ZMod.nat_cast_val]
    rw [this]
    exact ZMod.nat_cast_val n
  exact valZModLarger_eq_ZModSmaller h n

/- Previous version 
-- i don't think coercing to units is possible
theorem element_of_G_eq [NeZero (p ^ (2 * α + 1))] (r : Subgroup_G (p := p) (α := α)) :
    ∃(z₀ : ZMod (p ^ (α + 1))), r.val = 1 + (z₀ : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) := by
  have hr : r.val ∈ Subgroup_G := by exact SetLike.coe_mem r
  unfold Subgroup_G at hr
  simp only [G] at hr
  have : (r.val : ZMod (p ^ α)) = 1 := by exact hr
  rw [← ZMod.int_cast_zmod_cast (r.val : ZMod (p ^ (2 * α + 1)))] at this
  rw [ZMod.cast_int_cast pPow_dvd_pTwoaddOnePow] at this
  rw [← Int.cast_one] at this
  rw [ZMod.int_cast_eq_int_cast_iff] at this
  have hn : ∃(n : ℤ), 0 < n ∧ ((r.val : ZMod (p ^ (2 * α + 1))) : ℤ) = 1 + n * (p ^ α : ℤ)
  { 
    sorry
  }
  cases' hn with n hn
  use n
  rw [← zmod_iff_int_coe]

  have hmul_lt : (((n : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) : ℤ) < p ^ (2 * α + 1)
  { rw [lt_nat_coe_zmod_coe_int_eq_coe_int (h := pPow_lt_pTwoaddOnePow hα)]
    rw [IntZModLarger_eq_ZModSmaller]
    rw [pow_add p (2 * α) 1]
    rw [pow_one]
    rw [mul_comm 2 α]
    rw [pow_mul]
    rw [Nat.cast_mul]
    rw [Nat.cast_pow (p ^ α) 2]
    rw [pow_two]
    rw [← Int.lt_ediv_iff_mul_lt]
    -- rw [← Int.ediv_lt_iff_lt_mul (Iff.mpr Int.ofNat_pos Fin.size_positive')]
    · rw [mul_assoc]
      rw [mul_comm (p ^ α : ℤ) (p : ℤ)]
      rw [← mul_assoc]
      -- int.mul_div_assoc
      rw [Int.mul_ediv_assoc ((p ^ α : ℤ) * (p : ℤ)) (Int.dvd_refl ↑(p ^ α))]
      rw [Int.ediv_self (NeZero.natCast_ne (p ^ α) ℤ)]
      rw [mul_one]
      norm_cast
      have hp_pow_add : p ^ α * p = p ^ (α + 1) := rfl -- error : motive is not type correct
      rw [hp_pow_add]
      exact zmod_coe_int_lt (p ^ (α + 1)) (n : ZMod (p ^ (α + 1)))
    · exact Iff.mpr Int.ofNat_pos Fin.size_positive'
    · use (p ^ α : ℤ) * (p : ℤ)
      ring
    · apply pow_le_pow
      · exact Fin.size_positive'
      · rw [Nat.add_le_add_iff_right]
        exact Nat.le_of_lt (lt_two_mul_self hα)

    -- valZModLarger_eq_ZModSmaller'
    -- rw [lt_nat_coe_zmod_coe_int_eq_coe_int]
    -- rw [zmod_coe_int_lt]
    -- rw [← IntcoeZModLarger_eq_ZModSmaller]
  }
  have hn_self_lt : n < p ^ (α + 1)
  { have := zmod_coe_int_lt (p ^ (2 * α + 1)) (r.val : ZMod (p ^ (2 * α + 1)))
    rw [hn.right] at this
    rw [← mul_lt_mul_right (a := (p ^ α : ℤ)) (Iff.mpr Int.ofNat_pos Fin.size_positive')]
    norm_cast
    rw [← pow_add]
    rw [add_comm]
    rw [← add_assoc]
    rw [← two_mul]
    rw [← lt_tsub_iff_left] at this
    linarith
  }

  have he_self_eq : (((n : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) : ℤ) = n
  { rw [IntZModLarger_eq_ZModSmaller]
    rw [lt_nat_coe_zmod_coe_int_eq_coe_int (h := pPow_lt_pTwoaddOnePow)]
    -- lt_nat_coe_zmod_coe_int_eq_coe_int 
    sorry
  }

  have hadd_lt : ((1 : ZMod (p ^ (2 * α + 1))) : ℤ) + ((((n : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) : ZMod (p ^ (2 * α + 1))) : ℤ) < p ^ (2 * α + 1)
  { rw [ZMod_int_cast_mul (h := hmul_lt)]

    rw [ZMod.cast_one']
    sorry
  }
  /- previous version
  have hadd_lt : (1 + ((n : ZMod (p ^ α)) : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) : ℤ) < p ^ (2 * α + 1)
  {
    sorry
  }
  -/ 
  rw [ZMod_int_cast_add (h := hadd_lt)]
  rw [ZMod_int_cast_mul (h := hmul_lt)]

  /-
  have hn_self_lt : (((n : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) : ℤ) < p ^ (α + 1)
  { 
    sorry
  }
  -/ 
  rw [zmod_int_one]
  rw [he_self_eq]
  rw [lt_nat_coe_zmod_coe_int_eq_coe_int (h := pPow_lt_pTwoaddOnePow hα)]
  exact hn.right

-/

variable (r : Subgroup_G (p := p) (α := α)) 

-- i don't think coercing to units is possible
theorem element_of_G_eq :
    ∃(z₀ : ZMod (p ^ (α + 1))), r.val = 1 + (z₀ : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) := by
  have hr : r.val ∈ Subgroup_G := by exact SetLike.coe_mem r
  unfold Subgroup_G at hr
  simp only [G] at hr
  have : (r.val : ZMod (p ^ α)) = 1 := by exact hr
  rw [← ZMod.int_cast_zmod_cast (r.val : ZMod (p ^ (2 * α + 1)))] at this
  rw [ZMod.cast_int_cast pPow_dvd_pTwoaddOnePow] at this
  -- rw [← Int.cast_one] at this
  -- rw [ZMod.int_cast_eq_int_cast_iff] at this
  have hn : ∃(n : ℕ), ((r.val : ZMod (p ^ (2 * α + 1))) : ℤ) = 1 + n * (p ^ α : ℤ)
  { -- use (r.val : ZMod (p ^ (2 * α + 1))).val
    rw [ZMod.cast_eq_val (r.val : ZMod (p ^ (2 * α + 1)))] at this ⊢
    rw [Int.cast_ofNat (ZMod.val (r.val : ZMod (p ^ (2 * α + 1))))] at this
    rw [ZMod.nat_coe_zmod_eq_iff] at this
    cases' this with k hk
    rw [← Int.ofNat_inj] at hk
    rw [Nat.cast_add] at hk
    rw [Nat.cast_mul] at hk
    rw [mul_comm (p ^ α : ℤ) (k : ℤ)] at hk
    use k
    -- exact hk
    
    have hOne: ((1 : ZMod (p ^ α)).val : ℤ) = 1
    { -- have hNat_coe_int : ((1 : ℕ) : ℤ) = 1 := by exact rfl
      -- have : (p ^ α) ≠ 1 := by sorry
      -- have : (1 : ZMod (p ^ α)).val = 1 := by sorry 
      rw [ZMod.nat_cast_val]
      have : Fact (1 < p ^ α)
      { have hp : 1 < p := Nat.Prime.one_lt (Fact.out (p := p.Prime))
        exact { out := (Nat.one_lt_pow α p hα hp) }
      }
      rw [zmod_int_one]
      -- rw [← Nat.cast_one]

      -- rw [ZMod.cast_one']
      -- rw [← zmod_int_one]
    }

    rw [← hOne]
    exact hk
    -- exact ZMod.int_coe_zmod_eq_iff
    -- zmod.int_coe_zmod_eq_iff
  }
  cases' hn with n hn
  use n
  rw [← zmod_iff_int_coe]

  have hmul_lt : (((n : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) : ℤ) < p ^ (2 * α + 1)
  { rw [lt_nat_coe_zmod_coe_int_eq_coe_int (h := pPow_lt_pTwoaddOnePow hα)]
    rw [IntZModLarger_eq_ZModSmaller]
    rw [pow_add p (2 * α) 1]
    rw [pow_one]
    rw [mul_comm 2 α]
    rw [pow_mul]
    rw [Nat.cast_mul]
    rw [Nat.cast_pow (p ^ α) 2]
    rw [pow_two]
    rw [← Int.lt_ediv_iff_mul_lt]
    -- rw [← Int.ediv_lt_iff_lt_mul (Iff.mpr Int.ofNat_pos Fin.size_positive')]
    · rw [mul_assoc]
      rw [mul_comm (p ^ α : ℤ) (p : ℤ)]
      rw [← mul_assoc]
      -- int.mul_div_assoc
      rw [Int.mul_ediv_assoc ((p ^ α : ℤ) * (p : ℤ)) (Int.dvd_refl ↑(p ^ α))]
      rw [Int.ediv_self (NeZero.natCast_ne (p ^ α) ℤ)]
      rw [mul_one]
      norm_cast
      have hp_pow_add : p ^ α * p = p ^ (α + 1) := rfl -- error : motive is not type correct
      rw [hp_pow_add]
      exact zmod_coe_int_lt (p ^ (α + 1)) (n : ZMod (p ^ (α + 1)))
    · exact Iff.mpr Int.ofNat_pos Fin.size_positive'
    · use (p ^ α : ℤ) * (p : ℤ)
      ring
    · apply pow_le_pow
      · exact Fin.size_positive'
      · rw [Nat.add_le_add_iff_right]
        exact Nat.le_of_lt (lt_two_mul_self hα)

    -- valZModLarger_eq_ZModSmaller'
    -- rw [lt_nat_coe_zmod_coe_int_eq_coe_int]
    -- rw [zmod_coe_int_lt]
    -- rw [← IntcoeZModLarger_eq_ZModSmaller]
  }
  have hn_self_lt : n < p ^ (α + 1)
  { have := zmod_coe_int_lt (p ^ (2 * α + 1)) (r.val : ZMod (p ^ (2 * α + 1)))
    rw [hn] at this
    rw [← Int.ofNat_lt]
    rw [← mul_lt_mul_right (a := (p ^ α : ℤ)) (Iff.mpr Int.ofNat_pos Fin.size_positive')]
    rw [← Nat.cast_mul (p ^ (α + 1)) (p ^ α)]
    rw [← pow_add]
    rw [add_comm]
    rw [← add_assoc]
    rw [← two_mul]
    rw [← lt_tsub_iff_left] at this
    linarith
  }

  have hn_self_eq : (((n : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) : ℤ) = n
  { rw [IntZModLarger_eq_ZModSmaller]
    · rw [lt_nat_coe_zmod_coe_int_eq_coe_int]
      exact hn_self_lt
    · apply pow_le_pow
      · exact Fin.size_positive'
      · linarith
    -- lt_nat_coe_zmod_coe_int_eq_coe_int 
  }

  have hadd_lt : ((1 : ZMod (p ^ (2 * α + 1))) : ℤ) + ((((n : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) : ZMod (p ^ (2 * α + 1))) : ℤ) < p ^ (2 * α + 1)
  { rw [ZMod_int_cast_mul (h := hmul_lt)]
    rw [hn_self_eq]
    rw [lt_nat_coe_zmod_coe_int_eq_coe_int (h := pPow_lt_pTwoaddOnePow hα)]
    rw [zmod_int_one (p ^ (2 * α + 1))]
    rw [← hn]
    exact zmod_coe_int_lt (p ^ (2 * α + 1)) (r.val : ZMod (p ^ (2 * α + 1)))
  }
  /- previous version
  have hadd_lt : (1 + ((n : ZMod (p ^ α)) : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) : ℤ) < p ^ (2 * α + 1)
  {
    sorry
  }
  -/ 
  rw [ZMod_int_cast_add (h := hadd_lt)]
  rw [ZMod_int_cast_mul (h := hmul_lt)]

  /-
  have hn_self_lt : (((n : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) : ℤ) < p ^ (α + 1)
  { 
    sorry
  }
  -/ 
  rw [zmod_int_one]
  rw [hn_self_eq]
  rw [lt_nat_coe_zmod_coe_int_eq_coe_int (h := pPow_lt_pTwoaddOnePow hα)]
  exact hn


/- previous version
theorem element_of_G_eq_v1 (r : (ZMod (p ^ (2 * α + 1)))ˣ) (h : r ∈ Subgroup_G) : ∃(z₀ : ZMod (p ^ α)), r = 1 + (z₀ : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) := by
  
  
  sorry
-/

def element_of_G_eq_z : ZMod (p ^ (α + 1)) := (element_of_G_eq hα r).choose

-- ∃(z₀ : ZMod (p ^ (α + 1))), r.val = 1 + (z₀ : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1)))
theorem element_of_G_eq_z_spec :
    r.val = 1 + (((element_of_G_eq_z hα r) : ZMod (p ^ (α + 1))) : ZMod (p ^ (2 * α + 1))) * (p ^ α : ZMod (p ^ (2 * α + 1))) :=
  (element_of_G_eq hα r).choose_spec

def eZModOdd : ℂ := Complex.exp (2 * Real.pi * Complex.I * (z.val / (p ^ (α + 1) : ℂ) + (p - 1) * (z.val : ℂ) ^ 2 / (2 * p : ℂ)))

def eZModOdd_def : eZModOdd z = Complex.exp (2 * Real.pi * Complex.I * (z.val / (p ^ (α + 1) : ℂ) + (p - 1) * (z.val : ℂ) ^ 2 / (2 * p : ℂ))) := rfl

def ξ : Subgroup_G (p := p) (α := α) → ℂ :=
  fun r => eZModOdd (element_of_G_eq_z hα r)

-- fun r => r.val
-- ξ hα r = (r : (ZMod (p ^ (2 * α + 1)))ˣ) := by
lemma well_defined_xi : ξ hα r = eZModOdd (element_of_G_eq_z hα r) := rfl

-- `subgroup.of` creates the subgroup G

variable (χ : MulChar (ZMod (p ^ (2 * α + 1) : ℕ)) ℂ)

theorem chi_eq_xi :
    ∃(b : ℕ), b < p^α ∧ χ (1 + (element_of_G_eq_z hα r)) = ξ hα r ^ b := by
  sorry

theorem chi_eq_eZMod_for_subgroup :
    ∃(b : ℕ), b < p^α ∧ χ (1 + (element_of_G_eq_z hα r)) = eZModOdd (element_of_G_eq_z hα r) ^ b := by
  convert chi_eq_xi hα r χ
  done

theorem bruh :
    ∃(r₀ : Subgroup_G (p := p) (α := α)), z = element_of_G_eq_z hα r₀ := by
  unfold element_of_G_eq_z
  sorry

theorem chi_eq_eZMod_for_zmod : 
    ∃(b : ℕ), b < p^α ∧ χ (1 + z) = eZModOdd z ^ b := by
  have h := bruh z hα 
  cases' h with r₀ hr₀
  rw [hr₀]
  exact chi_eq_eZMod_for_subgroup hα r₀ χ


/-
Order to prove 
1. χ (1 + choose_spec) = ξ x
2. ξ x = exp (Big Nonsense in terms of choose_spec)
3. Thus for a given x, χ (1 + choose_spec) = exp (Big Nonsense in terms of choose_spec)
4. By proving that for a given z, there exists x s.t its choose_spec = z
5. Then we can write the expression 3 as χ (1 + z) = exp (Big Nonsense in terms of z)
-/





/- when building up the character ξ, think whether it would be more plausible to make it for ZMod (p ^ α), should I make it into 

because I need to the expression ξ x = ξ ( 1 + z * p ^ α )

but it seems like it wouldn't work unless I have ξ 's domain as a subgroup of ZMod (p ^ α) 

maybe I need to build another function that extends it to (ZMod (p ^ α))
something like ξ' : (ZMod (p ^ α)) → ℂˣ 
ξ' x = ξ x for x defined on domain of ξ
0 otherwise

take a look at how MulChar is defined
-/


