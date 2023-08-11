import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Fourier.AddCircle

@[simps!]
def ZMod.toQuotient (A) [AddCommGroupWithOne A] (q : ℕ) :
    ZMod q →+ A ⧸ AddSubgroup.zmultiples (q : A) :=
  ZMod.lift _ ⟨(QuotientAddGroup.mk' _).comp (Int.castAddHom A), by simp⟩

/-- A bundled version of `AddCircle.toCircle` -/
@[simps!]
noncomputable def AddCircle.toCircleHom (r : ℝ) : AddCircle r →+ Additive circle :=
  AddMonoidHom.mk' AddCircle.toCircle AddCircle.toCircle_add

-- note that we need to introduce `K` and all the extra assumptions since `AddCircle` isn't allowed on `ℤ`.
noncomputable abbrev ZMod.toAddCircle (K) [LinearOrderedRing K] [TopologicalSpace K] [OrderTopology K] (q : ℕ) :
    ZMod q →+ AddCircle (q : K) :=
  ZMod.toQuotient K q

-- circ
-- The canonical map fun z => exp (2 π i z / T) 
noncomputable abbrev ZMod.toCircle {q : ℕ} (z : ZMod q) : circle :=
  (ZMod.toAddCircle _ _ z).toCircle

noncomputable abbrev ZMod.toCircleHom (q : ℕ) : ZMod q →+ Additive circle :=
  (AddCircle.toCircleHom _).comp (ZMod.toAddCircle _ _)

/-
@[simps!]
def ZMod.toIntQuotient (q : ℕ) :
    ZMod q ≃+ ℤ ⧸ AddSubgroup.zmultiples (q : ℤ) :=
  AddMonoidHom.toAddEquiv
    (ZMod.lift _ ⟨QuotientAddGroup.mk' _, by simp⟩)
    ({ toFun := (sorry : Function.Periodic (Int.cast : ℤ → ZMod q) q).lift
       map_zero' := sorry
       map_add' := sorry })
    sorry
    sorry
-/

variable (q : ℕ) (x : ZMod q)

-- lemma eZMod_def : ZMod.toCircle x = Complex.exp (2 * Real.pi * Complex.I * x.val / q) := rfl

lemma ZMod.toCircle_add (x y : ZMod q) (zero_ne_hq : q ≠ 0) : ZMod.toCircle (x + y) = ZMod.toCircle x * ZMod.toCircle y := by
  
  
  simp_rw [ZMod.toCircle]
  simp_rw [ZMod.toAddCircle]
  simp_rw [AddCircle.toCircle]
  simp -- so don't need something like this rw [← Quotient.mk_add]
  --------------
  -- simp_rw [Function.Periodic.lift_coe]




  simp_rw [expMapCircle_add]
  simp_rw [Function.Periodic.lift_coe]
  
  induction x using QuotientAddGroup.induction_on'
  induction y using QuotientAddGroup.induction_on'
  rw [← QuotientAddGroup.mk_add]
  simp_rw [toCircle, Function.Periodic.lift_coe, mul_add, expMapCircle_add]



/-
lemma ZMod.toCircleHom_add (x y : ZMod q) (zero_ne_hq : q ≠ 0) : 
  @ZMod.toCircleHom q (x + y) = (ZMod.toCircleHom x) * (ZMod.toCircleHom y) := by
-/

  


