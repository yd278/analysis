import Mathlib.Tactic
import Analysis.Misc.UnitsSystem


/-- Example: SI units -/

@[ext]
structure SI_dimensions where
  units_length : ℤ
  units_mass : ℤ
  units_time : ℤ
deriving DecidableEq

instance SI_dimensions.instZero : Zero SI_dimensions where
  zero := ⟨0, 0, 0⟩

instance SI_dimensions.instAdd : Add SI_dimensions where
  add d₁ d₂ := ⟨d₁.units_length + d₂.units_length, d₁.units_mass + d₂.units_mass, d₁.units_time + d₂.units_time⟩

instance SI_dimensions.instNeg : Neg SI_dimensions where
  neg d := ⟨-d.units_length, -d.units_mass, -d.units_time⟩

instance SI_dimensions.instAddGroup : AddGroup SI_dimensions :=
AddGroup.ofLeftAxioms
  (by intros; simp_rw [HAdd.hAdd, Add.add]; simp [add_assoc])
  (by intros; simp_rw [HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]; simp)
  (by intros; simp_rw [Neg.neg, HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]; simp [Int.Linear.neg_fold])

instance SI_dimensions.instAddCommGroup : AddCommGroup SI_dimensions where
  add_comm d₁ d₂ := by
    simp_rw [HAdd.hAdd, Add.add]; simp [add_comm]

abbrev SI : UnitsSystem := {
  Dimensions := SI_dimensions
  addCommGroup := SI_dimensions.instAddCommGroup
}

instance instSI : UnitsSystem := SI

namespace SI
open UnitsSystem


abbrev Dimensionless := Scalar (0:Dimensions)
abbrev Length := Scalar (⟨1, 0, 0⟩:Dimensions)
abbrev Mass := Scalar (⟨0, 1, 0⟩:Dimensions)
abbrev Time := Scalar (⟨0, 0, 1⟩:Dimensions)
abbrev Speed := Scalar (⟨1, 0, -1⟩:Dimensions)
abbrev Acceleration := Scalar (⟨1, 0, -2⟩:Dimensions)
abbrev Momentum := Scalar (⟨1, 1, -1⟩:Dimensions)
abbrev Energy := Scalar (⟨2, 1, -2⟩:Dimensions)
abbrev Force := Scalar (⟨1, 1, -2⟩:Dimensions)

variable (m:Mass) (v c:Speed) (F:Force) (p:Momentum) (E:Energy) (s:Length) (t:Time) (a:Acceleration)

#check F = m * a
#check E = m * c**2
-- #check E = m * c**3  -- fails to typecheck



end SI
