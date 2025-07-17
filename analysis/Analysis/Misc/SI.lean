import Mathlib.Tactic
import Analysis.Misc.UnitsSystem


/-- The SI unit system. -/
@[ext]
structure SI_dimensions where
  units_length : ℤ
  units_mass : ℤ
  units_time : ℤ
  units_current : ℤ
  units_temperature : ℤ
  units_amount : ℤ
  units_intensity : ℤ
deriving DecidableEq

instance SI_dimensions.instZero : Zero SI_dimensions where
  zero := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- The addition structure here is simple enough that one gets a lot of definitional equalities, e.g., between `d₁+d₂` and `d₂+d₁` for explicit choices of `d₁` and `d₂`,
which is convenient as it means we do not need to utilize the `cast` operator much. -/
instance SI_dimensions.instAdd : Add SI_dimensions where
  add d₁ d₂ := ⟨d₁.units_length + d₂.units_length,
                d₁.units_mass + d₂.units_mass,
                d₁.units_time + d₂.units_time,
                d₁.units_current + d₂.units_current,
                d₁.units_temperature + d₂.units_temperature,
                d₁.units_amount + d₂.units_amount,
                d₁.units_intensity + d₂.units_intensity
                ⟩

instance SI_dimensions.instNeg : Neg SI_dimensions where
  neg d := ⟨-d.units_length, -d.units_mass, -d.units_time, -d.units_current,
            -d.units_temperature, -d.units_amount, -d.units_intensity⟩

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

abbrev length_unit :Dimensions := ⟨1, 0, 0, 0, 0, 0, 0⟩
abbrev Length := Scalar length_unit
abbrev meter:Length := StandardUnit _

abbrev mass_unit :Dimensions := ⟨0, 1, 0, 0, 0, 0, 0⟩
abbrev Mass := Scalar mass_unit
abbrev kilogram:Mass := StandardUnit _

abbrev time_unit :Dimensions := ⟨0, 0, 1, 0, 0, 0, 0⟩
abbrev Time := Scalar time_unit
abbrev second:Time := StandardUnit _

abbrev current_unit :Dimensions := ⟨0, 0, 0, 1, 0, 0, 0⟩
abbrev Current := Scalar current_unit
abbrev ampere:Current := StandardUnit _

abbrev temperature_unit :Dimensions := ⟨0, 0, 0, 0, 1, 0, 0⟩
abbrev Temperature := Scalar temperature_unit
abbrev kelvin:Temperature := StandardUnit _

abbrev amount_unit :Dimensions := ⟨0, 0, 0, 0, 0, 1, 0⟩
abbrev Amount := Scalar amount_unit
abbrev mole:Amount := StandardUnit _

abbrev intensity_unit :Dimensions := ⟨0, 0, 0, 0, 0, 0, 1⟩
abbrev Intensity := Scalar intensity_unit
abbrev candela:Intensity := StandardUnit _

abbrev speed_unit := length_unit - time_unit
abbrev Speed := Scalar speed_unit

abbrev acceleration_unit := length_unit - (2 • time_unit)
abbrev Acceleration := Scalar acceleration_unit

abbrev momentum_unit := mass_unit + speed_unit
abbrev Momentum := Scalar momentum_unit

abbrev energy_unit := mass_unit + (2 • speed_unit)
abbrev Energy := Scalar energy_unit
abbrev joule:Energy := StandardUnit _

abbrev force_unit := mass_unit + acceleration_unit
abbrev Force := Scalar force_unit
abbrev newton:Force := StandardUnit _

abbrev frequency_unit := -time_unit
abbrev Frequency := Scalar frequency_unit
abbrev hertz:Frequency := StandardUnit _

abbrev pressure_unit := force_unit - (2 • length_unit)
abbrev Pressure := Scalar pressure_unit
abbrev pascal:Pressure := StandardUnit _





end SI
