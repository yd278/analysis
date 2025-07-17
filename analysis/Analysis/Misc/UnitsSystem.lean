import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms


class UnitsSystem where
  Dimensions: Type*
  addCommGroup: AddCommGroup Dimensions

namespace UnitsSystem

variable [UnitsSystem]

instance Dimensions.instAddCommGroup : AddCommGroup Dimensions := UnitsSystem.addCommGroup

abbrev Formal := AddMonoidAlgebra ℝ Dimensions

@[ext]
structure Scalar (d:Dimensions) where
  val : ℝ

theorem Scalar.val_inj {d:Dimensions} (q₁ q₂:Scalar d) :
  q₁.val = q₂.val ↔ q₁ = q₂ := by aesop

def Scalar.cast {d d':Dimensions}  (q: Scalar d) (h : d' = d := by abel) : Scalar d' := _root_.cast (by rw [h]) q

theorem Scalar.cast_eq {d d':Dimensions} (q: Scalar d) (q': Scalar d') (h: d = d' := by abel) : q.val = q'.val ↔ q = q'.cast h := by aesop

theorem Scalar.cast_eq_symm {d d':Dimensions} (q: Scalar d) (q': Scalar d') (h: d = d' := by abel) : q = q'.cast h ↔ q' = q.cast h.symm := by aesop

@[simp]
theorem Scalar.cast_val {d d':Dimensions} (q: Scalar d) (h: d' = d := by abel) : (q.cast h).val = q.val := by aesop

@[coe]
noncomputable def Scalar.toFormal {d:Dimensions} (q:Scalar d) : Formal :=
  AddMonoidAlgebra.single d q.val

noncomputable instance Scalar.instCoeFormal (d: Dimensions) : CoeOut (Scalar d) Formal where
  coe := toFormal

@[simp]
theorem Scalar.toFormal_inj {d: Dimensions} (q₁ q₂:Scalar d) :
  (q₁:Formal) = (q₂:Formal) ↔ q₁ = q₂ := by
  constructor
  . simp [toFormal, ←val_inj]; intro h
    apply_fun (fun x ↦ x d) at h
    simpa using h
  intro h; simp [h]

@[simp]
theorem Scalar.toFormal_cast {d d': Dimensions} (q:Scalar d) (h:d' = d := by abel) :
  ((q.cast h):Formal) = (q:Formal) := by
  subst h
  simp_all only [cast, _root_.cast_eq]

instance Scalar.instZero {d:Dimensions} : Zero (Scalar d) where
  zero := ⟨ 0 ⟩

@[simp]
theorem Scalar.val_zero {d:Dimensions} : (0:Scalar d).val = 0 := rfl

theorem Scalar.neZero_iff {d:Dimensions} (q:Scalar d) : NeZero q ↔ q.val ≠ 0 := by simp [_root_.neZero_iff, ←val_inj]

@[simp, norm_cast]
theorem Scalar.toFormal_zero {d:Dimensions} : ((0:Scalar d):Formal) = 0 := by simp [toFormal]

instance Scalar.instAdd {d:Dimensions} : Add (Scalar d) where
  add q₁ q₂ := ⟨q₁.val + q₂.val⟩

@[simp]
theorem Scalar.val_add {d:Dimensions} (q₁ q₂:Scalar d) : (q₁ + q₂).val = q₁.val + q₂.val := rfl

@[simp,norm_cast]
theorem Scalar.toFormal_add {d:Dimensions} (q₁ q₂:Scalar d) : ((q₁ + q₂:Scalar d):Formal) = (q₁:Formal) + (q₂:Formal) := by
  simp [toFormal, MonoidAlgebra.single_add]

instance Scalar.instNeg {d:Dimensions} : Neg (Scalar d) where
  neg q := ⟨-q.val⟩

@[simp]
theorem Scalar.val_neg {d:Dimensions} (q:Scalar d) : (-q).val = -q.val := rfl

instance Scalar.instNeZero_neg {d:Dimensions} (q:Scalar d) [h:NeZero q] : NeZero (-q) := by
  rw [neZero_iff] at h ⊢
  simp [h]

@[simp,norm_cast]
theorem Scalar.toFormal_neg {d:Dimensions} (q:Scalar d) : ((-q:Scalar d):Formal) = -(q:Formal) := by
  simp [toFormal]

instance Scalar.instAddGroup {d:Dimensions} : AddGroup (Scalar d) :=
AddGroup.ofLeftAxioms
  (by intros; rw [←toFormal_inj]; push_cast; abel)
  (by intros; rw [←toFormal_inj]; push_cast; abel)
  (by intros; rw [←toFormal_inj]; push_cast; abel)

instance Scalar.instAddCommGroup {d:Dimensions} : AddCommGroup (Scalar d) where
  add_comm q₁ q₂ := by
    rw [←toFormal_inj]; push_cast; abel

@[coe]
def Scalar.ofReal (r:ℝ) : Scalar 0 := ⟨ r ⟩

instance Scalar.instCoeReal : Coe ℝ (Scalar 0) where
  coe := ofReal

@[simp]
theorem Scalar.coe_val (r:ℝ) : (r:Scalar 0).val = r := rfl

@[norm_cast,simp]
theorem Scalar.coe_zero : ((0:ℝ):Scalar 0) = 0 := by
  simp [ofReal]; rfl

theorem Scalar.neZero_coe_iff {r:ℝ} : NeZero (r:Scalar 0) ↔ r ≠ 0 := by
  simp [neZero_iff]

@[norm_cast,simp]
theorem Scalar.coe_add (r s:ℝ) : ((r+s:ℝ):Scalar 0) = (r:Scalar 0) + (s:Scalar 0) := by
  simp [ofReal]; rfl

@[norm_cast,simp]
theorem Scalar.coe_neg (r:ℝ) : ((-r:ℝ):Scalar 0) = -(r:Scalar 0) := by
  simp [ofReal]; rfl

@[norm_cast,simp]
theorem Scalar.coe_sub (r s:ℝ) : ((r-s:ℝ):Scalar 0) = (r:Scalar 0) - (s:Scalar 0) := by
  simp [ofReal]; rfl


noncomputable instance Formal.instCoeReal : Coe ℝ Formal where
  coe r := ((r:Scalar 0):Formal)

@[norm_cast,simp]
theorem Formal.coe_zero : ((0:ℝ):Formal) = 0 := by
  simp

@[norm_cast,simp]
theorem Formal.coe_one : ((1:ℝ):Formal) = 1 := by
  rfl

instance Scalar.instSMul {d:Dimensions} : SMul ℝ (Scalar d) where
  smul c q := ⟨c * q.val⟩

@[simp]
theorem Scalar.val_smul {d:Dimensions} (c:ℝ) (q:Scalar d) : (c • q).val = c * q.val := rfl

@[norm_cast,simp]
theorem Scalar.toFormal_smul {d:Dimensions} (c:ℝ) (q:Scalar d) : ((c • q:Scalar d):Formal) = (c:Formal) * (q:Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem Formal.smul_eq_mul (c:ℝ) (x:Formal) : c • x = (c:Formal) * x := by
  ext n
  simp [Scalar.toFormal]
  rw [Finsupp.smul_apply, AddMonoidAlgebra.single_zero_mul_apply, _root_.smul_eq_mul]

@[simp]
theorem Formal.smul_eq_mul' (c:ℕ) (x:Formal) : c • x = (c:Formal) * x := by
  simp [Scalar.toFormal]

@[simp]
theorem Formal.smul_eq_mul'' (c:ℤ) (x:Formal) : c • x = (c:Formal) * x := by
  simp [Scalar.toFormal]


@[norm_cast,simp]
theorem Scalar.coe_mul (r s:ℝ) : ((r*s:ℝ):Scalar 0) = r • (s:Scalar 0) := by
  ext; simp [ofReal]

instance Scalar.instModule {d:Dimensions} : Module ℝ (Scalar d) where
  smul_add c q₁ q₂ := by simp [←toFormal_inj]; ring
  add_smul c1 c2 q := by simp [←toFormal_inj]; ring
  one_smul q := by simp [←toFormal_inj]
  zero_smul q := by simp [←toFormal_inj]
  mul_smul c1 c2 q := by simp [←toFormal_inj]; ring
  smul_zero c := by simp [←toFormal_inj]

instance Scalar.instHMul {d₁ d₂:Dimensions} : HMul (Scalar d₁) (Scalar d₂) (Scalar (d₁ + d₂)) where
  hMul q₁ q₂ := ⟨q₁.val * q₂.val⟩

@[simp]
theorem Scalar.val_hMul {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  (q₁ * q₂).val = q₁.val * q₂.val := rfl

@[norm_cast,simp]
theorem Scalar.toFormal_hMul {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  ((q₁ * q₂:Scalar _):Formal) = (q₁:Formal) * (q₂:Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]

noncomputable def Scalar.pow {d:Dimensions} (q: Scalar d) (n:ℕ) : Scalar (n • d) := ⟨ q.val^n ⟩

/-- One cannot use the Mathlib classes `Pow` or `HPow` here because the output type `Scalar (n • d)` depends on the input `n`.  As the symbol `^` is reserved for such classes, we use the symbol `**` isntead.-/
infix:80 "**" => Scalar.pow

@[simp]
theorem Scalar.val_pow {d:Dimensions} (q:Scalar d) (n:ℕ) :
  (q ** n).val = q.val ^ n := rfl

@[norm_cast,simp]
theorem Scalar.toFormal_pow {d:Dimensions} (q:Scalar d) (n:ℕ) :
  ((q ** n):Formal) = (q:Formal) ^ n := by
  simp [toFormal, AddMonoidAlgebra.single_pow]

/-- We cannot use Mathlib's `Inv` class here or the associated `⁻¹` notation because `Inv` requires the output to be of the same type as the input. -/
noncomputable def Scalar.inv {d:Dimensions} (q:Scalar d) : Scalar (-d) := ⟨ q.val⁻¹ ⟩

@[simp]
theorem Scalar.val_inv {d:Dimensions} (q:Scalar d) :
  q.inv.val = q.val⁻¹ := rfl

instance Scalar.instNeg_inv {d:Dimensions} (q:Scalar d) [h: NeZero q] : NeZero q.inv := by
  rw [neZero_iff] at h ⊢
  simp [h]

@[simp]
theorem Scalar.mul_inv_self {d:Dimensions} (q:Scalar d) [h:NeZero q] : (q:Formal) * (q.inv:Formal) = 1 := by
  obtain ⟨ v ⟩ := q
  simp [neZero_iff] at h
  simp [inv, toFormal, AddMonoidAlgebra.single_mul_single,← Formal.coe_one]
  congr; field_simp

@[simp]
theorem Scalar.inv_mul_self {d:Dimensions} (q:Scalar d) [h:NeZero q] :  (q.inv:Formal) * (q:Formal) = 1 := by
  rw [mul_comm, mul_inv_self]

@[simp]
theorem Scalar.inv_coe (r:ℝ) :  ((r:Scalar 0).inv:Formal) = ((r⁻¹:ℝ):Scalar 0) := by
  rw [←toFormal_cast _ (show 0 = -0 by abel)]; congr
  symm; simp [←cast_eq]

@[simp]
theorem Scalar.mul_inv {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) : (q₁ * q₂).inv = ((q₁.inv) * (q₂.inv)).cast := by
  simp [←toFormal_inj, toFormal]; congr 1; ring

noncomputable instance Scalar.instHDiv {d₁ d₂:Dimensions} : HDiv (Scalar d₁) (Scalar d₂) (Scalar (d₁ - d₂)) where
  hDiv q₁ q₂ := ⟨q₁.val / q₂.val⟩

@[simp]
theorem Scalar.val_hDiv {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  (q₁ / q₂).val = q₁.val / q₂.val := rfl

@[norm_cast,simp]
theorem Scalar.toFormal_hDiv {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  ((q₁ / q₂:Scalar _):Formal) = (q₁:Formal) * (q₂.inv:Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]
  congr; abel

def StandardUnit (d:Dimensions) : Scalar d := ⟨ 1 ⟩

@[simp]
theorem StandardUnit.val_eq (d:Dimensions) : (StandardUnit d).val = 1 := rfl

instance StandardUnit.inst_NeZero (d:Dimensions) : NeZero (StandardUnit d) := by
  simp [Scalar.neZero_iff]

@[simp]
theorem StandardUnit.mul (d₁ d₂:Dimensions) : StandardUnit d₁ * StandardUnit d₂ = StandardUnit (d₁+d₂) := by
  simp [←Scalar.val_inj]

@[simp]
theorem StandardUnit.mul' (d₁ d₂:Dimensions) : (StandardUnit d₁:Formal) * (StandardUnit d₂:Formal) = StandardUnit (d₁+d₂) := by
  rw [←Scalar.toFormal_hMul, mul]

@[simp]
theorem StandardUnit.pow (d:Dimensions) (n:ℕ) : StandardUnit d ** n = StandardUnit (n • d) := by
  simp [←Scalar.val_inj]

@[simp]
theorem StandardUnit.pow' (d:Dimensions) (n:ℕ) : (StandardUnit d:Formal)^n = StandardUnit (n • d) := by
  rw [←Scalar.toFormal_pow, pow]

@[simp]
theorem StandardUnit.inv (d:Dimensions) : (StandardUnit d).inv = StandardUnit (-d) := by
  simp [←Scalar.val_inj]

@[simp]
theorem StandardUnit.div (d₁ d₂:Dimensions) : StandardUnit d₁ / StandardUnit d₂ = StandardUnit (d₁-d₂) := by
  simp [←Scalar.val_inj]

noncomputable def Scalar.in {d:Dimensions} (unit q:Scalar d) : ℝ := q.val / unit.val

@[simp]
theorem Scalar.val_in (d:Dimensions) (unit q:Scalar d) : unit.in q = q.val / unit.val := rfl

theorem Scalar.in_def {d:Dimensions} (unit q:Scalar d) [h: NeZero unit] : q = (unit.in q) • unit := by
  simp [neZero_iff] at h
  simp [←val_inj]
  field_simp

@[simp]
theorem Scalar.in_smul {d:Dimensions} (c:ℝ) (unit q:Scalar d) : unit.in (c • q) = c * unit.in q := by
  simp [←val_inj]; ring








end UnitsSystem
