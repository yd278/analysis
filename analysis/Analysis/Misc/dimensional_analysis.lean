import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

@[ext]
structure Dimensions where
  units_length : ℤ
  units_mass : ℤ
  units_time : ℤ
deriving DecidableEq

instance Dimensions.instZero : Zero Dimensions where
  zero := ⟨0, 0, 0⟩

instance Dimensions.instAdd : Add Dimensions where
  add d1 d2 := ⟨d1.units_length + d2.units_length, d1.units_mass + d2.units_mass, d1.units_time + d2.units_time⟩

instance Dimensions.instNeg : Neg Dimensions where
  neg d := ⟨-d.units_length, -d.units_mass, -d.units_time⟩

instance Dimensions.instAddGroup : AddGroup Dimensions :=
AddGroup.ofLeftAxioms
  (by intros; simp_rw [HAdd.hAdd, Add.add]; simp [add_assoc])
  (by intros; simp_rw [HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]; simp)
  (by intros; simp_rw [Neg.neg, HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]; simp [Int.Linear.neg_fold])

instance Dimensions.instAddCommGroup : AddCommGroup Dimensions where
  add_comm d1 d2 := by
    simp_rw [HAdd.hAdd, Add.add]; simp [add_comm]

@[ext]
structure Quantity (d:Dimensions) where
  value : ℝ

#check Quantity.ext

/-- Sometimes one will need to compare `q:Quantity d` with `q':Quanitty d'` with `d'` propositionally
equal, but not definitionally equal, to `d`.  For this, one needs an additional `cast`. -/
theorem Quantity.cast_eq {d d':Dimensions} (h: d = d') (q: Quantity d) (q': Quantity d') (hqq': q.value = q'.value) :
  (cast (by rw [h]) q) = q' := by aesop

abbrev Length := Quantity ⟨1, 0, 0⟩
abbrev Mass := Quantity ⟨0, 1, 0⟩
abbrev Time := Quantity ⟨0, 0, 1⟩
abbrev Speed := Quantity ⟨1, 0, -1⟩


instance Quantity.instZero {d:Dimensions} : Zero (Quantity d) where
  zero := ⟨0⟩

@[simp]
theorem Quantity.value_zero {d:Dimensions} : (0:Quantity d).value = 0 := rfl

instance Quantity.instAdd {d:Dimensions} : Add (Quantity d) where
  add q1 q2 := ⟨q1.value + q2.value⟩

@[simp]
theorem Quantity.value_add {d:Dimensions} (q1 q2:Quantity d) : (q1 + q2).value = q1.value + q2.value := rfl

instance Quantity.instNeg {d:Dimensions} : Neg (Quantity d) where
  neg q := ⟨-q.value⟩

@[simp]
theorem Quantity.value_neg {d:Dimensions} (q:Quantity d) : (-q).value = -q.value := rfl

instance Quantity.instAddGroup {d:Dimensions} : AddGroup (Quantity d) :=
AddGroup.ofLeftAxioms
  (by intros; apply Quantity.ext; simp [add_assoc])
  (by intros; apply Quantity.ext; simp)
  (by intros; apply Quantity.ext; simp)

instance Quantity.instAddCommGroup {d:Dimensions} : AddCommGroup (Quantity d) where
  add_comm q1 q2 := by
    apply Quantity.ext; simp [add_comm]

instance Quantity.instSMul {d:Dimensions} : SMul ℝ (Quantity d) where
  smul c q := ⟨c * q.value⟩

@[simp]
theorem Quantity.value_smul {d:Dimensions} (c:ℝ) (q:Quantity d) : (c • q).value = c * q.value := rfl

instance Quantity.instModule {d:Dimensions} : Module ℝ (Quantity d) where
  smul_add c q1 q2 := by apply Quantity.ext; simp [mul_add]
  add_smul c1 c2 q := by apply Quantity.ext; simp [add_mul]
  one_smul q := by apply Quantity.ext; simp
  zero_smul q := by apply Quantity.ext; simp
  mul_smul c1 c2 q := by apply Quantity.ext; simp [mul_assoc]
  smul_zero c := by apply Quantity.ext; simp

instance Quantity.instHMul {d1 d2:Dimensions} : HMul (Quantity d1) (Quantity d2) (Quantity (d1 + d2)) where
  hMul q1 q2 := ⟨q1.value * q2.value⟩

@[simp]
theorem Quantity.value_hMul {d1 d2:Dimensions} (q1:Quantity d1) (q2:Quantity d2) :
  (q1 * q2).value = q1.value * q2.value := rfl

theorem Quantity.left_distrib {d₁ d₂:Dimensions} (a:Quantity d₁) (b c:Quantity d₂) :
  a * (b + c) = (a * b) + (a * c) := by
  apply Quantity.ext; simp [mul_add]

theorem Quantity.right_distrib {d₁ d₂:Dimensions} (a b:Quantity d₁) (c:Quantity d₂) :
  (a + b) * c = (a * c) + (b * c) := by
  apply Quantity.ext; simp [add_mul]

theorem Quantity.smul_hmul {d₁ d₂:Dimensions} (a:Quantity d₁) (b:Quantity d₂) (c:ℝ):
  c • (a * b) = (c • a) * b := by
  apply Quantity.ext; simp; ring

theorem Quantity.smul_hmul' {d₁ d₂:Dimensions} (a:Quantity d₁) (b:Quantity d₂) (c:ℝ):
  c • (a * b) = a * (c • b) := by
  apply Quantity.ext; simp; ring

@[simp]
theorem Quantity.zero_hmul {d₁ d₂:Dimensions} (b:Quantity d₂):
  (0: Quantity d₁) * b = 0 := by
  apply Quantity.ext; simp

@[simp]
theorem Quantity.hmul_zero {d₁ d₂:Dimensions} (a:Quantity d₁):
  a * (0: Quantity d₂) = 0 := by
  apply Quantity.ext; simp

theorem Quantity.hMul_comm {d₁ d₂:Dimensions} (a:Quantity d₁) (b:Quantity d₂):
  cast (by rw [add_comm]) (a * b) = b * a := by
  apply cast_eq (by abel)
  simp [mul_comm]

theorem Quantity.hMul_assoc {d₁ d₂ d₃:Dimensions} (a:Quantity d₁) (b:Quantity d₂) (c:Quantity d₃):
  cast (by rw [add_assoc]) (a * (b * c)) = (a * b) * c := by
  apply cast_eq (by abel)
  simp [mul_assoc]




example (l:Length) (t:Time) (v:Speed) : l = v * t:= by
  sorry
