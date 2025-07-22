import Mathlib.Tactic
import Mathlib.Probability.Notation

open MeasureTheory ProbabilityTheory

structure MeasureTheory.Extension (X Y: Type*) [MeasureSpace X] [MeasureSpace Y] where
  π : X → Y
  extension : MeasurePreserving π

/-- An embedding, a.k.a. a bundled injective function. -/
infixr:25 " ↠ " => MeasureTheory.Extension

instance MeasureTheory.Extension.instFunLike {X Y:Type*} [MeasureSpace X] [MeasureSpace Y] : FunLike (X ↠ Y) X Y where
  coe := π
  coe_injective' f g h := by { cases f; cases g; congr }

theorem MeasureTheory.Extension.measure_preimage {X Y: Type*} [MeasureSpace X] [MeasureSpace Y] (f: X ↠ Y) {E:Set Y} (hE: MeasurableSet E) :ℙ (⇑f ⁻¹' E) = ℙ E := MeasureTheory.MeasurePreserving.measure_preimage f.extension (MeasurableSet.nullMeasurableSet hE)
