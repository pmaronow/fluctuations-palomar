module

public import SKBarriers2.Corner.FrozenRowsPotential3
public import SKBarriers2.Corner.FrozenRowsPotential

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner

namespace QuadraticTerminal

def translate (Q : QuadraticTerminal) (b : Vec3) : QuadraticTerminal where
  constant := Q.value b
  linear := fun i => Q.linear i + ∑ j, Q.hessian i j * b j
  hessian := Q.hessian
  symmetric := Q.symmetric

theorem eq_of_coefficients {Q R : QuadraticTerminal}
    (hc : Q.constant = R.constant) (hl : ∀ i, Q.linear i = R.linear i)
    (hh : ∀ i j, Q.hessian i j = R.hessian i j) : Q = R := by
  cases Q
  cases R
  simp only [mk.injEq]
  exact ⟨hc, funext hl, funext (fun i => funext (hh i))⟩

theorem translate_value (Q : QuadraticTerminal) (b x : Vec3) :
    (Q.translate b).value x = Q.value (x + b) := by
  simp [translate, value, Pi.add_apply, Fin.sum_univ_succ]
  rw [Q.symmetric 1 0, Q.symmetric 2 0, Q.symmetric 2 1]
  ring

@[simp] theorem translate_precision (Q : QuadraticTerminal) (b : Vec3)
    (m : ℝ) (v : Vec3) : (Q.translate b).precision m v = Q.precision m v := rfl

theorem translate_linearDirection (Q : QuadraticTerminal) (b v : Vec3) :
    (Q.translate b).linearDirection v = Q.slope v b := by
  simp [translate, linearDirection, slope, hessianDirection, Fin.sum_univ_succ]
  rw [Q.symmetric 1 0, Q.symmetric 2 0, Q.symmetric 2 1]
  ring

theorem translate_update (Q : QuadraticTerminal) (b : Vec3) (m : ℝ) (v : Vec3) :
    (Q.translate b).update m v = (Q.update m v).translate b := by
  apply eq_of_coefficients
  · change Q.value b - Real.log (Q.precision m v) / (2 * m) +
        m * (Q.translate b).linearDirection v ^ 2 / (2 * Q.precision m v) =
      (Q.update m v).value b
    rw [translate_linearDirection, update_value]
  · intro i
    change Q.linear i + (∑ j, Q.hessian i j * b j) +
        m / Q.precision m v * (Q.translate b).linearDirection v * Q.hessianDirection v i = _
    rw [translate_linearDirection]
    simp only [translate, update, slope, hessianDirection, Fin.sum_univ_succ]
    ring
  · intro i j
    rfl

def addConstant (Q : QuadraticTerminal) (c : ℝ) : QuadraticTerminal where
  constant := Q.constant + c
  linear := Q.linear
  hessian := Q.hessian
  symmetric := Q.symmetric

theorem addConstant_value (Q : QuadraticTerminal) (c : ℝ) (x : Vec3) :
    (Q.addConstant c).value x = Q.value x + c := by
  simp only [addConstant, value]
  ring

theorem addConstant_update (Q : QuadraticTerminal) (c m : ℝ) (v : Vec3) :
    (Q.addConstant c).update m v = (Q.update m v).addConstant c := by
  apply eq_of_coefficients
  · change (Q.constant + c) - Real.log (Q.precision m v) / (2 * m) +
        m * Q.linearDirection v ^ 2 / (2 * Q.precision m v) =
      Q.constant - Real.log (Q.precision m v) / (2 * m) +
        m * Q.linearDirection v ^ 2 / (2 * Q.precision m v) + c
    ring
  · intro i; rfl
  · intro i j; rfl

end QuadraticTerminal

theorem riccatiRecursion_translate (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (b : Vec3) :
    riccatiRecursion l (Q.translate b) = (riccatiRecursion l Q).translate b := by
  induction l with
  | nil => rfl
  | cons u t ih => simp only [riccatiRecursion, ih, QuadraticTerminal.translate_update]

theorem riccatiRecursion_addConstant (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (c : ℝ) :
    riccatiRecursion l (Q.addConstant c) = (riccatiRecursion l Q).addConstant c := by
  induction l with
  | nil => rfl
  | cons u t ih => simp only [riccatiRecursion, ih, QuadraticTerminal.addConstant_update]

theorem quadraticMeanTransition_translate (Q : QuadraticTerminal) (b v x : Vec3) (m : ℝ) :
    quadraticMeanTransition Q m v (x + b) =
      quadraticMeanTransition (Q.translate b) m v x + b := by
  have hs : (Q.translate b).slope v x = Q.slope v (x + b) := by
    change (Q.translate b).linearDirection v + ∑ i, x i * Q.hessianDirection v i = _
    rw [QuadraticTerminal.translate_linearDirection]
    simp [QuadraticTerminal.slope, QuadraticTerminal.hessianDirection, Pi.add_apply,
      Fin.sum_univ_succ]
    ring
  simp only [quadraticMeanTransition, QuadraticTerminal.translate_precision, hs]
  module

theorem gaussianPathMean_translate (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (b x : Vec3) :
    gaussianPathMean l Q (x + b) = gaussianPathMean l (Q.translate b) x + b := by
  induction l generalizing x with
  | nil => rfl
  | cons u t ih =>
    simp only [gaussianPathMean, riccatiRecursion_translate,
      quadraticMeanTransition_translate, ih]

theorem gaussianPathMean_addConstant (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (c : ℝ) (x : Vec3) :
    gaussianPathMean l (Q.addConstant c) x = gaussianPathMean l Q x := by
  induction l generalizing x with
  | nil => rfl
  | cons u t ih =>
    simp only [gaussianPathMean, riccatiRecursion_addConstant]
    exact ih _

theorem gaussianPathLinear_translate (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (b v : Vec3) : gaussianPathLinear l (Q.translate b) v = gaussianPathLinear l Q v := by
  induction l generalizing v with
  | nil => rfl
  | cons u t ih => simp only [gaussianPathLinear, riccatiRecursion_translate, ih]; rfl

theorem gaussianPathLinear_addConstant (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (c : ℝ) (v : Vec3) :
    gaussianPathLinear l (Q.addConstant c) v = gaussianPathLinear l Q v := by
  induction l generalizing v with
  | nil => rfl
  | cons u t ih => simp only [gaussianPathLinear, riccatiRecursion_addConstant, ih]; rfl

theorem completedSquareSchedule_translate (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (b : Vec3) : completedSquareSchedule l (Q.translate b) = completedSquareSchedule l Q := by
  induction l with
  | nil => rfl
  | cons u t ih =>
    simp only [completedSquareSchedule, riccatiRecursion_translate,
      QuadraticTerminal.translate_precision, gaussianPathLinear_translate, ih]

theorem completedSquareSchedule_addConstant (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (c : ℝ) : completedSquareSchedule l (Q.addConstant c) = completedSquareSchedule l Q := by
  induction l with
  | nil => rfl
  | cons u t ih =>
    simp only [completedSquareSchedule, riccatiRecursion_addConstant,
      gaussianPathLinear_addConstant, ih]
    rfl

theorem separableTaylorQuadratic_scale_translate (c u χ z η : ℝ) :
    ((separableTaylorQuadratic c u χ z).scale η).translate (fun _ => z) =
      (separableTaylorQuadratic 0 (η * u) (η * χ) 0).addConstant (3 * η * c) := by
  apply QuadraticTerminal.eq_of_coefficients
  · simp [QuadraticTerminal.translate, QuadraticTerminal.scale,
      QuadraticTerminal.value, separableTaylorQuadratic, QuadraticTerminal.addConstant]
    ring
  · intro i
    simp only [QuadraticTerminal.translate, QuadraticTerminal.scale,
      separableTaylorQuadratic, QuadraticTerminal.addConstant, Fin.sum_univ_succ]
    fin_cases i <;> norm_num <;> ring
  · intro i j
    simp only [QuadraticTerminal.translate, QuadraticTerminal.scale,
      separableTaylorQuadratic, QuadraticTerminal.addConstant]
    split_ifs <;> ring

theorem vectorStep_translate_argument (m : ℝ) (v b x : Vec3) (f : Vec3 → ℝ) :
    vectorStep m v f (x + b) = vectorStep m v (fun y => f (y + b)) x := by
  have he (g : ℝ) : (x + b) + g • v = (x + g • v) + b := by module
  simp only [vectorStep, gaussianStep, positiveGaussianLogStep, he]

theorem vectorIncrementChain_translate_argument (l : List (ℝ × Vec3))
    (f : Vec3 → ℝ) (b x : Vec3) :
    vectorIncrementChain l f (x + b) =
      vectorIncrementChain l (fun y => f (y + b)) x := by
  induction l generalizing x with
  | nil => rfl
  | cons u t ih =>
    change vectorStep u.1 u.2 (vectorIncrementChain t f) (x + b) = _
    rw [vectorStep_translate_argument]
    have he : (fun y => vectorIncrementChain t f (y + b)) =
        vectorIncrementChain t (fun y => f (y + b)) := funext ih
    rw [he]
    rfl

theorem completedSquareExpression_center (l : List (ℝ × Vec3))
    (Q R : QuadraticTerminal) (b : Vec3) (C : ℝ)
    (hQR : Q.translate b = R.addConstant C) (f : Vec3 → ℝ) (x : Vec3) :
    (riccatiRecursion l Q).value (x + b) +
        vectorIncrementChain (completedSquareSchedule l Q) f
          (gaussianPathMean l Q (x + b)) =
      C + (riccatiRecursion l R).value x +
        vectorIncrementChain (completedSquareSchedule l R) (fun y => f (y + b))
          (gaussianPathMean l R x) := by
  have hval : (riccatiRecursion l Q).value (x + b) =
      (riccatiRecursion l R).value x + C := by
    rw [← QuadraticTerminal.translate_value, ← riccatiRecursion_translate,
      hQR, riccatiRecursion_addConstant, QuadraticTerminal.addConstant_value]
  have hmean : gaussianPathMean l Q (x + b) = gaussianPathMean l R x + b := by
    rw [gaussianPathMean_translate, hQR, gaussianPathMean_addConstant]
  have hsched : completedSquareSchedule l Q = completedSquareSchedule l R := by
    rw [← completedSquareSchedule_translate l Q b, hQR, completedSquareSchedule_addConstant]
  rw [hval, hmean, hsched, vectorIncrementChain_translate_argument]
  ring

end SKBarriers2.Corner
