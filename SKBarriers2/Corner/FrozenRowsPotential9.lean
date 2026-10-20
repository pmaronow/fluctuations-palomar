module

public import SKBarriers2.Corner.FrozenRowsPotential5
public import SKBarriers2.Corner.FrozenRowsPotential8
public import SKBarriers2.Corner.FrozenRowsGeometry

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner

def frozenGeometryMeanVector (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) : Vec3 :=
  fun i => frozenGeometryCoefficient β j ⟨3 + i.val, by omega⟩ p

def frozenGeometryLinearVector (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) : Vec3 :=
  fun i => frozenGeometryCoefficient β j ⟨6 + i.val, by omega⟩ p

def frozenGeometryPolynomial (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) (g : ℝ) : ℝ :=
  frozenGeometryCoefficient β j 0 p + frozenGeometryCoefficient β j 1 p * g +
    frozenGeometryCoefficient β j 2 p * g ^ 2

def frozenCenteredModelPotential (β a u χ ρ : ℝ) (f : Vec3 → ℝ)
    (j : Fin 12) (k g : ℝ) : ℝ :=
  let p : FrozenGeometryParameter := (((a, (u, χ)), ρ), k)
  let t := (frozenGeometryLabels j.val).map
    (fun q => (frozenGeometryMass q p, frozenGeometryDirection β q p))
  let Q := frozenGeometryQuadratic p
  let x := g • frozenGeometryDirection β j p
  (riccatiRecursion t Q).value x +
    vectorIncrementChain (completedSquareSchedule t Q) f (gaussianPathMean t Q x)

theorem frozenGeometryMeanVector_eq (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) :
    frozenGeometryMeanVector β j p =
      gaussianPathMean ((frozenGeometryLabels j.val).map
        (fun q => (frozenGeometryMass q p, frozenGeometryDirection β q p)))
        (frozenGeometryQuadratic p) 0 := by
  ext i
  fin_cases i <;> rfl

theorem frozenGeometryLinearVector_eq (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) :
    frozenGeometryLinearVector β j p =
      gaussianPathLinear ((frozenGeometryLabels j.val).map
        (fun q => (frozenGeometryMass q p, frozenGeometryDirection β q p)))
        (frozenGeometryQuadratic p) (frozenGeometryDirection β j p) := by
  ext i
  fin_cases i <;> rfl

theorem quadratic_value_smul_origin (Q : QuadraticTerminal) (v : Vec3) (g : ℝ) :
    Q.value (g • v) = Q.constant + Q.linearDirection v * g + Q.curvature v / 2 * g ^ 2 := by
  simpa [QuadraticTerminal.value, QuadraticTerminal.slope] using Q.value_shift v 0 g

theorem frozenCenteredModelPotential_eq_coefficients (β a u χ ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : Vec3 → ℝ) (j : Fin 12) (k g : ℝ) :
    frozenCenteredModelPotential β a u χ ρ f j k g =
      let p : FrozenGeometryParameter := (((a, (u, χ)), ρ), k)
      let n := 12 - (j.val + 1)
      frozenGeometryPolynomial β j p g +
        vectorIncrementChain
          (List.ofFn (fun i : Fin n =>
            let q : Fin 12 := ⟨j.val + 1 + i.val, by omega⟩
            (a * frozenUnitMass q, frozenCompletedDirection β a χ (ρ ^ 2) q k)))
          f (frozenGeometryMeanVector β j p + g • frozenGeometryLinearVector β j p) := by
  let p : FrozenGeometryParameter := (((a, (u, χ)), ρ), k)
  let t := (frozenGeometryLabels j.val).map
    (fun q => (frozenGeometryMass q p, frozenGeometryDirection β q p))
  let Q := frozenGeometryQuadratic p
  let v := frozenGeometryDirection β j p
  have hsqrt : Real.sqrt (ρ ^ 2) = ρ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hρ]
  have ht : t = (frozenSchedule β a (1 / 2) (ρ ^ 2) k).drop (j.val + 1) := by
    rw [frozenSchedule_eq_labelled β a (ρ ^ 2) k (sq_nonneg ρ), hsqrt, ← List.map_drop]
    rfl
  have hdir : completedSquareSchedule t Q =
      List.ofFn (fun i : Fin (12 - (j.val + 1)) =>
        let q : Fin 12 := ⟨j.val + 1 + i.val, by omega⟩
        (a * frozenUnitMass q, frozenCompletedDirection β a χ (ρ ^ 2) q k)) := by
    change completedSquareSchedule t (separableTaylorQuadratic 0 u χ 0) = _
    rw [ht, completedSquareSchedule_drop,
      completedSquareSchedule_frozen β a 0 u χ (ρ ^ 2) 0 k (sq_nonneg ρ), list_drop_ofFn]
  have hmean : gaussianPathMean t Q (g • v) =
      frozenGeometryMeanVector β j p + g • frozenGeometryLinearVector β j p := by
    rw [frozenGeometryMeanVector_eq, frozenGeometryLinearVector_eq]
    simpa only [zero_add] using gaussianPathMean_shift t Q 0 v g
  have hquad : (riccatiRecursion t Q).value (g • v) = frozenGeometryPolynomial β j p g := by
    exact quadratic_value_smul_origin (riccatiRecursion t Q) v g
  change (riccatiRecursion t Q).value (g • v) +
    vectorIncrementChain (completedSquareSchedule t Q) f (gaussianPathMean t Q (g • v)) = _
  rw [hquad, hdir, hmean]

theorem frozenRowsHead_direction_eq_unit (β a h k : ℝ) (hh : 0 ≤ h) (j : Fin 12) :
    (frozenRowsHead β a h j.val k).2 = Real.sqrt h • frozenUnitDirection β k j := by
  rw [frozenRowsHead, frozenSchedule_eq_labelled β a h k hh, ← List.ofFn_eq_map,
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt)]
  simp only [List.getElem_ofFn]

theorem centeredFrozenRowsPotential_eq_model (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (hh : 0 ≤ h) (j : Fin 12) (k g : ℝ) :
    centeredFrozenRowsPotential β α a s h z ε j.val k g =
      frozenCenteredModelPotential β a
        ((1 - ε) * jet β α 1 (s + 4 * h) z)
        ((1 - ε) * jet β α 2 (s + 4 * h) z) (Real.sqrt h)
        (centeredFrozenRowsTerminal β α s h z ε) j k g := by
  let p : FrozenGeometryParameter :=
    (((a, ((1 - ε) * jet β α 1 (s + 4 * h) z,
      (1 - ε) * jet β α 2 (s + 4 * h) z)), Real.sqrt h), k)
  have ht : (frozenGeometryLabels j.val).map
      (fun q => (frozenGeometryMass q p, frozenGeometryDirection β q p)) =
      (frozenSchedule β a (1 / 2) h k).drop (j.val + 1) := by
    rw [frozenSchedule_eq_labelled β a h k hh, ← List.map_drop]
    rfl
  dsimp only [centeredFrozenRowsPotential, frozenCenteredModelPotential]
  rw [frozenRowsHead_direction_eq_unit β a h k hh j, ht]
  rfl

theorem curve_derivatives_of_twoJets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℝ → E} {U : Set ℝ} (hU : IsOpen U)
    (H : ∀ k ∈ U, HasDerivAt f (f₁ k) k ∧ HasDerivAt f₁ (f₂ k) k)
    {k : ℝ} (hk : k ∈ U) : deriv f k = f₁ k ∧ deriv (deriv f) k = f₂ k := by
  have hnear : deriv f =ᶠ[𝓝 k] f₁ := by
    filter_upwards [hU.mem_nhds hk] with t ht
    exact (H t ht).1.deriv
  exact ⟨(H k hk).1.deriv, hnear.deriv_eq.trans (H k hk).2.deriv⟩

end SKBarriers2.Corner
