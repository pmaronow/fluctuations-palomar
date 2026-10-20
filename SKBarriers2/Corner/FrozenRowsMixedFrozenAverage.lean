module

public import SKBarriers2.Corner.FrozenRowsMixedAverageRealization
public import SKBarriers2.Corner.FrozenRowsMixed28

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

theorem frozenRowsHead_mass_eq_partition (β a h k : ℝ) (hh : 0 ≤ h) (q : Fin 12) :
    (frozenRowsHead β a h q.val k).1 = frozenPartitionMass a q.val := by
  rw [frozenRowsHead_mass_eq β a h k hh q]
  fin_cases q <;> norm_num [frozenUnitMass,frozenPartitionMass] <;> ring

theorem scalarData_frozenRowsMovingBellKJet_realization {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j : ℕ, ∀ hj : j < 11, ∀ g : ℝ, ∀ y : Vec3,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r-h)
      let parent : Fin 12 := ⟨j,by omega⟩
      let q : Fin 12 := ⟨j+1,by omega⟩
      let p := frozenRowsMovingParameterCurve β α a (r-h) h z ε parent q g
      let A := fun i => affineCoordinateAverage (frozenRowsNaturalHead h z q)
        (frozenRowsNaturalPotential β α (r-h) h z ε (j+2))
        (frozenRowsNaturalBellTest β α (r-h) h z ε q i)
      ∀ k ∈ frozenRowsKDomain, ∀ i : Fin 3,
        frozenRowsMovingBellKJet β α a (r-h) h z ε j i y k g =
          parameterCurveKJet (A i) p k y ∧
        MomentKJet.Differentiates
          (fun κ => frozenRowsMovingBellKJet β α a (r-h) h z ε j i y κ g) k := by
  obtain ⟨hR,hhR,HR⟩ := scalarData_frozenRows_average_inputs D hl hu
  obtain ⟨hG,_,hhG,_,HG⟩ := scalarData_frozenRowsMovingTestEndpoint_geometry D hl hu
  refine ⟨min hR hG,lt_min hhR hhG,?_⟩
  intro r hr h hh hhsmall z ε hε j hj g y
  dsimp only
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r-h)
  let parent : Fin 12 := ⟨j,by omega⟩
  let q : Fin 12 := ⟨j+1,by omega⟩
  let p := frozenRowsMovingParameterCurve β α a (r-h) h z ε parent q g
  let A := fun i => affineCoordinateAverage (frozenRowsNaturalHead h z q)
    (frozenRowsNaturalPotential β α (r-h) h z ε (j+2))
    (frozenRowsNaturalBellTest β α (r-h) h z ε q i)
  let ρ := Real.sqrt h
  let c : Vec3 := fun _ => z
  let v := fun κ => (frozenRowsHead β a h (j+1) κ).2
  let u := fun κ => g • (frozenRowsHead β a h j κ).2
  let x := fun κ => ρ • (y+ρ⁻¹ • u κ)+c
  let F := fun κ e => epsilonChain ((frozenSchedule β a (1/2) h κ).drop (j+2))
    (terminalTaylorQuadratic β α (r-h) h z) (terminalResidual β α (r-h) h z) e
  have Hpack := HR r hr h hh (hhsmall.trans (min_le_left _ _)) z ε hε
  have H := Hpack.1
  have hρ : ρ ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have hx : x = fun κ => ρ • y+c+u κ := by
    funext κ
    dsimp only [x]
    rw [smul_add,smul_smul,mul_inv_cancel₀ hρ,one_smul]
    abel
  have he (i : Fin 3) (κ : ℝ) (hκ : κ ∈ frozenRowsKDomain) :
      normalizedMovingBellAverage ρ (frozenPartitionMass a (j+1)) v x F ε i κ = A i (p κ,y) := by
    obtain ⟨hD,L,hCont,hLip⟩ := Hpack.2 κ hκ q
    have HV := H.translated_average_eq hκ q i u y hD hCont hLip
    rw [frozenRowsHead_mass_eq_partition β a h κ hh.le q] at HV
    rw [hx]
    dsimp only [A,p]
    rw [frozenRowsMovingParameterCurve_eq_physical β α a (r-h) h z ε hh.le parent q g]
    exact HV
  intro k hk i
  have hp : ContDiffAt ℝ 2 p k :=
    ((HG r hr h hh (hhsmall.trans (min_le_right _ _)) z ε hε parent q k hk g).1).of_le (by simp)
  have hA : ParamSmooth (A i) :=
    smooth_affineCoordinateAverage (frozenRowsNaturalHead h z q)
      (H.potential_regular (j+2)) (H.bell_smooth q i)
  have Hjet := normalizedMovingBellKJet_eq_of_average_eq (A i) p y hk (he i)
  have Hdiff := normalizedMovingBellKJet_differentiates_of_paramSmooth_average hA hp y hk (he i)
  exact ⟨Hjet,Hdiff⟩

end SKBarriers2.Corner
