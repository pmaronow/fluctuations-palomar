module

public import SKBarriers2.Corner.FrozenRowsMixed18
public import SKBarriers2.Corner.FrozenRowsMixed34
public import SKBarriers2.Corner.FrozenRowsMixedFrozenAverage
public import SKBarriers2.Corner.FrozenRowsMixedRecursion2

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

theorem epsilonLogCumulantsKJet_externalRow_spatial
    {r : ℕ} {ρ g M D m : ℝ} {A : Fin 3 → Vec3 → MomentKJet}
    (hm : m ∈ Icc (0 : ℝ) 1) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (HA : ∀ i : Fin 3,
      MomentKJet.SpatialBound r (D*M^(i.val+1)*(1+|g|)^(3*(i.val+1)))
        (3*(i.val+1)) (fun y => MomentKJet.rescale (ρ/(1+|g|)) (A i y))) :
    ∀ i : Fin 3, MomentKJet.SpatialBound r
      ((8*mixedCumulantBudget r D*M*(1+g^2)^3)^(i.val+1)) (3*(i.val+1))
      (fun y => MomentKJet.rescale ρ
        (epsilonLogCumulantsKJet m (fun i => A i y) i)) := by
  intro i
  let W := 1+|g|
  let C := mixedCumulantBudget r D
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hC : 0 ≤ C := le_trans (by norm_num) (mixedCumulantBudget_ge_one r hD)
  have hA (i : Fin 3) : MomentKJet.SpatialBound r
      (D*(M*W^3)^(i.val+1)) (3*(i.val+1))
      (fun y => MomentKJet.rescale (ρ/W) (A i y)) := by
    convert HA i using 1
    dsimp only [W]
    simp only [mul_pow,pow_mul]
    ring
  have H := epsilonLogCumulantsKJet_spatial hm (mul_nonneg hM (by positivity : 0 ≤ W^3)) hD hA i
  have he : (fun y => epsilonLogCumulantsKJet m
      (fun i => MomentKJet.rescale (ρ/W) (A i y)) i) =
      fun y => MomentKJet.rescale (ρ/W) (epsilonLogCumulantsKJet m (fun i => A i y) i) := by
    funext y
    rw [epsilonLogCumulantsKJet_rescale]
  rw [he] at H
  have H' : MomentKJet.SpatialBound r ((C*M*W^3)^(i.val+1)) (3*(i.val+1))
      (fun y => MomentKJet.rescale (ρ/W) (epsilonLogCumulantsKJet m (fun i => A i y) i)) := by
    convert H using 1
    dsimp only [C]
    ring
  exact H'.restore_external_row hC hM (by omega)

theorem frozenRowsMixedEnvelope_of_normalizedBellBounds
    {β a s h z ε M D m k : ℝ} {α : ℝ → ℝ} {j : ℕ}
    {A : ℝ → Fin 3 → Vec3 → MomentKJet}
    (hm : m ∈ Icc (0 : ℝ) 1) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hEq : ∀ g i y, frozenRowsNormalizedJet β α a s h z ε j i y k g =
      epsilonLogCumulantsKJet m (fun i => A g i y) i)
    (HA : ∀ g : ℝ, ∀ i : Fin 3,
      MomentKJet.SpatialBound (2*j) (D*M^(i.val+1)*(1+|g|)^(3*(i.val+1)))
        (3*(i.val+1))
        (fun y => MomentKJet.rescale (Real.sqrt h/(1+|g|)) (A g i y))) :
    FrozenRowsMixedEnvelope β α a s h z ε j (8*mixedCumulantBudget (2*j) D*M) k := by
  intro g i
  have H := epsilonLogCumulantsKJet_externalRow_spatial hm hM hD (HA g) i
  simpa only [MomentKJet.SpatialBound,hEq] using H

theorem scalarData_frozenRowsMixedStep {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) : FrozenRowsMixedStep D (Icc l u) := by
  classical
  obtain ⟨hS,M₀,hhS,hM₀,HS⟩ := scalarData_frozenRowsMixed_seed D hl hu
  obtain ⟨hB,E,hhB,hE,HB⟩ := scalarData_frozenRowsMovingAffineAverage_spatial D hl hu
  obtain ⟨hR,hhR,HR⟩ := scalarData_frozenRowsMovingBellKJet_realization D hl hu
  obtain ⟨hI,hhI,HI⟩ := scalarData_frozenRowsNormalizedJet_eq_cumulants D hl hu
  let T := 1+∑ j : Fin 11, 8*mixedCumulantBudget (2*j.val) E
  have hE₀ : 0 ≤ E := zero_le_one.trans hE
  have hterm (j : Fin 11) : 0 ≤ 8*mixedCumulantBudget (2*j.val) E :=
    mul_nonneg (by norm_num) (zero_le_one.trans (mixedCumulantBudget_ge_one _ hE₀))
  have hsum : 0 ≤ ∑ j : Fin 11, 8*mixedCumulantBudget (2*j.val) E :=
    Finset.sum_nonneg (fun j _ => hterm j)
  have hT : 1 ≤ T := by dsimp only [T]; linarith only [hsum]
  have hbudget (j : ℕ) (hj : j < 11) : 8*mixedCumulantBudget (2*j) E ≤ T := by
    have H := Finset.single_le_sum (f := fun q : Fin 11 => 8*mixedCumulantBudget (2*q.val) E)
      (fun q _ => hterm q) (Finset.mem_univ (⟨j,hj⟩ : Fin 11))
    exact H.trans (by dsimp only [T]; linarith only)
  let h₀ := min hS (min hB (min hR hI))
  refine ⟨h₀,M₀,T,lt_min hhS (lt_min hhB (lt_min hhR hhI)),hM₀,hT,?_⟩
  intro r hr h hh hhsmall z ε hε
  have hcaps : h ≤ hS ∧ h ≤ hB ∧ h ≤ hR ∧ h ≤ hI := by
    simpa only [h₀,le_min_iff] using hhsmall
  refine ⟨HS r hr h hh hcaps.1 z ε hε,?_⟩
  intro j hj M hM Hfine k hk
  let α := cdf (D.μ : MeasureTheory.Measure ℝ)
  let a := α (r-h)
  have hM₁ : 0 ≤ M := zero_le_one.trans hM
  have hm : frozenPartitionMass a (j+1) ∈ Icc (0 : ℝ) 1 := by
    have ha₀ : 0 ≤ a := cdf_nonneg _ _
    have ha₁ : a ≤ 1 := cdf_le_one _ _
    unfold frozenPartitionMass
    split_ifs <;> constructor <;> linarith only [ha₀,ha₁]
  have hEq (g : ℝ) (i : Fin 3) (y : Vec3) :
      frozenRowsNormalizedJet β α a (r-h) h z ε j i y k g =
        epsilonLogCumulantsKJet (frozenPartitionMass a (j+1))
          (fun v => frozenRowsMovingBellKJet β α a (r-h) h z ε j v y k g) i := by
    apply HI r hr h hh hcaps.2.2.2 z ε hε j hj y g
      (fun κ hκ v => (HR r hr h hh hcaps.2.2.1 z ε hε j hj g y κ hκ v).2) k hk i
  have HA (g : ℝ) (i : Fin 3) : MomentKJet.SpatialBound (2*j)
      (E*M^(i.val+1)*(1+|g|)^(3*(i.val+1))) (3*(i.val+1))
      (fun y => MomentKJet.rescale (Real.sqrt h/(1+|g|))
        (frozenRowsMovingBellKJet β α a (r-h) h z ε j i y k g)) := by
    have H := HB r hr h hh hcaps.2.1 z ε hε j hj M hM Hfine k hk g i
    have he (y : Vec3) := (HR r hr h hh hcaps.2.2.1 z ε hε j hj g y k hk i).1
    simpa only [MomentKJet.SpatialBound,α,a,he] using H
  have Hout := frozenRowsMixedEnvelope_of_normalizedBellBounds hm hM₁ hE₀ hEq HA
  exact Hout.mono
    (mul_nonneg (mul_nonneg (by norm_num)
      (zero_le_one.trans (mixedCumulantBudget_ge_one (2*j) hE₀))) hM₁)
    (mul_le_mul_of_nonneg_right (hbudget j hj) hM₁)

end SKBarriers2.Corner
