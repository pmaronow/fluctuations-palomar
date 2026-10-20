module

public import SKBarriers2.Corner.FrozenRowsMixed26
public import SKBarriers2.Corner.FrozenRowsMixedSlotProfiles

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

def bellFineCoefficient (r : ℕ) : ℝ :=
  1+3*(2:ℝ)^(r+4)+((2:ℝ)^(r+4))^2

def bellCoarseCoefficient (r : ℕ) : ℝ :=
  1+3*(2:ℝ)^(r+3)+((2:ℝ)^(r+3))^2

private theorem epsilonBellTestsKJet_uniform_fine {r : ℕ} {m M : ℝ}
    {R : Fin 3 → Vec3 → MomentKJet} (hm : m ∈ Icc (0 : ℝ) 1) (hM : 0 ≤ M)
    (H : ∀ i : Fin 3, MomentKJet.SpatialBound (r+2) (M^(i.val+1)) (3*(i.val+1)) (R i)) :
    ∀ i : Fin 3, MomentKJet.SpatialBound (r+2)
      (bellFineCoefficient r*M^(i.val+1)) (3*(i.val+1))
      (fun y => epsilonBellTestsKJet m (fun j => R j y) i) := by
  have HB := epsilonBellTestsKJet_spatial hm H
  let S := (2:ℝ)^(r+4)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hD : 1 ≤ bellFineCoefficient r := by
    change 1 ≤ 1+3*S+S^2
    nlinarith [sq_nonneg S]
  have hD₂ : 1+S ≤ bellFineCoefficient r := by
    change 1+S ≤ 1+3*S+S^2
    nlinarith [sq_nonneg S]
  intro i
  fin_cases i
  · simpa [epsilonBellTestsKJet] using
      HB.1.mono (le_mul_of_one_le_left hM hD) le_rfl
  · simpa [epsilonBellTestsKJet,Nat.mul_comm] using
      HB.2.1.mono (mul_le_mul_of_nonneg_right hD₂ (sq_nonneg M)) le_rfl
  · simpa [bellFineCoefficient,S,epsilonBellTestsKJet,Nat.add_assoc] using HB.2.2

theorem FrozenRowsNaturalRealization.bell_intrinsicTestProfiles
    {β a s h z ε k M Mc W : ℝ} {α : ℝ → ℝ} {r : ℕ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (q : Fin 12) (u : ℝ → Vec3) (hm : a*frozenUnitMass q ∈ Icc (0 : ℝ) 1)
    (hM : 1 ≤ M) (hMc : 1 ≤ Mc) (hρ₁ : Real.sqrt h ≤ 1) (hW : 1 ≤ W)
    (hFine : ∀ v : Fin 3, MomentKJet.SpatialBound (r+2) (M^(v.val+1)) (3*(v.val+1))
      (fun y => MomentKJet.rescale (Real.sqrt h) (normalizedEpsilonKJet
        (fun κ => (frozenSchedule β a (1/2) h κ).drop (q.val+1))
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
        (Real.sqrt h) (fun _ => z) (fun _ => y) (v.val+1) ε k)))
    (hCoarse : ∀ v : Fin 3, MomentKJet.FirstDegreeBound (r+2)
      ((Mc/Real.sqrt h)^(v.val+1)) (2*(v.val+1)-1)
      (fun y => MomentKJet.rescale (Real.sqrt h) (normalizedEpsilonKJet
        (fun κ => (frozenSchedule β a (1/2) h κ).drop (q.val+1))
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
        (Real.sqrt h) (fun _ => z) (fun _ => y) (v.val+1) ε k))) (i : Fin 3) :
    IntrinsicTestProfiles r
      ((bellFineCoefficient r+bellCoarseCoefficient r*(max 1 Mc)^3)*M^(i.val+1))
      (3*(i.val+1)) ((Real.sqrt h)^3/W)
      (fun y => frozenRowsNaturalBellTest β α s h z ε q i
        (frozenRowsTranslatedParameterCurve β α a s h z ε q u k,y))
      (fun y => (Real.sqrt h/W)*deriv (fun κ => frozenRowsNaturalBellTest β α s h z ε q i
        (frozenRowsTranslatedParameterCurve β α a s h z ε q u κ,y)) k)
      (fun y => (Real.sqrt h/W)^2*deriv (deriv (fun κ => frozenRowsNaturalBellTest β α s h z ε q i
        (frozenRowsTranslatedParameterCurve β α a s h z ε q u κ,y))) k) := by
  let ρ := Real.sqrt h
  let R := fun v : Fin 3 => fun y : Vec3 => MomentKJet.rescale ρ (normalizedEpsilonKJet
    (fun κ => (frozenSchedule β a (1/2) h κ).drop (q.val+1))
    (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
    ρ (fun _ => z) (fun _ => y) (v.val+1) ε k)
  let J := fun y => MomentKJet.rescale ρ (parameterCurveKJet
    (frozenRowsNaturalBellTest β α s h z ε q i)
    (frozenRowsTranslatedParameterCurve β α a s h z ε q u) k y)
  have hρ : 0 < ρ := Real.sqrt_pos.mpr H.scale_pos
  have hJ : J = fun y => epsilonBellTestsKJet (a*frozenUnitMass q) (fun v => R v y) i := by
    funext y
    dsimp only [J]
    rw [frozenRowsTranslated_bellJet_eq]
    exact H.normalized_bellJet_eq hk q i y
  have HF : MomentKJet.SpatialBound (r+2) (bellFineCoefficient r*M^(i.val+1)) (3*(i.val+1)) J := by
    rw [hJ]
    exact epsilonBellTestsKJet_uniform_fine hm (zero_le_one.trans hM) hFine i
  have HC : MomentKJet.FirstDegreeBound (r+2)
      (bellCoarseCoefficient r*(Mc/ρ)^(i.val+1)) (2*(i.val+1)-1) J := by
    rw [hJ]
    exact epsilonBellTestsKJet_first_degree (div_nonneg (zero_le_one.trans hMc) hρ.le) hm hCoarse i
  have HS := MomentKJet.intrinsicTestProfiles_of_fine_coarse
    (show 1 ≤ i.val+1 by omega) (show i.val+1 ≤ 3 by omega)
    (show 0 ≤ bellFineCoefficient r by dsimp only [bellFineCoefficient]; positivity)
    (show 0 ≤ bellCoarseCoefficient r by dsimp only [bellCoarseCoefficient]; positivity)
    (zero_le_one.trans hMc) hM hρ hρ₁ hW HF HC
  convert HS using 1 <;> funext y <;>
    simp only [J,MomentKJet.rescale,parameterCurveKJet,div_pow] <;> ring

end SKBarriers2.Corner
