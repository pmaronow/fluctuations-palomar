module

public import SKBarriers2.Corner.FrozenRowsNoise2
public import SKBarriers2.Corner.FrozenRowsMoments4

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set Filter OAI.SK.Analytic
namespace SKBarriers2.Corner
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "X" => (Fin 3 → ℝ)
def parameterCurveKJet (F : P × X → ℝ) (p : ℝ → P) (k : ℝ) (x : X) : MomentKJet :=
  ⟨F (p k,x), deriv (fun t => F (p t,x)) k,
    deriv (deriv (fun t => F (p t,x))) k⟩

theorem parameterCurveKJet_differentiates {F : P × X → ℝ} (hF : ParamSmooth F)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (x : X) :
    MomentKJet.Differentiates (fun t => parameterCurveKJet F p t x) k := by
  have H : ContDiffAt ℝ 2 (fun t => F (p t,x)) k :=
    hF.1.contDiffAt.comp k (hp.prodMk contDiffAt_const)
  exact ⟨(H.differentiableAt (by norm_num)).hasDerivAt,
    ((H.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt⟩

end SKBarriers2.Corner
