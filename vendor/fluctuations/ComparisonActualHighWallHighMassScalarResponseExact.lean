module

public import ComparisonActualHighWallStarClockDistinct
public import ComparisonScalarClosureIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Hierarchy

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem high_mass_scalar_response_exact
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Gamma : ℝ→ℝ) {u : ℝ} (hu : u∈Icc M.data.s 1) :
    let K := actualMixedClock (n+1) M.bf M.hf u
    let S := orderedPathS (n+1) M.bf M.hf u
    let R := M.data.wallRadius M.alpha u
    let e := M.data.g R
    comparisonRescaledScalarResponse Gamma M.data.T M.xs
      (K/(M.data.T*M.xs)) =
      (Gamma K-S)/M.xs^3+(e/M.data.T)*(S-R)/M.xs^3 := by
  let K := actualMixedClock (n+1) M.bf M.hf u
  let S := orderedPathS (n+1) M.bf M.hf u
  let R := M.data.wallRadius M.alpha u
  let e := M.data.g R
  have hK : K=M.data.T*S+e*(R-S) := by
    dsimp only [K,S,R,e]
    linarith only [M.high_mass_clock_compensation hu]
  have hTpos : 0 < M.data.T := M.data.hepsilon.1.trans M.data.hepsilon.2
  dsimp only [K,S,R,e] at hK ⊢
  have harg : M.data.T*M.xs*(K/(M.data.T*M.xs))=K := by
    field_simp [hTpos.ne',M.hxs.ne']
  dsimp only [K] at harg
  unfold comparisonRescaledScalarResponse
  rw [harg]
  field_simp [hTpos.ne',M.hxs.ne']
  nlinarith only [hK]

theorem high_mass_scalar_clock_radius_exact
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc M.data.s 1) :
    let K := actualMixedClock (n+1) M.bf M.hf u
    let S := orderedPathS (n+1) M.bf M.hf u
    let R := M.data.wallRadius M.alpha u
    let e := M.data.g R
    K/(M.data.T*M.xs)-R/M.xs=
      (S-R)/M.xs+(e/M.data.T)*(R-S)/M.xs := by
  let K := actualMixedClock (n+1) M.bf M.hf u
  let S := orderedPathS (n+1) M.bf M.hf u
  let R := M.data.wallRadius M.alpha u
  let e := M.data.g R
  have hK : K=M.data.T*S+e*(R-S) := by
    dsimp only [K,S,R,e]
    linarith only [M.high_mass_clock_compensation hu]
  have hTpos : 0 < M.data.T := M.data.hepsilon.1.trans M.data.hepsilon.2
  dsimp only [K,S,R,e] at hK ⊢
  field_simp [hTpos.ne',M.hxs.ne']
  nlinarith only [hK]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
