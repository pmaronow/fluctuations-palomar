module

public import ComparisonSignedCavityActualCalibratedBand
public import ComparisonNativeStarPolynomialSelection

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 4000000

theorem calibrated_mass_node_mem {N j : ℕ} {a L W quarter : ℝ}
    (hq : 0 ≤ quarter) (hj : j ≤ 4*N)
    (htotal : 4*(N:ℝ)*quarter=4*L*W) :
    massNode (a*W) quarter j ∈ Icc (a*W) ((a+4*L)*W) := by
  have hjr : (j:ℝ) ≤ 4*(N:ℝ) := by exact_mod_cast hj
  have hhi := mul_le_mul_of_nonneg_right hjr hq
  have hlo : 0 ≤ (j:ℝ)*quarter := mul_nonneg (Nat.cast_nonneg j) hq
  unfold massNode
  constructor <;> nlinarith only [hhi,hlo,htotal]

theorem calibrated_mass_central_length (start quarter : ℝ) (i : ℕ) :
    massNode start quarter (4*i+3)-massNode start quarter (4*i+1)=2*quarter := by
  unfold massNode
  push_cast
  ring

theorem calibrated_mass_block_subset {N i : ℕ} {a L W quarter : ℝ}
    (hq : 0 ≤ quarter) (hi : i < N)
    (htotal : 4*(N:ℝ)*quarter=4*L*W) :
    Icc (massNode (a*W) quarter (4*i)) (massNode (a*W) quarter (4*(i+1))) ⊆
      Icc (a*W) ((a+4*L)*W) := by
  intro u hu
  exact ⟨(calibrated_mass_node_mem hq (show 4*i ≤ 4*N by omega) htotal).1.trans hu.1,
    hu.2.trans (calibrated_mass_node_mem hq (show 4*(i+1) ≤ 4*N by omega) htotal).2⟩

theorem calibrated_mass_central_subset {i : ℕ} {start quarter : ℝ}
    (_hq : 0 ≤ quarter) :
    Ioo (massNode start quarter (4*i+1)) (massNode start quarter (4*i+3)) ⊆
      Icc (massNode start quarter (4*i)) (massNode start quarter (4*(i+1))) := by
  intro u hu
  unfold massNode at *
  push_cast at *
  constructor <;> nlinarith only [hu.1,hu.2,_hq]

theorem calibrated_mass_middle_length (start quarter : ℝ) (i : ℕ) :
    (massNode start quarter (4*i+3)-quarter/2)-
      (massNode start quarter (4*i+1)+quarter/2)=quarter := by
  have H := calibrated_mass_central_length start quarter i
  linarith only [H]

theorem calibrated_mass_middle_subset {i : ℕ} {start quarter : ℝ}
    (hq : 0 ≤ quarter) :
    Ioo (massNode start quarter (4*i+1)+quarter/2)
      (massNode start quarter (4*i+3)-quarter/2) ⊆
      Ioo (massNode start quarter (4*i+1)) (massNode start quarter (4*i+3)) := by
  intro u hu
  constructor <;> linarith only [hu.1,hu.2,hq]

end OAI.SKFluctuations.LaplaceWindowFormalization
