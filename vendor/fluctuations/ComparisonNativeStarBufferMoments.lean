module

public import ComparisonNativeStarBandScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
namespace NativeStarBuffer

def energyScale (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (r : Fin (steps.length+2) → ℝ) : ℝ :=
  (1+(2*(l:ℝ))^2/3)*(physicalWindowMass steps 0 J)⁻¹^2*
    (∫z,(physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j=>r j.castSucc) (fun j=>r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) z)^l
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)^((l:ℝ)⁻¹)

theorem centered_buffer_le_sqrt_actual_energy (n l : ℕ) (hl : 0<l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀j,physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc<r j.succ) :
    physicalBufferCenteredNorm n steps q0 (physicalWindowWeight steps 0 J) (2*l:ℕ) ≤
      Real.sqrt (energyScale n l steps q0 J r) := by
  apply Real.le_sqrt_of_sq_le
  have h := physical_window_centered_moment_energy n l hl steps ha q0 J r hr hc
  dsimp only at h
  simpa only [physicalBufferCenteredNorm,energyScale,Nat.cast_mul,Nat.cast_ofNat] using h

theorem exists_star_all_order_energy_bounds {n N : ℕ}
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (D : CutBlocks n steps N) (hN : 0<N)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hvariation : physicalPathSecondMoment n steps q0 (D.cut (4*N))-
      physicalPathSecondMoment n steps q0 (D.cut 0) ≤ (N:ℝ)*eta)
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hcell : ∀j:Fin (steps.length+1),pathMassDifferences steps 0 j ≠ 0 → r j.castSucc<r j.succ) :
    ∃i:ℕ,∃_hi:i<N,∃B:PhysicalStarBufferData n steps q0 (D.fork i) (D.central i)
      (physicalPathSecondMoment n steps q0 (D.fork i)),
      B.km=physicalWindowWeight steps 0 (D.pastRows i) ∧
      B.kp=physicalWindowWeight steps 0 (D.futureRows i) ∧ B.eta=eta ∧
      ∀l:ℕ,0<l → 
      let mu:=rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
      let S:=physicalPathSecondMoment n steps q0 (D.fork i)
      let Em:=Real.sqrt (energyScale n l steps q0 (D.pastRows i) r)
      let Ep:=Real.sqrt (energyScale n l steps q0 (D.futureRows i) r)
      (momentNorm mu (fun z=>‖actualSpinPath n steps id (D.fork i) z‖^2-S) (2*l:ℕ) ≤ 2*Em+2*Ep+eta) ∧
      (momentNorm mu (fun z=>‖actualSpinPath n steps id (D.central i) z‖^2-S) (2*l:ℕ) ≤ 2*Em+2*Ep+eta) ∧
      (momentNorm mu (fun z=>‖actualSpinPath n steps id (D.central i) z-
        actualSpinPath n steps id (D.fork i) z‖^2) (2*l:ℕ) ≤ 16*Em+8*Ep+8*eta) := by
  obtain ⟨i,hi,B,hkm,hkp,he,_,_⟩ := D.exists_star_buffer_data ha q0 hN heta hvariation
  refine ⟨i,hi,B,hkm,hkp,he,?_⟩
  intro l hl
  dsimp only
  have hcp (J : Finset (Fin (steps.length+1))) j
      (hj : physicalWindowCellMass steps 0 J j ≠ 0) : r j.castSucc<r j.succ := by
    apply hcell j
    intro hz
    simp [physicalWindowCellMass,hz] at hj
  have hm := centered_buffer_le_sqrt_actual_energy n l hl steps ha q0 (D.pastRows i) r hr (hcp _)
  have hp := centered_buffer_le_sqrt_actual_energy n l hl steps ha q0 (D.futureRows i) r hr (hcp _)
  rw [←hkm] at hm
  rw [←hkp] at hp
  have horder : (1:ℝ) ≤ (2*l:ℕ) := by exact_mod_cast (show 1 ≤ 2*l by omega)
  have hnf := physical_buffered_norm_concentration n steps ha q0 B.km B.kp B.nonnegm B.nonnegp
    B.normalizedm B.normalizedp B.forkBound B.forkPast B.forkFuture horder B.etaNonneg B.meanPast B.meanFuture
  have hnt := physical_buffered_norm_concentration n steps ha q0 B.km B.kp B.nonnegm B.nonnegp
    B.normalizedm B.normalizedp B.centralBound B.centralPast B.centralFuture horder B.etaNonneg B.meanPast B.meanFuture
  dsimp only at hnf hnt
  change _ ≤ 2*physicalBufferCenteredNorm n steps q0 B.km (2*l:ℕ)+
    2*physicalBufferCenteredNorm n steps q0 B.kp (2*l:ℕ)+B.eta at hnf hnt
  rw [he] at hnf hnt
  have hmov := physical_central_movement_moment n steps ha q0 B.km B.nonnegm B.normalizedm
    B.centralBound B.forkBound B.centralPast B.forkPast horder B.etaNonneg B.meanPast
  dsimp only at hmov
  change _ ≤ 2*momentNorm _ (fun z=>‖actualSpinPath n steps id (D.central i) z‖^2-
      physicalPathSecondMoment n steps q0 (D.fork i)) (2*l:ℕ)+
    2*momentNorm _ (fun z=>‖actualSpinPath n steps id (D.fork i) z‖^2-
      physicalPathSecondMoment n steps q0 (D.fork i)) (2*l:ℕ)+
    8*physicalBufferCenteredNorm n steps q0 B.km (2*l:ℕ)+4*B.eta at hmov
  rw [he] at hmov
  refine ⟨by linarith,by linarith,by linarith⟩

end NativeStarBuffer
end OAI.SKFluctuations
