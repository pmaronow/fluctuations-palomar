module

public import ComparisonSignedCavityCompletedScalarExact
public import SKFluctuationsOAI.Probability.SKFluctuations.CavityFrozenJet

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy

def nativeSiteSpinPerm {n : ℕ} (π : Fin n≃Fin n) : Spin n≃Spin n where
  toFun σ:=fun i=>σ (π.symm i)
  invFun σ:=fun i=>σ (π i)
  left_inv σ:=by funext i;simp
  right_inv σ:=by funext i;simp

def nativeSiteEdgeMap {n : ℕ} (π : Fin n≃Fin n) (e : Edge n) : Edge n :=
  if h : π e.val.1<π e.val.2 then ⟨(π e.val.1,π e.val.2),h⟩
  else ⟨(π e.val.2,π e.val.1),lt_of_le_of_ne (le_of_not_gt h)
    (fun H=>e.property.ne (π.injective H.symm))⟩

theorem nativeSiteEdgeMap_inverse {n : ℕ} (π : Fin n≃Fin n) (e : Edge n) :
    nativeSiteEdgeMap π.symm (nativeSiteEdgeMap π e)=e := by
  apply Subtype.ext
  by_cases h : π e.val.1<π e.val.2
  · simp [nativeSiteEdgeMap,h,e.property]
  · simp [nativeSiteEdgeMap,h,not_lt.mpr e.property.le]

def nativeSiteEdgePerm {n : ℕ} (π : Fin n≃Fin n) : Edge n≃Edge n where
  toFun:=nativeSiteEdgeMap π
  invFun:=nativeSiteEdgeMap π.symm
  left_inv:=nativeSiteEdgeMap_inverse π
  right_inv:=nativeSiteEdgeMap_inverse π.symm

def nativeSiteFeaturePerm {n : ℕ} (π : Fin n≃Fin n) : FeatureIndex n≃FeatureIndex n :=
  Equiv.sumCongr π (Equiv.optionCongr (nativeSiteEdgePerm π))

theorem featureCoefficient_nativeSitePerm {n : ℕ} (π : Fin n≃Fin n)
    (σ : Spin n) (i : FeatureIndex n) :
    featureCoefficient n (nativeSiteSpinPerm π σ) (nativeSiteFeaturePerm π i)=
      featureCoefficient n σ i := by
  rcases i with i|(_|e)
  · simp [nativeSiteFeaturePerm,nativeSiteSpinPerm,featureCoefficient]
  · rfl
  · by_cases h : π e.val.1<π e.val.2
    · simp [nativeSiteFeaturePerm,nativeSiteSpinPerm,nativeSiteEdgePerm,nativeSiteEdgeMap,
        featureCoefficient,liftedCoefficients,h]
    · simp only [nativeSiteFeaturePerm,Equiv.sumCongr_apply,Sum.map_inr,Equiv.optionCongr_apply,
        Option.map_some,featureCoefficient,liftedCoefficients,nativeSiteEdgePerm,
        Equiv.coe_fn_mk,nativeSiteEdgeMap,dite_eq_right h,nativeSiteSpinPerm,Equiv.symm_apply_apply]
      ring

theorem finiteFeature_nativeSitePerm {n : ℕ} (π : Fin n≃Fin n)
    (σ : Spin n) (x : FeatureIndex n→ℝ) :
    finiteFeature n (nativeSiteSpinPerm π σ) (coordinateEquiv (nativeSiteFeaturePerm π) x)=
      finiteFeature n σ x := by
  simp only [finiteFeature_apply]
  rw [←(nativeSiteFeaturePerm π).sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [featureCoefficient_nativeSitePerm,coordinateEquiv_apply,Equiv.symm_apply_apply]

theorem nativeSiteFeaturePerm_physicalClock {n : ℕ} (π : Fin n≃Fin n)
    (b h : ℕ→ℝ) (j : ℕ) (i : FeatureIndex n) :
    Cavity.physicalCompletedClock n b h j (nativeSiteFeaturePerm π i)=
      Cavity.physicalCompletedClock n b h j i := by
  cases i <;> rfl

theorem nativeSiteFeaturePerm_completedPathClock {n : ℕ} (π : Fin n≃Fin n)
    (b h : ℝ→ℝ≥0) (u : ℝ) (i : FeatureIndex n) :
    completedPathClock n b h u (nativeSiteFeaturePerm π i)=completedPathClock n b h u i := by
  cases i <;> rfl

theorem nativeSiteFeaturePerm_gaussian {n : ℕ} (π : Fin n≃Fin n)
    (q : FeatureIndex n→ℝ≥0) (hq : ∀i,q (nativeSiteFeaturePerm π i)=q i) :
    MeasurePreserving (coordinateEquiv (nativeSiteFeaturePerm π))
      (Measure.pi fun i=>gaussianReal 0 (q i)) (Measure.pi fun i=>gaussianReal 0 (q i)) := by
  simpa only [hq] using coordinateEquiv_measPres (nativeSiteFeaturePerm π) q

end OAI.SKFluctuations
