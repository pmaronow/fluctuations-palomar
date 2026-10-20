module

public import SKFluctuationsOAI.Probability.SKFluctuations.InverseConstraintNonempty

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
local instance (n : ℕ) : DecidableEq (OrderedFeatureIndex n) := fun _ _=>Classical.propDecidable _

theorem orderedPathPair_clock_congr (n : ℕ) (hn : 0<n)
    (b h b' h' : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    (he : ∀ u∈Icc (0:ℝ) 1,b u=b' u ∧ h u=h' u)
    (P : Spin n → Spin n → ℝ) {u : ℝ} (hu : u∈Ioc (0:ℝ) 1) :
    orderedPathPair n b h P u=orderedPathPair n b' h' P u := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let K : ℝ := ∑ σ,∑ τ,|P σ τ|
  have hK : 0≤K := Finset.sum_nonneg fun σ _=>Finset.sum_nonneg fun τ _=>abs_nonneg _
  have hP : ∀ σ τ,|P σ τ|≤K := by
    intro σ τ
    exact (Finset.single_le_sum (fun ρ _=>abs_nonneg (P σ ρ)) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (fun ρ _=>Finset.sum_nonneg fun η _=>abs_nonneg (P ρ η)) (Finset.mem_univ σ))
  have hφ (σ : Spin n) (i : OrderedFeatureIndex n) :
      |orderedFeature n σ (Pi.single i 1)|≤orderedAmplitude n i := by
    simpa [orderedFeature_apply,Pi.single_apply] using (orderedFeature_abs n σ i).le
  have hc : ∀ v∈Icc (0:ℝ) 1,∀ i,
      |(orderedPathClock n b h v i:ℝ)-(orderedPathClock n b' h' v i:ℝ)|≤(0:ℝ) := by
    intro v hv i
    rcases he v hv with ⟨hbv,hhv⟩
    cases i <;> simp only [orderedPathClock,Sum.elim_inl,Sum.elim_inr,hbv,hhv,sub_self,abs_zero,le_refl]
  have hp := pathPairMoment_sup_comparison (uniformWeight_pos n) (orderedFeature n)
    (orderedAmplitude n) (fun _=>0) (orderedAmplitude_nonneg n) hφ
    (orderedPathClock n b h) (orderedPathClock n b' h')
    (orderedPathClock_monotone n hb hh) (orderedPathClock_monotone n hb' hh') hc hu P hK hP
  change |orderedPathPair n b h P u-orderedPathPair n b' h' P u|≤_ at hp
  have hz : |orderedPathPair n b h P u-orderedPathPair n b' h' P u|≤0 := by simpa using hp
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

end OAI.SKFluctuations.LaplaceWindowFormalization
