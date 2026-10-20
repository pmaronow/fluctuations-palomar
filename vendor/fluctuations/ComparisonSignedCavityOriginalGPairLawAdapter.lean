module

public import ComparisonSignedCavityOriginalProjectedLawAdapter

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

theorem native_actual_original_G_pair_half_eq_rest_add_restoration
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    (1/2:ℝ)*nativeActualOriginalGProjectedResampling T P₀.live.test.target star U K b C 0
      (cutFullVariance n q U 1 1 b h K) 0 (fun σ τ=>A σ.1 τ.1)
      (fun σ=>P (T.cavityAssignment σ).1)=
      nativeRetainedGProjectedDisplacement T P₀.live.test.target star U q b h K A P+
      nativeOriginalGProjectedDisplacementRestoration T P₀.live.test.target star U q b h K C A P := by
  have hfull : ∀i,Monotone (fun j=>cutFullVariance n q U 1 1 b h K j i) :=
    cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm
  have hzero : ∀i,(0 : FullCoordinate n→ℝ) i ≤ cutFullVariance n q U 1 1 b h K 0 i :=
    fun i=>cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0 i
  rw [←native_actual_generated_original_G_projected_row_polarization hP hi hs ho 0
    (cutFullVariance n q U 1 1 b h K) 0 K b C hfull hzero hK hKm
    (fun σ τ=>A σ.1 τ.1) (fun σ=>P (T.cavityAssignment σ).1)]
  exact native_original_G_projected_displacement_eq_retained_add_restoration n T ho
    P₀.live.test.target star U q b h K C hKC hP.highCut_le_length A P hq0 hq hb hh hK hbm hhm hKm

end OAI.SKFluctuations.Cavity
