module

public import ComparisonShiftedNativeBandCarrier
public import ContactDerivativeMeasure
public import RadiusCellEnergySupport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 10000000
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem radius_density_zero_outside (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) {r : ℝ} (hr : r∉Icc m.rmin 1) :
    m.radiusDensity dphys e as ho r=0 := by
  have hzero (us : List PositiveMass) (u : ℝ) (C : ℕ→ℝ) :
      radiusCellEnergyDensity m.R u us C r=0 := by
    induction us generalizing u C with
    | nil => rfl
    | cons v us ih =>
      have hnot : r∉Ioc (m.R u) (m.R v.val) := by
        intro h
        exact hr ⟨(m.R_bounds u).1.trans h.1.le,h.2.trans (m.R_bounds v.val).2⟩
      simp only [radiusCellEnergyDensity,indicator_of_notMem hnot,ih v.val _,zero_add]
  exact hzero as 0 _

theorem radius_measure_le_compact_volume (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    m.radiusMeasure dphys e as ho≤volume.restrict (Icc m.rmin 1) := by
  rw [←withDensity_indicator_one measurableSet_Icc]
  unfold radiusMeasure
  apply withDensity_mono
  apply ae_of_all
  intro r
  by_cases hr : r∈Icc m.rmin 1
  · rw [indicator_of_mem hr]
    change ENNReal.ofReal (m.radiusDensity dphys e as ho r) ≤ 1
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (m.radiusDensity_bounds dphys e as ho r).2
  · rw [indicator_of_notMem hr]
    change ENNReal.ofReal (m.radiusDensity dphys e as ho r) ≤ 0
    rw [m.radius_density_zero_outside dphys e as ho hr,ENNReal.ofReal_zero]

instance radiusMeasure_isFinite (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    IsFiniteMeasure (m.radiusMeasure dphys e as ho) :=
  isFiniteMeasure_of_le (volume.restrict (Icc m.rmin 1))
    (m.radius_measure_le_compact_volume dphys e as ho)

def radiusFiniteMeasure (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) : FiniteMeasure ℝ :=
  ⟨m.radiusMeasure dphys e as ho,inferInstance⟩

theorem radius_trace_boundedWeight_of_interval_budgets
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    {a z F : ℝ} (ha : m.rmin≤a) (haz : a≤z) (hz : z≤1) (hF : 0<F)
    (S : ℝ→ℝ) (hSm : MonotoneOn S (Icc a z))
    (hAC : AbsolutelyContinuousOnInterval S a z)
    (error : ℝ→ℝ→ℕ→ℝ≥0∞)
    (herr : ∀p q : ℝ,a≤p → p<q → q≤z → Tendsto (error p q) atTop (𝓝 0))
    (hinterval : ∀p q : ℝ,a≤p → p<q → q≤z → ∀ᶠj : ℕ in atTop,
      m.radiusMeasure dphys e (as j) (ho j) (Ioo p q)≤
        ENNReal.ofReal ((S q-S p)/F)+error p q j)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo a z)
    (weight : ℝ→ℝ) (hwm : AEStronglyMeasurable weight volume) (K : ℝ)
    (hwb : ∀r∈A,‖weight r‖≤K) (hw0 : ∀r∈A,0≤weight r)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠj : ℕ in atTop,
      (∫r in A,weight r∂m.radiusMeasure dphys e (as j) (ho j))≤
        (∫r in A,weight r*deriv S r)/F+epsilon := by
  let mus:=fun j=>m.radiusFiniteMeasure dphys e (as j) (ho j)
  let rho:=volume.restrict (Icc m.rmin 1)
  let nu:=contactDerivativeMeasure S a z F
  letI : IsFiniteMeasure nu:=contactDerivativeMeasure_isFinite haz hSm hAC hF
  letI : nu.OuterRegular:=inferInstance
  have hsub : A⊆Icc m.rmin 1 := hAD.trans (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha hz))
  have hiS : IntegrableOn (deriv S) A:=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le haz).mp hAC.intervalIntegrable_deriv).mono_set
      (hAD.trans Ioo_subset_Icc_self)
  have hbound : ∀ᵐr∂volume.restrict A,‖weight r‖≤K := by
    filter_upwards [ae_restrict_mem hA] with r hr
    exact hwb r hr
  have hAfin : volume A≠⊤ := ne_top_of_le_ne_top (by simp : volume (Icc m.rmin 1)≠⊤)
    (measure_mono hsub)
  have hiOne : IntegrableOn (fun _ : ℝ=>(1:ℝ)) A:=integrableOn_const hAfin
  have hiW : IntegrableOn weight A := by
    simpa only [IntegrableOn,mul_one] using hiOne.bdd_mul hwm.restrict hbound
  have hiProd : IntegrableOn (fun r=>weight r*deriv S r) A:=hiS.bdd_mul hwm.restrict hbound
  have hiRho : IntegrableOn weight A rho:=by
    change Integrable _ ((volume.restrict (Icc m.rmin 1)).restrict A)
    rw [Measure.restrict_restrict_of_subset hsub]
    exact hiW
  have hiNu : IntegrableOn weight A nu:=contactDerivativeMeasure_weight_integrable hSm hF hA
    (hAD.trans Ioo_subset_Icc_self) hiProd
  have hbudget (p q : ℝ) (hap : a≤p) (hpq : p<q) (hqz : q≤z) :
      ∀ᶠj : ℕ in atTop,(mus j:Measure ℝ) (Ioo p q)≤nu (Ioo p q)+error p q j := by
    rw [contactDerivativeMeasure_interval haz hSm hAC hF hap hpq.le hqz]
    exact hinterval p q hap hpq hqz
  have hfinal:=finite_contact_trace_budget_eventually mus rho (K:=Icc m.rmin 1) isCompact_Icc
    (by simp [rho]) (fun j=>m.radius_measure_le_compact_volume dphys e (as j) (ho j))
    nu error herr hbudget weight hA hAD hiRho hiNu hw0 hepsilon
  rw [contactDerivativeMeasure_weight_integral hSm hF hA (hAD.trans Ioo_subset_Icc_self)] at hfinal
  exact hfinal

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
