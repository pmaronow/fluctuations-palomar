module

public import ComparisonActualHighOnlyVirtualMovingPotentialAlong
public import ComparisonActualHighOnlyVirtualGapReferencesAlong
public import ComparisonActualHighOnlyBoundedGradientCore
public import ComparisonVirtualGapLimitExistenceEventually

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy ActualHighOnlyOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 18000000

theorem actual_compact_gap_mass_band_along_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs) atTop (𝓝 (V s)))
    {a b : ℝ} (hab : a < b)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (hmass : 0 < V ((a+b)/2)) {s t : ℝ} (hs : s∈Ioo a b) (ht : t∈Ioo a b) :
    ∀ᶠn in atTop,∀r∈Icc s t,
      (V ((a+b)/2)/2)*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*r) ∧
        (M n).alpha.val.val ((M n).xs*r) ≤ (V ((a+b)/2)+1)*(M n).xs := by
  have hsV := comparison_increment_support_gap_constant hV hgap s hs
    ((a+b)/2) (by constructor <;> linarith)
  have htV := comparison_increment_support_gap_constant hV hgap t ht
    ((a+b)/2) (by constructor <;> linarith)
  have hlo : V ((a+b)/2)/2 < V s := by rw [hsV];linarith
  have hup : V t < V ((a+b)/2)+1 := by rw [htV];linarith
  filter_upwards [(hCDF s).eventually (lt_mem_nhds hlo),
    (hCDF t).eventually (gt_mem_nhds hup)] with n hnlo hnup r hr
  refine ⟨?_,?_⟩
  · exact ((le_div_iff₀ (M n).hxs).mp hnlo.le).trans
      ((M n).alpha.val.property.2 (mul_le_mul_of_nonneg_left hr.1 (M n).hxs.le))
  · exact ((M n).alpha.val.property.2 (mul_le_mul_of_nonneg_left hr.2 (M n).hxs.le)).trans
      ((div_le_iff₀ (M n).hxs).mp hnup.le)

theorem actual_virtual_gap_primitive_of_gradient_limit_along_high_only
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (_hdelta : 0 < delta) (hcu : 0 ≤ cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs) atTop (𝓝 (V s)))
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport V) (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (hmass : 0 < V ((a+b)/2))
    (f : ℝ→ℝ) (hf : IntegrableOn f (Icc a b))
    (hgradient : ∃KG : ℝ,0 ≤ KG ∧ ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      (V ((a+b)/2)/2)*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) →
        |(M n).actualVirtualScaledGradient t| ≤ KG)
    (hGlim : ∀s∈Ioo a b,∀t∈Ioo a b,s ≤ t →
      Tendsto (fun n=>∫r in Icc s t,|(M n).actualVirtualScaledGradient r-f r|) atTop (𝓝 0)) :
    ∃K : ℝ,1 ≤ K ∧ ∃j : ℝ→ℝ,Monotone j ∧
      (∀t∈Icc a b,j t∈Icc (1/K^2) (K^2)) ∧
      Nonempty (ComparisonPinnedGapPrimitive a b (fun t=>j t*f t)) := by
  classical
  let c := V ((a+b)/2)/2
  have hc : 0 < c := half_pos hmass
  obtain ⟨n0,Hn0⟩:=eventually_atTop.mp (G.eventually_geometric_gates.mono fun n hn=>hn.2)
  let theta : ℕ→ℕ := fun n=>n+n0
  have hthetaStrict:StrictMono theta:=fun i j hij=>Nat.add_lt_add_right hij n0
  have htheta : Tendsto theta atTop atTop:=hthetaStrict.tendsto_atTop
  have hp n : Nonempty ((M (theta n)).Potential):=(M (theta n)).exists_potential_high_only
    (Hn0 (theta n) (by dsimp only [theta];omega))
  let p := fun n=>Classical.choice (hp n)
  obtain ⟨phi,hphi,left,right,hleft,hright,Hcontacts⟩ :=
    actual_virtual_gap_references_subsequence_along hC0 hroom (dim ∘ theta) (hdim.comp htheta)
      (fun n=>M (theta n)) (G.comp theta hthetaStrict) p (hxs.comp htheta) V hV
      (fun s=>(hCDF s).comp htheta) ha hab hbB hasupport hbsupport hgap hmass
  let psi := theta ∘ phi
  have hpsi : Tendsto psi atTop atTop := htheta.comp hphi.tendsto_atTop
  obtain ⟨KG,hKG,Hgradient⟩ := hgradient
  have Hgrad : ∀ᶠn in atTop,∀t∈Icc (left n) B,
      |(M (psi n)).actualVirtualScaledGradient t| ≤ KG := by
    filter_upwards [hpsi.eventually Hgradient] with n hn t ht
    have hncontact := Hcontacts n
    apply hn t ⟨hncontact.2.2.2.1.le.trans ht.1,ht.2⟩
    exact hncontact.2.2.2.2.2.2.2.1.trans ((M (psi n)).alpha.val.property.2
      (mul_le_mul_of_nonneg_left ht.1 (M (psi n)).hxs.le))
  obtain ⟨hK,errors,herrors0,herrors,Hdata⟩ := actual_virtual_moving_potential_data_along
    hcu hAz hC0 hroom (dim ∘ psi) (hdim.comp hpsi) (fun n=>M (psi n))
    (fun n=>p (phi n)) (hxs.comp hpsi) ha hab hbB hc hKG left hleft
    (Eventually.of_forall (fun n=>(Hcontacts n).2.2.2.1.le))
    (Eventually.of_forall (fun n=>(Hcontacts n).2.2.2.2.2.2.2.1))
    (Eventually.of_forall (fun n=>(Hcontacts n).2.2.2.2.2.1)) Hgrad
  let K := (c+cu*(B+Az)+1)/c
  let L : ℝ≥0 := (K^2*KG).toNNReal
  let H := fun n=>(p (phi n)).actualVirtualScaledPotential ((M (psi n)).xs*left n)
  let J := fun n=>(M (psi n)).actualVirtualMovingFactor ((M (psi n)).xs*left n)
  let G := fun n=>(M (psi n)).actualVirtualScaledGradient
  refine ⟨K,hK,?_⟩
  apply comparison_virtual_gap_limit_exists_of_eventual hab hbB hK left right errors H J G f
    hleft hright herrors hf
    (fun s hs t ht hst=>(hGlim s hs t ht hst).comp hpsi)
  filter_upwards [Hdata] with n hn
  obtain ⟨hleftb,hphysical,hzero,hLip,hJcont,hJmono,hJbound,hLower,hPrimitive⟩ := hn
  have hncontact := Hcontacts n
  refine ⟨hncontact.1,hncontact.2.1.trans hncontact.2.2.1.2,
    hncontact.2.2.1,hncontact.2.1,hzero,?_,hLip,hLower,?_,?_,hJcont.measurable,?_,?_⟩
  · dsimp only [H,Potential.actualVirtualScaledPotential]
    rw [hncontact.2.2.2.2.2.2.1,zero_div]
  · exact hJmono.mono (fun t ht=>ht.2)
  · intro t ht
    exact hJbound t ht.2
  · intro s hs t ht _hst
    exact (M (psi n)).actual_scaled_gradient_integrable (ha.trans_lt hs.1)
      ((mul_le_mul_of_nonneg_left (ht.2.le.trans hbB.le) (M (psi n)).hxs.le).trans hphysical)
  · intro s hs t ht hls hst
    exact hPrimitive s ⟨hls,hs.2.le.trans hbB.le⟩ t ⟨hls.trans hst,ht.2.le.trans hbB.le⟩ hst

end OAI.SKFluctuations.LaplaceWindowFormalization
