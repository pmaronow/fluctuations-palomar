module

public import ActualComparisonContact

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem potential_cap_density_on_interval
    {H α M : ℝ → ℝ} {a b : ℝ} (ha : 0≤a) (hb : b≤1)
    (hcap : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→deriv α r=M (α r))
    (hneg : ∀r∈Ioo a b,H r<0) :
    ∀ᵐ r,r∈Icc a b→deriv α r=M (α r) := by
  filter_upwards [hcap,volume.ae_ne a,volume.ae_ne b] with r hr hra hrb hri
  exact hr ⟨ha.trans hri.1,hri.2.trans hb⟩
    (hneg r ⟨lt_of_le_of_ne hri.1 hra.symm,lt_of_le_of_ne hri.2 hrb⟩)

theorem potential_comparison_cap_interval_travel
    {N δ U L E d : ℝ} (hN : 0<N) (hU : 0<U) (hL : 0<L)
    (hE : 0<E) (hd : 0<d) {H α : ℝ → ℝ} {C : ℝ≥0}
    (hα : LipschitzOnWith C α (Icc (0:ℝ) 1))
    (hm : StrictMonoOn α (Icc (0:ℝ) 1))
    (hαr : ∀r∈Icc (0:ℝ) 1,α r∈Icc (0:ℝ) 1)
    (hcap : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→
      deriv α r=comparisonCap N δ U L E d (α r))
    {a b : ℝ} (ha : 0≤a) (hb : b≤1) (hab : a≤b)
    (hneg : ∀r∈Ioo a b,H r<0) :
    (∫u in α a..α b,1/comparisonCap N δ U L E d u)=b-a ∧
    b-a≤(L/N^δ)*Real.log ((1+U)/U) ∧
    ∀v>0,v≤α a+U→b-a≤(α b-α a)*E/(N^δ*d^3*v^2) := by
  have hsub : Icc a b⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hb
  have hden := potential_cap_density_on_interval ha hb hcap hneg
  have hM (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      0<comparisonCap N δ U L E d u :=
    (comparisonCap_first_term (δ:=δ) hN hU hL hE hd.le hu.1).1
  have heq := cap_travel_identity hab (hα.mono hsub) (hm.mono hsub)
    (fun r hr=>hM (α r) (hαr r (hsub hr))) hden
  have htravel := cap_travel_le_total hab (hα.mono hsub) (hm.mono hsub)
    (fun r hr=>hαr r (hsub hr)) (comparisonCap_continuous N δ U L E d).continuousOn hM hden
  have hW : (∫u in (0:ℝ)..1,1/comparisonCap N δ U L E d u)≤
      (L/N^δ)*Real.log ((1+U)/U) := by
    simpa only [zero_add] using comparisonCap_log_travel (δ:=δ) hN hU hL hE hd.le
      (a:=0) (b:=1) le_rfl zero_le_one
  refine ⟨heq,htravel.trans hW,?_⟩
  intro v hv hva
  rw [←heq]
  exact comparisonCap_band_travel (δ:=δ) hN hU hL hE hd hv hva
    (hαr a ⟨ha,hab.trans hb⟩).1
    (hm.monotoneOn ⟨ha,hab.trans hb⟩ ⟨ha.trans hab,hb⟩ hab)

theorem comparison_cap_comparable_band_length
    {N δ E d a b v K : ℝ} (hN : 0<N) (hd : 0<d) (hv : 0<v)
    (hE : 0≤E) (hwidth : b-a≤K*v)
    {length : ℝ} (hlen : length≤(b-a)*E/(N^δ*d^3*v^2)) :
    v*length≤K*E/(N^δ*d^3) := by
  have hden : 0<N^δ*d^3 := mul_pos (Real.rpow_pos_of_pos hN _) (pow_pos hd _)
  have hlen' := (le_div_iff₀ (mul_pos hden (pow_pos hv 2))).mp hlen
  apply (le_div_iff₀ hden).mpr
  have hwidthE := mul_le_mul_of_nonneg_right hwidth hE
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
