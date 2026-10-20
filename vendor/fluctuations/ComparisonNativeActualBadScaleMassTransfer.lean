module

public import ComparisonNativeActualBadScaleMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapContext
variable {n : ℕ} {delta : ℝ}

theorem profile_le_mass_iff_radius_le (c : NativeOverlapContext n delta)
    (alpha : c.Profile) {r u : ℝ} (hr : r∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    alpha.val.val r ≤ u ↔ r ≤ c.R alpha u := by
  constructor
  · intro h
    have H := comparisonSweepQuantile_monotone c.hc c.hk c.hkc c.hm c.hM alpha h
    simpa only [comparisonSweepQuantile_inverse c.hc c.hk c.hkc c.hm c.hM alpha hr] using H
  · intro h
    have H := alpha.val.property.2 h
    simpa only [R,comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM alpha hu] using H

theorem mass_le_profile_iff_radius_le (c : NativeOverlapContext n delta)
    (alpha : c.Profile) {r u : ℝ} (hr : r∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    u ≤ alpha.val.val r ↔ c.R alpha u ≤ r := by
  constructor
  · intro h
    have H := comparisonSweepQuantile_monotone c.hc c.hk c.hkc c.hm c.hM alpha h
    simpa only [comparisonSweepQuantile_inverse c.hc c.hk c.hkc c.hm c.hM alpha hr] using H
  · intro h
    have H := alpha.val.property.2 h
    simpa only [R,comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM alpha hu] using H

theorem physical_mass_mem_profile_interval_iff (c : NativeOverlapContext n delta)
    (alpha : c.Profile) {a b u : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    u∈Icc (alpha.val.val a) (alpha.val.val b) ↔ c.R alpha u∈Icc a b := by
  exact and_congr (c.profile_le_mass_iff_radius_le alpha ha hu)
    (c.mass_le_profile_iff_radius_le alpha hb hu)

theorem radius_mem_physical_interval_iff (c : NativeOverlapContext n delta)
    (alpha : c.Profile) {a b r : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1) :
    r∈Icc (c.R alpha a) (c.R alpha b) ↔ alpha.val.val r∈Icc a b := by
  exact and_congr (c.mass_le_profile_iff_radius_le alpha hr ha).symm
    (c.profile_le_mass_iff_radius_le alpha hr hb).symm

theorem bad_radius_iff_bad_physical_mass (c : NativeOverlapContext n delta)
    (alpha : c.Profile) {cl cu r : ℝ} (hcl : 0 < cl) (hcu : 0 < cu)
    (hr : r∈Icc (0:ℝ) 1) :
    (alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) ↔
      (c.R alpha (alpha.val.val r) < alpha.val.val r/cu ∨
        alpha.val.val r/cl < c.R alpha (alpha.val.val r)) := by
  have hinv := comparisonSweepQuantile_inverse c.hc c.hk c.hkc c.hm c.hM alpha hr
  change (alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) ↔
    (comparisonSweepQuantile c.hc c.hk c.hkc c.hm c.hM alpha (alpha.val.val r) < _ ∨ _ <
      comparisonSweepQuantile c.hc c.hk c.hkc c.hm c.hM alpha (alpha.val.val r))
  rw [hinv,lt_div_iff₀ hcu,div_lt_iff₀ hcl]
  constructor <;> intro h <;> rcases h with h|h
  · exact Or.inr (by nlinarith only [h])
  · exact Or.inl (by nlinarith only [h])
  · exact Or.inr (by nlinarith only [h])
  · exact Or.inl (by nlinarith only [h])

theorem bad_physical_mass_iff_bad_radius (c : NativeOverlapContext n delta)
    (alpha : c.Profile) {cl cu u : ℝ} (hcl : 0 < cl) (hcu : 0 < cu)
    (hu : u∈Icc (0:ℝ) 1) :
    (c.R alpha u < u/cu ∨ u/cl < c.R alpha u) ↔
      (alpha.val.val (c.R alpha u) < cl*c.R alpha u ∨
        cu*c.R alpha u < alpha.val.val (c.R alpha u)) := by
  have hspec : alpha.val.val (c.R alpha u)=u :=
    comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM alpha hu
  have H := c.bad_radius_iff_bad_physical_mass alpha hcl hcu
    (comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha u)
  rw [hspec] at H ⊢
  exact H.symm

theorem exists_bad_radius_iff_physical_mass_above_profile_cut
    (c : NativeOverlapContext n delta) (alpha : c.Profile)
    {cl cu r0 : ℝ} (hcl : 0 < cl) (hcu : 0 < cu) (hr0 : r0∈Icc (0:ℝ) 1) :
    (∃r∈Icc r0 1,alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) ↔
      ∃u∈Icc (alpha.val.val r0) 1,
        c.R alpha u < u/cu ∨ u/cl < c.R alpha u := by
  constructor
  · rintro ⟨r,hr,hbad⟩
    have hr01 : r∈Icc (0:ℝ) 1 := ⟨hr0.1.trans hr.1,hr.2⟩
    exact ⟨alpha.val.val r,⟨alpha.val.property.2 hr.1,(alpha.val.property.1 r).2⟩,
      (c.bad_radius_iff_bad_physical_mass alpha hcl hcu hr01).mp hbad⟩
  · rintro ⟨u,hu,hbad⟩
    have hu01 : u∈Icc (0:ℝ) 1 := ⟨(alpha.val.property.1 r0).1.trans hu.1,hu.2⟩
    exact ⟨c.R alpha u,⟨(c.profile_le_mass_iff_radius_le alpha hr0 hu01).mp hu.1,
      (comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha u).2⟩,
      (c.bad_physical_mass_iff_bad_radius alpha hcl hcu hu01).mp hbad⟩

theorem exists_bad_physical_mass_iff_radius_above_inverse_cut
    (c : NativeOverlapContext n delta) (alpha : c.Profile)
    {cl cu u0 : ℝ} (hcl : 0 < cl) (hcu : 0 < cu) (hu0 : u0∈Icc (0:ℝ) 1) :
    (∃u∈Icc u0 1,c.R alpha u < u/cu ∨ u/cl < c.R alpha u) ↔
      ∃r∈Icc (c.R alpha u0) 1,
        alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r := by
  have H := c.exists_bad_radius_iff_physical_mass_above_profile_cut alpha hcl hcu
    (comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha u0)
  have he : alpha.val.val (c.R alpha u0)=u0 :=
    comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM alpha hu0
  rw [he] at H
  exact H.symm

theorem positive_radius_profile_mem (c : NativeOverlapContext n delta)
    (alpha : c.Profile) {r : ℝ} (hr : r∈Ioc (0:ℝ) 1) :
    alpha.val.val r∈Ioc (0:ℝ) 1 := by
  refine ⟨?_,(alpha.val.property.1 r).2⟩
  by_contra hn
  have he : alpha.val.val r=0 := le_antisymm (le_of_not_gt hn) (alpha.val.property.1 r).1
  have H := comparisonSweepQuantile_inverse c.hc c.hk c.hkc c.hm c.hM alpha ⟨hr.1.le,hr.2⟩
  rw [he,comparisonSweepQuantile_zero c.hc c.hk c.hkc c.hm c.hM alpha] at H
  exact hr.1.ne H

theorem positive_mass_inverse_mem (c : NativeOverlapContext n delta)
    (alpha : c.Profile) {u : ℝ} (hu : u∈Ioc (0:ℝ) 1) :
    c.R alpha u∈Ioc (0:ℝ) 1 := by
  have hb := comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha u
  refine ⟨?_,hb.2⟩
  by_contra hn
  have he : c.R alpha u=0 := le_antisymm (le_of_not_gt hn) hb.1
  have H : alpha.val.val (c.R alpha u)=u :=
    comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM alpha ⟨hu.1.le,hu.2⟩
  rw [he,alpha.property.1] at H
  exact hu.1.ne H

theorem regular_radius_iff_physical_mass_above_profile_cut
    (c : NativeOverlapContext n delta) (alpha : c.Profile)
    {cl cu r0 : ℝ} (hcl : 0 < cl) (hcu : 0 < cu) (hr0 : r0∈Icc (0:ℝ) 1) :
    (∀r∈Icc r0 1,cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) ↔
      ∀u∈Icc (alpha.val.val r0) 1,u/cu ≤ c.R alpha u ∧ c.R alpha u ≤ u/cl := by
  constructor
  · intro H u hu
    have hu01 : u∈Icc (0:ℝ) 1 := ⟨(alpha.val.property.1 r0).1.trans hu.1,hu.2⟩
    have hru : c.R alpha u∈Icc r0 1 :=
      ⟨(c.profile_le_mass_iff_radius_le alpha hr0 hu01).mp hu.1,
        (comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha u).2⟩
    have h := H _ hru
    have he : alpha.val.val (c.R alpha u)=u :=
      comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM alpha hu01
    rw [he] at h
    exact ⟨(div_le_iff₀ hcu).mpr (by nlinarith only [h.2]),
      (le_div_iff₀ hcl).mpr (by nlinarith only [h.1])⟩
  · intro H r hr
    have hr01 : r∈Icc (0:ℝ) 1 := ⟨hr0.1.trans hr.1,hr.2⟩
    have h := H (alpha.val.val r) ⟨alpha.val.property.2 hr.1,(alpha.val.property.1 r).2⟩
    have he : c.R alpha (alpha.val.val r)=r :=
      comparisonSweepQuantile_inverse c.hc c.hk c.hkc c.hm c.hM alpha hr01
    rw [he] at h
    exact ⟨by nlinarith only [(le_div_iff₀ hcl).mp h.2],
      by nlinarith only [(div_le_iff₀ hcu).mp h.1]⟩

theorem exists_bad_radius_with_regular_outer_of_physical_failure
    (c : NativeOverlapContext n delta) (alpha : c.Profile)
    {A cl cu : ℝ} (hA : 0 < A) (hcl : 0 < cl) (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu)
    (hbad : ∃u∈Icc (alpha.val.val (min A 1)) 1,
      c.R alpha u < u/cu ∨ u/cl < c.R alpha u) :
    ∃r∈Icc A 1,(alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) ∧
      ∀s∈Icc (min (2*r) 1) 1,cl*s ≤ alpha.val.val s ∧ alpha.val.val s ≤ cu*s := by
  have hcut : min A 1∈Icc (0:ℝ) 1 :=
    ⟨le_min hA.le zero_le_one,min_le_right _ _⟩
  have H := (c.exists_bad_radius_iff_physical_mass_above_profile_cut alpha hcl
    (zero_lt_one.trans_le hcu1) hcut).mpr hbad
  exact comparison_exists_bad_scale_with_regular_outer alpha.val.val hA hcl1 hcu1
    alpha.property.2.1 H

end NativeOverlapContext
end OAI.SKFluctuations.LaplaceWindowFormalization
