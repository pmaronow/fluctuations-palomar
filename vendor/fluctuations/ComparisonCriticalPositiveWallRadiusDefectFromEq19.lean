module

public import ComparisonActualHighWallRadiusSequenceDimAlong
public import ComparisonActualHighWallRadiusScalarIntegrability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 8000000

theorem critical_positive_wall_radius_defect_L1_of_mass_band
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D a b ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hca : 0 < ca)
    (hab : a ≤ b)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (ha : ∀n,(M n).data.rmin < (M n).xs*a)
    (hb : ∀n,(M n).xs*b ≤ 1)
    (hmass : ∀n,ca*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*a))
    (dphys : ℕ → ℕ) (e : ∀n,Fin (dphys n+1) ≃ FeatureIndex (dim n+1)) :
    Tendsto (fun n=>(∫r in Icc ((M n).xs*a) ((M n).xs*b),
      (M n).wallRadiusPointDefect r)/(M n).xs^3) atTop (𝓝 0) := by
  have H := actual_high_wall_radius_Eq19_dim_tendsto_zero Bclock hm hdelta hmargin
    hcl hcu hAz hC0 hCt (C:=max b 1) (ca:=ca) (le_max_right b 1) hca dim hdim M
    (fun n=>(M n).xs) (fun n=>(M n).xs*a) (fun n=>(M n).xs*b)
    ha (fun n=>mul_le_mul_of_nonneg_left hab (M n).hxs.le) hb
    (fun _=>le_rfl)
    (fun n=>by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (le_max_left b 1) (M n).hxs.le)
    hmass dphys e
  convert H using 1
  ext n
  simp only [ActualHighWallOverlapMinimum.wallRadiusDefect,
    ActualHighWallOverlapMinimum.wallRadiusPointDefect,
    ActualHighWallOverlapMinimum.radiusB,ActualHighWallOverlapMinimum.radiusS,
    integral_Icc_eq_integral_Ioo]

theorem critical_positive_wall_radius_defect_L1_of_eventual_mass_band
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D a b ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hca : 0 < ca)
    (hab : a ≤ b)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hband : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*a ∧
      (M n).xs*b ≤ 1 ∧ ca*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*a))
    (dphys : ℕ → ℕ) (e : ∀n,Fin (dphys n+1) ≃ FeatureIndex (dim n+1)) :
    Tendsto (fun n=>(∫r in Icc ((M n).xs*a) ((M n).xs*b),
      (M n).wallRadiusPointDefect r)/(M n).xs^3) atTop (𝓝 0) := by
  let good := fun n=>(M n).data.rmin < (M n).xs*a ∧
      (M n).xs*b ≤ 1 ∧ ca*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*a)
  let left := fun n=>if good n then (M n).xs*a else max (M n).z (M n).xs
  let right := fun n=>if good n then (M n).xs*b else left n
  let C:=max b (Az+1)
  let ca':=min ca cl
  have hC : 1 ≤ C :=
    (by linarith : (1:ℝ) ≤ Az+1).trans (le_max_right b (Az+1))
  have hca' : 0 < ca' := lt_min hca hcl
  have H := actual_high_wall_radius_Eq19_dim_tendsto_zero Bclock hm hdelta hmargin
    hcl hcu hAz hC0 hCt hC hca' dim hdim M (fun n=>(M n).xs) left right
    (by
      intro n
      by_cases hn:good n
      · simpa [left,hn] using hn.1
      · have Hr : (M n).data.rmin < (M n).xs := by
          have Hr0 := (M n).data.hrbounds.2.1
          rw [hfixed n]
          nlinarith [(M n).data.hd]
        simp [left,hn]
        exact Or.inr Hr)
    (by
      intro n
      by_cases hn:good n
      · simpa [left,right,hn] using
          mul_le_mul_of_nonneg_left hab (M n).hxs.le
      · simp [left,right,hn])
    (by
      intro n
      by_cases hn:good n
      · simpa [right,hn] using hn.2.1
      · simp [right,left,hn]
        exact ⟨(M n).hz.2,by rw [hfixed n];exact (M n).data.hd1⟩)
    (fun _=>le_rfl)
    (by
      intro n
      by_cases hn:good n
      · simp [right,hn]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (le_max_left b (Az+1)) (M n).hxs.le
      · simp [right,left,hn]
        constructor
        · exact (M n).hzxs.trans
            (mul_le_mul_of_nonneg_right (by dsimp [C];linarith [le_max_right b (Az+1)] : Az≤C) (M n).hxs.le)
        · simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right (by linarith : (1:ℝ)≤C) (M n).hxs.le))
    (by
      intro n
      by_cases hn:good n
      · simpa [left,hn] using
          (mul_le_mul_of_nonneg_right (min_le_left ca cl) (M n).hxs.le).trans hn.2.2
      · let r:=max (M n).z (M n).xs
        have hr : r∈Icc (M n).z 1 :=
          ⟨le_max_left _ _,max_le (M n).hz.2
            (by rw [hfixed n];exact (M n).data.hd1)⟩
        have Hreg:=((M n).regular r hr).1
        have Hleft : (M n).xs ≤ r := le_max_right _ _
        have Hmin:=mul_le_mul_of_nonneg_right (min_le_right ca cl) (M n).hxs.le
        have Hcl:=mul_le_mul_of_nonneg_left Hleft hcl.le
        simpa [left,hn] using Hmin.trans (Hcl.trans Hreg))
    dphys e
  have Heq : (fun n=>(M n).wallRadiusDefect (left n) (right n)/(M n).xs^3) =ᶠ[atTop]
      (fun n=>(∫r in Icc ((M n).xs*a) ((M n).xs*b),
        (M n).wallRadiusPointDefect r)/(M n).xs^3) := by
    filter_upwards [hband] with n hn
    have hgood : good n := hn
    simp only [left,right,ite_eq_left hgood,
      ActualHighWallOverlapMinimum.wallRadiusDefect,
      ActualHighWallOverlapMinimum.wallRadiusPointDefect,
      ActualHighWallOverlapMinimum.radiusB,ActualHighWallOverlapMinimum.radiusS,
      integral_Icc_eq_integral_Ioo]
  exact H.congr' Heq

end OAI.SKFluctuations.LaplaceWindowFormalization
