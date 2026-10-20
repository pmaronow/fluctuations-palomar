module

public import HarmonicMovementGain

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set
open scoped BigOperators

theorem harmonic_downward_separated_gain {B t r v z e emin c y : ℝ}
    (hB : 0<B) (ht : t∈Icc (0:ℝ) 1) (hv : 0 ≤ v) (hzv : z ≤ v)
    (hc : 0<c) (hy : 0<y) (hemin : 0 ≤ emin) (he : emin ≤ e)
    (hrv : c*y ≤ r-v) (hrz : c*y ≤ r-z) :
    emin*t*c^2*y^2 ≤ e*((r-harmonicBarrierRadius B t r v)/(r-z))*(z-r)^2 := by
  have hcy : 0<c*y := mul_pos hc hy
  have hvr : v ≤ r := by linarith
  have hzr : z<r := by linarith
  have he0 : 0 ≤ e := hemin.trans he
  have hs := harmonic_downward_gain hB ht hv hvr hzv hzr he0
  have hp := mul_le_mul hrv hrz hcy.le (by linarith : 0 ≤ r-v)
  have hscaled := mul_le_mul_of_nonneg_left hp (mul_nonneg hemin ht.1)
  have heg := mul_le_mul_of_nonneg_right he
    (mul_nonneg (mul_nonneg ht.1 (by linarith : 0 ≤ r-v)) (by linarith : 0 ≤ r-z))
  have heq : emin*t*c^2*y^2=emin*t*((c*y)*(c*y)) := by ring
  rw [heq]
  have h0 : emin*t*((c*y)*(c*y)) ≤ e*t*(r-v)*(r-z) := by nlinarith
  exact h0.trans hs

theorem finite_harmonic_downward_band_gain {ι : Type*} [DecidableEq ι]
    (I J : Finset ι) (hJI : J⊆I) (w e r v z : ι→ℝ) {B t emin c y : ℝ}
    (hB : 0<B) (ht : t∈Icc (0:ℝ) 1) (hc : 0<c) (hy : 0<y) (hemin : 0 ≤ emin)
    (hw : ∀j∈I,0 ≤ w j) (he : ∀j∈I,0 ≤ e j)
    (hgeom : ∀j∈I,0 ≤ v j ∧ v j ≤ r j ∧ z j ≤ v j ∧ z j<r j)
    (hmass : c*y ≤ ∑j∈J,w j)
    (hband : ∀j∈J,emin ≤ e j ∧ c*y ≤ r j-v j ∧ c*y ≤ r j-z j) :
    emin*t*c^3*y^3 ≤
      ∑j∈I,w j*(e j*((r j-harmonicBarrierRadius B t (r j) (v j))/(r j-z j))*(z j-r j)^2) := by
  let G := fun j=>e j*((r j-harmonicBarrierRadius B t (r j) (v j))/(r j-z j))*(z j-r j)^2
  have hG (j : ι) (hj : j∈I) : 0 ≤ G j := by
    obtain ⟨hv,hvr,hzv,hzr⟩ := hgeom j hj
    have hs := harmonicBarrierRadius_displacement_bounds hB ht hv hvr
    have hdisp : 0 ≤ r j-harmonicBarrierRadius B t (r j) (v j) :=
      (mul_nonneg ht.1 (sub_nonneg.mpr hvr)).trans hs.1
    dsimp [G]
    exact mul_nonneg (mul_nonneg (he j hj) (div_nonneg hdisp (sub_pos.mpr hzr).le)) (sq_nonneg _)
  have hsum : (∑j∈J,w j)*(emin*t*c^2*y^2) ≤ ∑j∈J,w j*G j := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hgj := harmonic_downward_separated_gain hB ht (hgeom j (hJI hj)).1
      (hgeom j (hJI hj)).2.2.1 hc hy hemin (hband j hj).1 (hband j hj).2.1 (hband j hj).2.2
    exact mul_le_mul_of_nonneg_left hgj (hw j (hJI hj))
  have hcoef : 0 ≤ emin*t*c^2*y^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hemin ht.1) (sq_nonneg c)) (sq_nonneg y)
  have hmass' := mul_le_mul_of_nonneg_right hmass hcoef
  have hsubset : (∑j∈J,w j*G j) ≤ ∑j∈I,w j*G j :=
    Finset.sum_le_sum_of_subset_of_nonneg hJI (fun j hj _=>mul_nonneg (hw j hj) (hG j hj))
  have hid : (c*y)*(emin*t*c^2*y^2)=emin*t*c^3*y^3 := by ring
  rw [hid] at hmass'
  exact hmass'.trans (hsum.trans hsubset)

end OAI.SKFluctuations.LaplaceWindowFormalization
