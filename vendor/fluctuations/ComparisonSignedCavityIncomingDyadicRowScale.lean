module

public import ComparisonSignedCavityActualRadiusDyadicCover
public import CavityWeightedDyadicAbsorption

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeSavedIncomingScale (x W s r : ℝ) : ℝ :=
  savedProjectedScale x W r*savedWeightedExteriorScale x W r s/s

theorem native_saved_incoming_scale_nonneg {x W s r : ℝ}
    (hx : 0 ≤ x) (hW : 0 < W) (hs : 0 < s) (hr : 0 < r) :
    0 ≤ nativeSavedIncomingScale x W s r := by
  unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale
  positivity

theorem native_saved_incoming_scale_band_le {x W s r v : ℝ}
    (hx : 0 ≤ x) (hW : 0 < W) (hs : 0 < s) (hv : 0 < v)
    (hxW : x ≤ W) (hxs : x ≤ s) (hvr : v ≤ r) :
    nativeSavedIncomingScale x W s r ≤ W*x^2/v^2 := by
  have hr:=hv.trans_le hvr
  have H:=weighted_projected_dyadic_product_le hx hW hr hs hxW hxs
  have hB:=native_saved_incoming_scale_nonneg hx hW hs hr
  have Hmono:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.le hvr 2) hB
  apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
  have HH : r^2*nativeSavedIncomingScale x W s r ≤ W*x^2 := by
    convert H using 1
    unfold nativeSavedIncomingScale
    ring
  simpa only [mul_comm] using Hmono.trans HH

theorem native_saved_incoming_scale_le_dyadic_sum {x W s r V : ℝ}
    (hx : 0 ≤ x) (hW : 0 < W) (hs : 0 < s) (hV : 0 < V)
    (hxW : x ≤ W) (hxs : x ≤ s) (hr1 : r ≤ 1) :
    (if V ≤ r then nativeSavedIncomingScale x W s r else 0) ≤
      ∑j∈comparisonMassDyadicIndices V,
        (if V*(2:ℝ)^j ≤ r ∧ r ≤ 2*(V*(2:ℝ)^j) then (1:ℝ) else 0)*
          (W*x^2/(V*(2:ℝ)^j)^2) := by
  have hnonneg (j : ℕ) : 0 ≤
      (if V*(2:ℝ)^j ≤ r ∧ r ≤ 2*(V*(2:ℝ)^j) then (1:ℝ) else 0)*
          (W*x^2/(V*(2:ℝ)^j)^2) := by split_ifs <;> positivity
  split_ifs with hVr
  · obtain ⟨j,hlo,hhi⟩:=comparison_mass_dyadic_cover hV hVr hr1
    have H:=native_saved_incoming_scale_band_le hx hW hs
      (show 0 < V*(2:ℝ)^(j:ℕ) by positivity) hxW hxs hlo
    have Hsum:=Finset.single_le_sum (fun j _=>hnonneg j) j.property
    rw [ite_eq_left ⟨hlo,hhi.le⟩,one_mul] at Hsum
    exact H.trans Hsum
  · exact Finset.sum_nonneg (fun j _=>hnonneg j)

theorem native_list_sum_finset_sum {A : Type} (L : List A) (J : Finset ℕ)
    (F : A → ℕ → ℝ) :
    (L.map (fun a=>∑j∈J,F a j)).sum=∑j∈J,(L.map (fun a=>F a j)).sum := by
  induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.map_cons,List.sum_cons,ih,Finset.sum_add_distrib]

theorem native_finite_saved_incoming_row_le {A : Type} (L : List A)
    (weight radius : A → ℝ) {x W s V C : ℝ}
    (hw : ∀a∈L,0 ≤ weight a) (hr1 : ∀a∈L,radius a ≤ 1)
    (hx : 0 ≤ x) (hW : 0 < W) (hs : 0 < s) (hV : 0 < V)
    (hxW : x ≤ W) (hxs : x ≤ s)
    (hband : ∀j∈comparisonMassDyadicIndices V,
      (L.map (fun a=>weight a*(if V*(2:ℝ)^j ≤ radius a ∧ radius a ≤ 2*(V*(2:ℝ)^j)
        then (1:ℝ) else 0))).sum ≤ C*(V*(2:ℝ)^j)^2) :
    (L.map (fun a=>weight a*(if V ≤ radius a then nativeSavedIncomingScale x W s (radius a) else 0))).sum ≤
      C*((comparisonMassDyadicIndices V).card:ℝ)*(W*x^2) := by
  calc
    _ ≤ (L.map (fun a=>∑j∈comparisonMassDyadicIndices V,
        weight a*((if V*(2:ℝ)^j ≤ radius a ∧ radius a ≤ 2*(V*(2:ℝ)^j) then (1:ℝ) else 0)*
          (W*x^2/(V*(2:ℝ)^j)^2)))).sum := by
      apply List.sum_le_sum
      intro a ha
      simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left
        (native_saved_incoming_scale_le_dyadic_sum hx hW hs hV hxW hxs (hr1 a ha)) (hw a ha)
    _ = ∑j∈comparisonMassDyadicIndices V,
        (L.map (fun a=>weight a*(if V*(2:ℝ)^j ≤ radius a ∧ radius a ≤ 2*(V*(2:ℝ)^j)
          then (1:ℝ) else 0))).sum*(W*x^2/(V*(2:ℝ)^j)^2) := by
      rw [native_list_sum_finset_sum]
      simp only [←mul_assoc,List.sum_map_mul_right]
    _ ≤ ∑j∈comparisonMassDyadicIndices V,C*(W*x^2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hvj : 0 < V*(2:ℝ)^j:=by positivity
      have H:=mul_le_mul_of_nonneg_right (hband j hj)
        (show 0 ≤ W*x^2/(V*(2:ℝ)^j)^2 by positivity)
      apply H.trans_eq
      field_simp
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul];ring

end OAI.SKFluctuations.Cavity
