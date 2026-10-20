module

public import HarmonicBarrierInterpolation
public import PositiveReciprocalLipschitz

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set
open scoped NNReal

def reciprocalFloorTime (A B r : ℝ) : ℝ := A/B-A/(r+B)
def reciprocalFloorInverse (A B s : ℝ) : ℝ := A/(A/B-s)-B

theorem reciprocalFloorTime_zero (A B : ℝ) : reciprocalFloorTime A B 0=0 := by
  simp [reciprocalFloorTime]

theorem reciprocalFloorTime_one_pos {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    0<reciprocalFloorTime A B 1 := by
  unfold reciprocalFloorTime
  exact sub_pos.mpr (div_lt_div_of_pos_left hA hB (by linarith))

theorem reciprocalFloorTime_monotoneOn {A B : ℝ} (hA : 0 ≤ A) (hB : 0<B) :
    MonotoneOn (reciprocalFloorTime A B) (Icc (0:ℝ) 1) := by
  intro r hr s hs hrs
  have hR : 0<r+B := by linarith [hr.1]
  have hd := div_le_div_of_nonneg_left hA hR (by linarith : r+B ≤ s+B)
  exact sub_le_sub_left hd _

theorem reciprocalFloorTime_mem {A B r : ℝ} (hA : 0 ≤ A) (hB : 0<B)
    (hr : r∈Icc (0:ℝ) 1) : reciprocalFloorTime A B r∈Icc 0 (reciprocalFloorTime A B 1) := by
  have hm := reciprocalFloorTime_monotoneOn hA hB
  exact ⟨by simpa only [reciprocalFloorTime_zero] using hm (by norm_num) hr hr.1,
    hm hr (by norm_num) hr.2⟩

theorem reciprocalFloorInverse_left {A B r : ℝ} (hA : 0<A) (hB : 0<B) (hr : 0 ≤ r) :
    reciprocalFloorInverse A B (reciprocalFloorTime A B r)=r := by
  have hR : r+B≠0 := (by linarith : 0<r+B).ne'
  unfold reciprocalFloorTime reciprocalFloorInverse
  have he : A/B-(A/B-A/(r+B))=A/(r+B) := by ring
  rw [he]
  field_simp
  ring

theorem reciprocalFloorInverse_mem {A B s : ℝ} (hA : 0<A) (hB : 0<B)
    (hs : s∈Icc 0 (reciprocalFloorTime A B 1)) : reciprocalFloorInverse A B s∈Icc (0:ℝ) 1 := by
  have hBB : 0<1+B := by linarith
  have hdlo : A/(1+B) ≤ A/B-s := by
    have hh := hs.2
    unfold reciprocalFloorTime at hh
    linarith
  have hdhi : A/B-s ≤ A/B := by linarith [hs.1]
  have hd : 0<A/B-s := (div_pos hA hBB).trans_le hdlo
  have hlo : B ≤ A/(A/B-s) := by
    apply (le_div_iff₀ hd).mpr
    have hh := (le_div_iff₀ hB).mp hdhi
    nlinarith
  have hhi : A/(A/B-s) ≤ 1+B := by
    apply (div_le_iff₀ hd).mpr
    have hh := (div_le_iff₀ hBB).mp hdlo
    nlinarith
  unfold reciprocalFloorInverse
  constructor <;> linarith

theorem reciprocalFloorInverse_right {A B s : ℝ} (hA : 0<A) (hB : 0<B)
    (hs : s∈Icc 0 (reciprocalFloorTime A B 1)) :
    reciprocalFloorTime A B (reciprocalFloorInverse A B s)=s := by
  have hBB : 0<1+B := by linarith
  have hdlo : A/(1+B) ≤ A/B-s := by
    have hh := hs.2
    unfold reciprocalFloorTime at hh
    linarith
  have hd : A/B-s≠0 := ((div_pos hA hBB).trans_le hdlo).ne'
  unfold reciprocalFloorTime reciprocalFloorInverse
  rw [sub_add_cancel]
  field_simp
  ring

theorem reciprocalFloorTime_hasDerivAt {A B r : ℝ} (hR : r+B≠0) :
    HasDerivAt (reciprocalFloorTime A B) (reciprocalSquareFloor A B r) r := by
  have hd := (((hasDerivAt_id r).add_const B).inv hR).const_mul A
  have he := hd.const_sub (A/B)
  convert he using 1
  · ext u
    simp only [reciprocalFloorTime,div_eq_mul_inv,Pi.inv_apply,id_eq]
  · simp only [reciprocalSquareFloor,id_eq]
    ring

theorem reciprocalFloorInverse_hasDerivAt {A B s : ℝ} (hA : 0<A) (hB : 0<B)
    (hs : s∈Icc 0 (reciprocalFloorTime A B 1)) :
    HasDerivAt (reciprocalFloorInverse A B)
      (reciprocalSquareFloor A B (reciprocalFloorInverse A B s))⁻¹ s := by
  have hBB : 0<1+B := by linarith
  have hdlo : A/(1+B) ≤ A/B-s := by
    have hh := hs.2
    unfold reciprocalFloorTime at hh
    linarith
  have hd : A/B-s≠0 := ((div_pos hA hBB).trans_le hdlo).ne'
  have he := (((hasDerivAt_id s).const_sub (A/B)).inv hd).const_mul A |>.sub_const B
  convert he using 1
  · ext u
    simp only [reciprocalFloorInverse,div_eq_mul_inv,Pi.inv_apply,id_eq]
  · unfold reciprocalSquareFloor reciprocalFloorInverse
    rw [sub_add_cancel]
    simp only [id_eq]
    field_simp

theorem reciprocalFloorTime_lipschitz {A B : ℝ} (hA : 0 ≤ A) (hB : 0<B) :
    ∃C : ℝ≥0,LipschitzOnWith C (reciprocalFloorTime A B) (Icc (0:ℝ) 1) := by
  refine ⟨⟨A*(B^2)⁻¹,mul_nonneg hA (inv_nonneg.mpr (sq_nonneg B))⟩,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hi := (positiveReciprocal_lipschitzOn hB).dist_le_mul (x+B)
    (by change B ≤ x+B;linarith [hx.1]) (y+B) (by change B ≤ y+B;linarith [hy.1])
  have he : reciprocalFloorTime A B x-reciprocalFloorTime A B y=
      -A*((x+B)⁻¹-(y+B)⁻¹) := by unfold reciprocalFloorTime;rw [div_eq_mul_inv,div_eq_mul_inv];ring
  simp only [Real.dist_eq,NNReal.coe_mk] at hi ⊢
  change |(x+B)⁻¹-(y+B)⁻¹| ≤ (B^2)⁻¹*|x+B-(y+B)| at hi
  change |reciprocalFloorTime A B x-reciprocalFloorTime A B y| ≤ (A*(B^2)⁻¹)*|x-y|
  rw [he,abs_mul,abs_neg,abs_of_nonneg hA]
  have hxy : x+B-(y+B)=x-y := by ring
  rw [hxy] at hi
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi hA

theorem reciprocalFloorInverse_lipschitz {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    ∃C : ℝ≥0,LipschitzOnWith C (reciprocalFloorInverse A B)
      (Icc 0 (reciprocalFloorTime A B 1)) := by
  let D := A/(1+B)
  have hD : 0<D := div_pos hA (by linarith)
  refine ⟨⟨A*(D^2)⁻¹,by positivity⟩,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxD : D ≤ A/B-x := by have hh:=hx.2;unfold reciprocalFloorTime at hh;dsimp [D];linarith
  have hyD : D ≤ A/B-y := by have hh:=hy.2;unfold reciprocalFloorTime at hh;dsimp [D];linarith
  have hi := (positiveReciprocal_lipschitzOn hD).dist_le_mul (A/B-x) hxD (A/B-y) hyD
  have he : reciprocalFloorInverse A B x-reciprocalFloorInverse A B y=
      A*((A/B-x)⁻¹-(A/B-y)⁻¹) := by unfold reciprocalFloorInverse;rw [div_eq_mul_inv,div_eq_mul_inv];ring
  simp only [Real.dist_eq,NNReal.coe_mk] at hi ⊢
  change |(A/B-x)⁻¹-(A/B-y)⁻¹| ≤ (D^2)⁻¹*|A/B-x-(A/B-y)| at hi
  change |reciprocalFloorInverse A B x-reciprocalFloorInverse A B y| ≤ (A*(D^2)⁻¹)*|x-y|
  rw [he,abs_mul,abs_of_pos hA]
  have hxy : A/B-x-(A/B-y)=y-x := by ring
  rw [hxy,abs_sub_comm y x] at hi
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi hA.le

end OAI.SKFluctuations.LaplaceWindowFormalization
