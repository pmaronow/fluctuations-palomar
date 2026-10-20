module

public import PhysicalRetainedBFieldBand
public import WallSampledFieldGap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin ≤ 1) (hs1 : s ≤ 1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

theorem wallOrderedPathB_dyadic_band_le {T ε θ d v A : ℝ} (n dim : ℕ)
    (e : Fin (dim+1) ≃ FeatureIndex (n+1))
    (hs : 0 < s) (hlogn : 1 ≤ Real.log ((n+1:ℕ):ℝ))
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Ioc (0:ℝ) 1)
    (hd : d ≠ 0) (hrmin : 0 < rmin)
    (hvτ : 4*((n+1:ℕ):ℝ)^(-(10:ℝ)) ≤ v) (hvs : v ≤ s/2)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin=d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r∈Icc rmin 1, g r≤d^2)
    (α : inverseIntegralConstraints rmin s k M) (hA : 0 ≤ A) :
    let B := fun u => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u).toNNReal
    let F := fun u => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
      (((n+1:ℕ):ℝ)^(-(10:ℝ))) d α u).toNNReal
    orderedPathS (n+1) B F (s-v/4)<A →
    (∫ u in (s-v)..(s-v/2), orderedPathB (n+1) B F u) ≤
      2*v*A^2+28600*A*Real.log ((n+1:ℕ):ℝ)/
        (((n+1:ℕ):ℝ)*θ*wallLowStrength T ε*wallLowRadius d rmin ε*s) := by
  dsimp only
  intro hmean
  let B := fun u => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u).toNNReal
  let F := fun u => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
    (((n+1:ℕ):ℝ)^(-(10:ℝ))) d α u).toNNReal
  let q := completedPathClock (n+1) B F
  have hn : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hτ : 0 < ((n+1:ℕ):ℝ)^(-(10:ℝ)) := Real.rpow_pos_of_pos hn _
  have hv : 0 < v := by linarith
  have hadm := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg hs hτ hrmin.le
    hε ⟨hθ.1.le,hθ.2⟩ hdepsilon hginitial hganti hgrmono hgbound α
  have hB : MonotoneOn B (Icc (0:ℝ) 1) :=
    fun u hu z hz huz => Real.toNNReal_mono (hadm.1 hu hz huz)
  have hF : MonotoneOn F (Icc (0:ℝ) 1) :=
    fun u hu z hz huz => Real.toNNReal_mono (hadm.2.1 hu hz huz)
  let a : PositiveMass := ⟨s-v,by linarith⟩
  let b : PositiveMass := ⟨s-v/2,by linarith⟩
  let z : PositiveMass := ⟨s-v/4,by linarith⟩
  let us : List PositiveMass := [a,b,z]
  have hua : a.val≤1 := by dsimp [a]; linarith
  have hub : b.val≤1 := by dsimp [b]; linarith
  have huz : z.val≤1 := by dsimp [z]; linarith
  have hu : ∀ u∈us, u.val≤1 := by
    intro u hu
    simp only [us,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl <;> assumption
  have hna : a∈us := by simp [us]
  have hnb : b∈us := by simp [us]
  have hnz : z∈us := by simp [us]
  have hab : a.val<b.val := by dsimp [a,b]; linarith
  have hbz : b.val<z.val := by dsimp [b,z]; linarith
  have haRange : a.val∈Icc (s-v) (s-v/4) := by dsimp [a]; constructor <;> linarith
  have hbRange : b.val∈Icc (s-v) (s-v/4) := by dsimp [b]; constructor <;> linarith
  have hvfull : v ≤ s := by linarith
  have hG : 0 < wallBandSlope T ε θ d rmin v (n+1) :=
    wallBandSlope_pos hε hθ.1 hd hrmin hv (by linarith)
  have htarget (j:ℕ) := (canonicalRetainedMass_four_ordered us hu a b z hna hnb hnz hab hbz j).2.1
  have hfuture (j:ℕ) := (canonicalRetainedMass_four_ordered us hu a b z hna hnb hnz hab hbz j).2.2.1
  have hendb (j:ℕ) := (canonicalRetainedMass_four_ordered us hu a b z hna hnb hnz hab hbz j).2.2.2.2.2.1
  have hendz (j:ℕ) := (canonicalRetainedMass_four_ordered us hu a b z hna hnb hnz hab hbz j).2.2.2.2.2.2
  have hslopeTarget (j:ℕ) : List.Forall₂
      (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
        wallBandSlope T ε θ d rmin v (n+1)*(w:ℝ) ≤ st.2 (Sum.inl 0))
      (sampleMassDurations a.val (retainedMassBand a.val b.val (finiteCutMasses us j)))
      (sampleClockSteps q a.val (retainedMassBand a.val b.val (finiteCutMasses us j))) := by
    exact wallSampledField_gap hr hs1 hc hk hkc hm hM g hg hs (by omega) hlogn hε
      ⟨hθ.1.le,hθ.2⟩ hrmin.le hvτ hvfull _ (htarget j) haRange
      (fun u hu => ⟨(htarget j).le_of_mem hu |> haRange.1.trans,
        (massOrdered_mem_le_end _ (htarget j) hu).trans ((hendb j).le.trans hbRange.2)⟩) α
  have hslopeFuture (j:ℕ) : List.Forall₂
      (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
        wallBandSlope T ε θ d rmin v (n+1)*(w:ℝ) ≤ st.2 (Sum.inl 0))
      (sampleMassDurations b.val (retainedMassBand b.val z.val (retainedMassAfter a.val (finiteCutMasses us j))))
      (sampleClockSteps q b.val (retainedMassBand b.val z.val (retainedMassAfter a.val (finiteCutMasses us j)))) := by
    exact wallSampledField_gap hr hs1 hc hk hkc hm hM g hg hs (by omega) hlogn hε
      ⟨hθ.1.le,hθ.2⟩ hrmin.le hvτ hvfull _ (hfuture j) hbRange
      (fun u hu => ⟨hbRange.1.trans ((hfuture j).le_of_mem hu),
        by simpa only [hendz j,z] using massOrdered_mem_le_end _ (hfuture j) hu⟩) α
  have hpath := physicalOrderedPathB_adjacent_field_band_le n dim e B F hB hF us hu a b z
    hna hnb hnz hab hbz hG hslopeTarget hslopeFuture hmean
  have halg := wallDyadicBand_actualMass_cost_algebra hA (by norm_num : (0:ℝ)≤0) hn hG hs hv hvs
  dsimp only at halg
  have heq : 1300*A/(((n+1:ℕ):ℝ)*wallBandSlope T ε θ d rmin v (n+1)*s*v)=
      28600*A*Real.log ((n+1:ℕ):ℝ)/
        (((n+1:ℕ):ℝ)*θ*wallLowStrength T ε*wallLowRadius d rmin ε*s) := by
    unfold wallBandSlope
    field_simp
    ring
  simp only [mul_zero,zero_mul,add_zero,zero_div,heq] at halg
  apply hpath.trans
  convert halg using 1 <;> dsimp [a,b,z] <;> ring

end
end OAI.SKFluctuations.LaplaceWindowFormalization
