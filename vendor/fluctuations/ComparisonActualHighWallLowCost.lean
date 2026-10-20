module

public import ComparisonActualHighWallLowProfileMoments
public import ComparisonActualHighWallLowDensity
public import ComparisonSignedCavityTransientLowMovingDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

private theorem actual_low_error_second_le_slopes
    (n U : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (q : ℕ→FullCoordinate n→ℝ) (b h K : ℕ→ℝ) (j : ℕ) :
    nativeWholeLawErrorSecond n as q (cutLowError n U b h K) j ≤
      2*(pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun sigma=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (pairSpin as j sigma).1 (pairSpin as j sigma).2|^2) 0+
      2*(pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun sigma=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K) j
          (pairSpin as j sigma).1 (pairSpin as j sigma).2|^2) 0 := by
  have HD : cutLowError n U b h K=
      fun j x=>cutLSlope n U 1 b h K j x-cutLSlope n U 0 b h K j x := by
    funext j x
    rcases x with (x|x)|(x|x) <;>
      simp only [cutLowError,cutLSlope,fullVariance,rowInterpolationSlope,
        Sum.elim_inl,Sum.elim_inr] <;> split_ifs <;>
      simp only [Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] <;> ring
  let V:=pairClock (S:=Spin n×Bool) as j
  let F (s : ℝ) (sigma : V.Assignment):=
    ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
      (pairSpin as j sigma).1 (pairSpin as j sigma).2
  let H (sigma : V.Assignment):=
    ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) j
      (pairSpin as j sigma).1 (pairSpin as j sigma).2
  have HH sigma : H sigma=F 1 sigma-F 0 sigma := by
    dsimp only [H,F]
    rw [HD]
    simp only [ReplicaTree.coordinateProfile,sub_mul,Finset.sum_sub_distrib]
  have hpos sigma : 0≤2*|F 1 sigma|^2+2*|F 0 sigma|^2-(H sigma)^2 := by
    rw [HH]
    simp only [sq_abs]
    nlinarith only [sq_nonneg (F 1 sigma+F 0 sigma)]
  have HP:=wholeLaw_disorderExpect_nonneg (fullWeight_pos n) (fullFeature n) V ho 0 q
    (fun sigma=>2*|F 1 sigma|^2+2*|F 0 sigma|^2-(H sigma)^2) hpos 0
  change _ ≤ _
  unfold nativeWholeLawErrorSecond
  dsimp only [V,F,H] at HP
  simp only [ClockTree.disorderExpect,sub_mul,add_mul,mul_sub,mul_add,Finset.sum_sub_distrib,
    Finset.sum_add_distrib,mul_assoc,mul_left_comm,mul_comm,←Finset.mul_sum] at HP ⊢
  linarith only [HP]

theorem eventually_actual_high_wall_current_LOW_radius_bigO
    (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U j : ℕ) (l t : ℝ),U ≤ as.length → j ≤ as.length →
          partitionPoint 0 as U ≤ Ccut*M.data.d → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
            (cutLowError n U b h K) j ≤ C*M.data.d := by
  obtain ⟨C,hC,H⟩ := eventually_actual_high_wall_continuum_low_profile_moment (D:=D)
    1 (by norm_num) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U j l t hU hjlen hcut hl ht
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HK : (fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))=K := by
    rfl
  have hprofile := hj
  change ∀U l t s,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 →
    partitionPoint 0 as U ≤ Ccut*M.data.d → ∀j,j≤as.length →
    (pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h
        (fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)))
      (fun sigma=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U s b h (fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))) j
          (pairSpin as j sigma).1 (pairSpin as j sigma).2|^(2*1)) 0≤(C*M.data.d)^(2*1) at hprofile
  rw [HK] at hprofile
  have H0:=hprofile U l t 0 hl ht (by norm_num) hcut j hjlen
  have H1:=hprofile U l t 1 hl ht (by norm_num) hcut j hjlen
  have HS:=actual_low_error_second_le_slopes n U (finiteCutMasses_ordered us hus jGrid)
    (cutFullVariance n q U l t b h K) b h K j
  have Hsquare : nativeWholeLawErrorSecond n as (cutFullVariance n q U l t b h K)
      (cutLowError n U b h K) j ≤ (2*C*M.data.d)^2 := by
    norm_num only [Nat.mul_one] at H0 H1
    nlinarith only [HS,H0,H1]
  unfold nativeWholeLawErrorRadius
  exact Real.sqrt_le_iff.mpr ⟨mul_nonneg (mul_nonneg (by norm_num) hC.le) M.data.hd.le,Hsquare⟩

end OAI.SKFluctuations.Cavity
