module

public import SKProof.Port.OriginalQHighOnlyBridge
public import ComparisonActualHighWallThetaZeroCapOscillation
public import ComparisonActualHighWallThetaZeroCapTravelCore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem rmin_le_cavityCapTravel
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    M.data.rmin ≤ M.cavityCapTravel := by
  have hU : 0 < M.data.U := M.data.hU
  have hL : 0 < M.data.L := M.data.hL
  have hpow : 0 < M.data.N^delta := Real.rpow_pos_of_pos M.data.hN _
  have hs0 : 0 ≤ M.data.s := M.data.hs.1.le
  have hrecip := (comparisonCap_first_term (δ:=delta) M.data.hN M.data.hU
    M.data.hL M.data.hE M.data.hd.le M.data.hs.1.le).2
  change 1/M.data.M M.data.s ≤
    (M.data.L/M.data.N^delta)*(1/(M.data.s+M.data.U)) at hrecip
  have hratio : M.data.U/(M.data.s+M.data.U) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [M.data.hs.1])
  have hhalf : M.data.rmin ≤ (M.data.L/M.data.N^delta)/2 := by
    calc
      M.data.rmin = (M.data.U/2)*(1/M.data.M M.data.s) := by
        change M.data.U/(2*M.data.M M.data.s) = _
        ring
      _ ≤ (M.data.U/2)*((M.data.L/M.data.N^delta)*(1/(M.data.s+M.data.U))) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = ((M.data.L/M.data.N^delta)/2)*(M.data.U/(M.data.s+M.data.U)) := by ring
      _ ≤ ((M.data.L/M.data.N^delta)/2)*1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (M.data.L/M.data.N^delta)/2 := mul_one _
  have hU1 : M.data.U ≤ 1 := M.data.hsmall.trans M.data.hd1
  have hlog : (1:ℝ)/2 ≤ Real.log ((1+M.data.U)/M.data.U) := by
    have htwo : (2:ℝ) ≤ (1+M.data.U)/M.data.U :=
      (le_div_iff₀ M.data.hU).mpr (by linarith only [hU1])
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at H
    exact H.trans (Real.log_le_log (by norm_num) htwo)
  exact hhalf.trans (by
    change (M.data.L/M.data.N^delta)/2 ≤
      (M.data.L/M.data.N^delta)*Real.log ((1+M.data.U)/M.data.U)
    simpa only [div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ M.data.L/M.data.N^delta))

namespace ShiftedCapInterval
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {P : Q.Potential} (c : ShiftedCapInterval Q P)

def WallGate : Prop :=
  c.left = Q.data.rmin → Q.data.rmin ≤ 2*(c.right-c.left)

theorem wallGate_of_left_ne (h : c.left ≠ Q.data.rmin) : c.WallGate := by
  intro hleft
  exact (h hleft).elim

theorem wallGate_of_unit_mass
    (hmass : Q.data.U ≤ Q.alpha.val.val c.right-Q.alpha.val.val c.left) :
    c.WallGate := by
  intro hinitial
  have hleft : Q.alpha.val.val c.left = Q.data.s := by
    rw [hinitial]
    exact Q.alpha.property.1
  have hmass : Q.data.U ≤ Q.alpha.val.val c.right-Q.data.s := by
    simpa only [hleft] using hmass
  let u:=Q.data.s+Q.data.U
  let t:=Q.sweepRadius u
  have hu : u∈Icc Q.data.s 1 :=
    ⟨by dsimp only [u]; linarith [Q.data.hU],by
      dsimp only [u]
      linarith [(Q.alpha.val.property.1 c.right).2]⟩
  have ht : t∈Icc Q.data.rmin 1 := Q.sweepRadius_bounds u
  have htα : Q.alpha.val.val t=u := Q.sweepRadius_spec hu
  have htr : t≤c.right := by
    have h:=Q.sweepRadius_monotone
      (show u≤Q.alpha.val.val c.right by dsimp only [u]; linarith)
    rw [Q.sweepRadius_inverse ⟨c.hleft.trans c.hlt.le,c.hright⟩] at h
    exact h
  have hinc : u-Q.data.s≤Q.data.M u*(t-Q.data.rmin) := by
    have h:=(Q.alpha.property.2.2 Q.data.rmin ⟨le_rfl,Q.data.hr⟩ t ht ht.1).2
    rw [Q.alpha.property.1,htα] at h
    apply h.trans
    calc
      (∫q in Q.data.rmin..t,Q.data.M (Q.alpha.val.val q))≤
          ∫q in Q.data.rmin..t,Q.data.M u := by
        apply intervalIntegral.integral_mono_on ht.1
        · exact (show Monotone (fun q=>Q.data.M (Q.alpha.val.val q)) from
            fun q v hqv=>Q.data.hm (Q.alpha.val.property.1 q)
              (Q.alpha.val.property.1 v) (Q.alpha.val.property.2 hqv)).intervalIntegrable
        · exact intervalIntegrable_const
        · intro q hq
          rw [←htα]
          exact Q.data.hm (Q.alpha.val.property.1 q) (Q.alpha.val.property.1 t)
            (Q.alpha.val.property.2 hq.2)
      _=Q.data.M u*(t-Q.data.rmin) := by simp only [intervalIntegral.integral_const,smul_eq_mul]; ring
  have hMs : 0<Q.data.M Q.data.s :=
    (comparisonCap_first_term (δ:=delta) Q.data.hN Q.data.hU Q.data.hL
      Q.data.hE Q.data.hd.le Q.data.hs.1.le).1
  have hratio : Q.data.M u≤4*Q.data.M Q.data.s := by
    have h:=comparisonCap_comparable_density (δ:=delta) Q.data.hN Q.data.hU
      Q.data.hL Q.data.hE Q.data.hd.le Q.data.hs.1.le (Q.data.hs.1.le.trans hu.1)
      (by norm_num : (1:ℝ)≤2)
      (show u+Q.data.U≤2*(Q.data.s+Q.data.U) by dsimp only [u]; linarith [Q.data.hs.1])
    norm_num at h
    simpa only [ActualHighWallData.M,concreteWallCap,ActualHighWallData.N,Nat.cast_add,Nat.cast_one] using h
  have hrad : 2*Q.data.M Q.data.s*Q.data.rmin=Q.data.U := by
    change 2*Q.data.M Q.data.s*(Q.data.U/(2*Q.data.M Q.data.s))=Q.data.U
    field_simp
  have hM0 : 0≤Q.data.M u := hMs.le.trans (Q.data.hm
    ⟨Q.data.hs.1.le,Q.data.hs1⟩ ⟨Q.data.hs.1.le.trans hu.1,hu.2⟩ hu.1)
  have htop:=mul_le_mul_of_nonneg_left (sub_le_sub_right htr Q.data.rmin) hM0
  have hfour:=mul_le_mul_of_nonneg_right hratio (by linarith [c.hlt] : 0≤c.right-Q.data.rmin)
  rw [hinitial]
  apply (mul_le_mul_iff_right₀ hMs).mp
  dsimp only [u] at hinc
  nlinarith only [hinc,htop,hfour,hrad]

theorem wallGate_of_overlap {ag zg : ℝ} (hag : 3*Q.data.rmin ≤ 2*ag)
    (hoverlap : max c.left ag < min c.right zg) : c.WallGate := by
  intro hleft
  have har : ag < c.right :=
    (le_max_right c.left ag).trans_lt (hoverlap.trans_le (min_le_left c.right zg))
  rw [hleft]
  linarith only [hag,har]

theorem rmin_lt_left_of_outer (hcl : 0 < cl) (hcu : 0 < cu)
    (htravel : Q.cavityCapTravel ≤ Q.xs)
    (houter : 2*cu*(Az+1)*Q.xs ≤ Q.alpha.val.val c.right) :
    Q.data.rmin < c.left := by
  have hAzxs : Q.data.rmin ≤ Az*Q.xs := Q.hz.1.trans Q.hzxs
  have hAz : 0 < Az := (mul_pos_iff_of_pos_right Q.hxs).mp
    (Q.data.hrbounds.1.trans_le hAzxs)
  have hzright : Q.z ≤ c.right := by
    by_contra h
    have hα : Q.alpha.val.val c.right ≤ Q.alpha.val.val Q.z :=
      Q.alpha.val.property.2 (le_of_not_ge h)
    have hzα : Q.alpha.val.val Q.z ≤ cu*Q.z :=
      (Q.regular Q.z ⟨le_rfl,Q.hz.2⟩).2
    have hcuAz : 0 < cu*(Az+2)*Q.xs :=
      mul_pos (mul_pos hcu (by linarith only [hAz])) Q.hxs
    have hmul := mul_le_mul_of_nonneg_left Q.hzxs hcu.le
    nlinarith only [houter,hα,hzα,hmul,hcuAz]
  have hright : 2*(Az+1)*Q.xs ≤ c.right := by
    have hα := (Q.regular c.right ⟨hzright,c.hright⟩).2
    apply (mul_le_mul_iff_right₀ hcu).mp
    nlinarith only [houter,hα]
  have hwidth : c.right-c.left ≤ Q.xs :=
    ((P.cap_interval_travel Q c.hleft c.hlt.le c.hright c.negative).2.1).trans htravel
  have hclxs : 0 < cl*Q.xs := mul_pos hcl Q.hxs
  nlinarith only [hAzxs,hright,hwidth,Q.hxs,hAz,hclxs]

theorem left_ne_rmin_of_mass_floor {v : ℝ} (hv : Q.data.s+Q.data.U < v)
    (hleft : v ≤ Q.alpha.val.val c.left+Q.data.U) : c.left ≠ Q.data.rmin := by
  intro hwall
  rw [hwall,Q.alpha.property.1] at hleft
  exact (not_le_of_gt hv) hleft

theorem radiusS_increment_all_gated
    (hN : 1 ≤ Q.data.N) (hlog : 1 ≤ Real.log Q.data.N)
    (hnd : 1/Q.data.N ≤ Q.data.d)
    (hleft : P.H c.left=0 ∨ c.left=Q.data.rmin)
    (hright : P.H c.right=0 ∨ c.right=1) (hgate : c.WallGate)
    {s t : ℝ} (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) (hst : s≤t) :
    Q.radiusS t-Q.radiusS s ≤ 9*Real.log Q.data.N*(c.right-c.left) := by
  rcases hleft with hcontact | hwall
  · exact c.interior_radiusS_increment hN hlog hnd hcontact hright hs ht hst
  · have hwidth : Q.data.rmin ≤ 2*(c.right-c.left) := hgate hwall
    have hinc := c.initial_radiusS_increment hwall hright hs ht
    have hnonneg : 0 ≤ c.right-c.left := sub_nonneg.mpr c.hlt.le
    have hlarge := mul_le_mul_of_nonneg_right
      (show (3:ℝ) ≤ 9*Real.log Q.data.N by linarith only [hlog]) hnonneg
    linarith only [hwidth,hinc,hlarge]

end ShiftedCapInterval
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
