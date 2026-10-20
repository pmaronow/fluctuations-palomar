module

public import ComparisonActualHighOnlyLocalCapDiameter

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
namespace ActualHighOnlyOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)

theorem endpoint_mass_envelope
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (htravel : a.cavityCapTravel ≤ a.xs) :
    a.alpha.val.val c.right ≤ cu*(a.alpha.val.val c.left/cl+(Az+1)*a.xs) := by
  have hlen:=((P.cap_interval_travel c.hleft c.hlt.le c.hright c.negative).2.1).trans htravel
  have ha0 : 0 ≤ a.alpha.val.val c.left:=
    (a.radius_mass_mem ⟨c.hleft,c.hlt.le.trans c.hright⟩).1
  have hmax : a.alpha.val.val c.right ≤ cu*(max c.left a.z+a.xs) := by
    by_cases hz : a.z ≤ c.right
    · have hh:=(a.regular c.right ⟨hz,c.hright⟩).2
      exact hh.trans (mul_le_mul_of_nonneg_left
        (show c.right ≤ max c.left a.z+a.xs by linarith [le_max_left c.left a.z]) hcu.le)
    · have hh : a.alpha.val.val c.right ≤ a.alpha.val.val a.z:=
        a.alpha.val.property.2 (le_of_not_ge hz)
      have hr:=(a.regular a.z ⟨le_rfl,a.hz.2⟩).2
      exact (hh.trans hr).trans (mul_le_mul_of_nonneg_left
        (by linarith [le_max_right c.left a.z,a.hxs] : a.z ≤ max c.left a.z+a.xs) hcu.le)
  have hrad : max c.left a.z ≤ a.alpha.val.val c.left/cl+Az*a.xs := by
    by_cases ha : a.z ≤ c.left
    · rw [max_eq_left ha]
      have hp:=(a.regular c.left ⟨ha,c.hlt.le.trans c.hright⟩).1
      have hh : c.left ≤ a.alpha.val.val c.left/cl:=
        (le_div_iff₀ hcl).mpr (by simpa only [mul_comm] using hp)
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg hAz a.hxs.le))
    · rw [max_eq_right (le_of_not_ge ha)]
      exact a.hzxs.trans (le_add_of_nonneg_left (div_nonneg ha0 hcl.le))
  exact hmax.trans (mul_le_mul_of_nonneg_left (by linarith :
    max c.left a.z+a.xs ≤ a.alpha.val.val c.left/cl+(Az+1)*a.xs) hcu.le)

theorem outer_mass_floor
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (htravel : a.cavityCapTravel ≤ a.xs)
    (houter : 2*cu*(Az+1)*a.xs ≤ a.alpha.val.val c.right) :
    (cl/(2*cu))*a.alpha.val.val c.right ≤ a.alpha.val.val c.left := by
  have he:=c.endpoint_mass_envelope hcl hcu hAz htravel
  have hh : a.alpha.val.val c.right ≤ 2*cu*(a.alpha.val.val c.left/cl):=by nlinarith
  have hp:=mul_le_mul_of_nonneg_right hh hcl.le
  have hcancel : (a.alpha.val.val c.left/cl)*cl=a.alpha.val.val c.left:=div_mul_cancel₀ _ hcl.ne'
  rw [mul_assoc,hcancel] at hp
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) hcu)).mpr
  nlinarith

theorem outer_local_radius_travel
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (htravel : a.cavityCapTravel ≤ a.xs)
    (houter : 2*cu*(Az+1)*a.xs ≤ a.alpha.val.val c.right)
    {v : ℝ} (hv : 0 < v) (hvB : v ≤ a.alpha.val.val c.right)
    (hAmax : a.alpha.val.val c.left ≤ 4*v) :
    c.right-c.left ≤ (32*cu^3/cl^3)*a.data.E/(a.data.N^delta*a.data.d^3*v) := by
  have hfloor:=c.outer_mass_floor hcl hcu hAz htravel houter
  have hBmax : a.alpha.val.val c.right ≤ (8*cu/cl)*v := by
    have hh:=hfloor.trans hAmax
    have hc : 0 < cl/(2*cu):=div_pos hcl (mul_pos (by norm_num) hcu)
    have hb : a.alpha.val.val c.right ≤ (4*v)/(cl/(2*cu)):=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)
    convert hb using 1
    field_simp [hcl.ne',hcu.ne']; ring
  let vfloor:=(cl/(2*cu))*v
  have hvf : 0 < vfloor:=mul_pos (div_pos hcl (mul_pos (by norm_num) hcu)) hv
  have hvfa : vfloor ≤ a.alpha.val.val c.left+a.data.U := by
    have hh:=(mul_le_mul_of_nonneg_left hvB (div_pos hcl (mul_pos (by norm_num) hcu)).le).trans hfloor
    exact hh.trans (le_add_of_nonneg_right a.data.hU.le)
  have ht:=(P.cap_interval_travel c.hleft c.hlt.le c.hright c.negative).2.2 vfloor hvf hvfa
  have hA0:=(a.radius_mass_mem ⟨c.hleft,c.hlt.le.trans c.hright⟩).1
  have hwidth : a.alpha.val.val c.right-a.alpha.val.val c.left ≤ (8*cu/cl)*v:=by linarith
  have hs:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwidth a.data.hE.le)
    (show 0 ≤ a.data.N^delta*a.data.d^3*vfloor^2 from
      mul_nonneg (mul_nonneg (Real.rpow_nonneg a.data.hN.le _) (pow_nonneg a.data.hd.le _))
        (sq_nonneg _))
  exact ht.trans (by
    convert hs using 1
    dsimp [vfloor]
    field_simp [hcl.ne',hcu.ne']; ring)

theorem radiusS_increment_outer_chosen
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (hleftContact : P.H c.left=0 ∨ c.left=0) (hrightContact : P.H c.right=0 ∨ c.right=1)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (htravel : a.cavityCapTravel ≤ a.xs)
    (houter : 2*cu*(Az+1)*a.xs ≤ a.alpha.val.val c.right)
    {v s t : ℝ} (hv : 0 < v) (hvB : v ≤ a.alpha.val.val c.right)
    (hAmax : a.alpha.val.val c.left ≤ 4*v)
    (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) (hst : s ≤ t) :
    a.radiusS t-a.radiusS s ≤ 9*Real.log a.data.N*
      min a.cavityCapTravel ((32*cu^3/cl^3)*a.data.E/(a.data.N^delta*a.data.d^3*v)) := by
  have H:=c.radiusS_increment_all hN hlog hnd hleftContact hrightContact hs ht hst
  have Hwidth:=le_min (P.cap_interval_travel c.hleft c.hlt.le c.hright c.negative).2.1
    (c.outer_local_radius_travel hcl hcu hAz htravel houter hv hvB hAmax)
  exact H.trans (mul_le_mul_of_nonneg_left Hwidth (show 0 ≤ 9*Real.log a.data.N by linarith))

end ActualHighOnlyOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
