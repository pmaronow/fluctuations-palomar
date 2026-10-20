module

public import ComparisonOuterPhysicalLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000

theorem comparison_broad_loss_normalized {U v Ko : ℝ}
    (hU : 0 < U) (hv : U ≤ v) :
    Ko^2+25*(1+v/U)*Real.log ((1+U)/U)+1 ≤
      (Ko^2+1+50*Real.log ((1+U)/U))*v/U := by
  have ht : 1 ≤ v/U := (le_div_iff₀ hU).mpr (by simpa using hv)
  have hlog : 0 ≤ Real.log ((1+U)/U) :=
    (Real.log_pos ((lt_div_iff₀ hU).mpr (by linarith))).le
  have h1 := mul_nonneg (sq_nonneg Ko) (sub_nonneg.mpr ht)
  have h2 := mul_nonneg hlog (sub_nonneg.mpr ht)
  have he : (Ko^2+1+50*Real.log ((1+U)/U))*v/U=
      (Ko^2+1+50*Real.log ((1+U)/U))*(v/U) := by ring
  rw [he]
  nlinarith

theorem comparison_broad_trace_normalization {N E U s P v rho width loss A K R W : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hUeq : U=comparisonSmallMass N E)
    (hs : 0 < s) (hP : 0 < P) (hv : 0 < v) (hrho : 0 < rho)
    (hwidth : 0 ≤ width) (hloss0 : 0 ≤ loss)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hstrength : N*s ≤ K*P) (hloss : loss ≤ A*v/U)
    (hratio : v ≤ R*rho) (hwidthBound : width ≤ W*v) :
    s*loss/(P*rho) ≤ A*K*R*E ∧
      s*loss*width/(P*rho^2) ≤ A*K*W*R^2*E := by
  have hU : 0 < U := hUeq ▸ comparisonSmallMass_pos hN hE
  have hscale : A*v/U=A*v*N*E := by rw [hUeq];unfold comparisonSmallMass;field_simp <;> ring
  rw [hscale] at hloss
  have h1 := mul_le_mul hstrength hloss hloss0 (mul_nonneg hK hP.le)
  have h2 : s*loss ≤ A*K*P*v*E := by
    apply le_of_mul_le_mul_left (a:=N) _ hN
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left hratio (show 0 ≤ A*K*P*E by positivity)
  have hbase : s*loss/(P*rho) ≤ A*K*R*E := by
    apply (div_le_iff₀ (mul_pos hP hrho)).mpr
    nlinarith
  refine ⟨hbase,?_⟩
  have hw : width/rho ≤ W*R := by
    apply (div_le_iff₀ hrho).mpr
    have hh := mul_le_mul_of_nonneg_left hratio hW
    nlinarith
  have ht := mul_le_mul hbase hw (div_nonneg hwidth hrho.le)
    (show 0 ≤ A*K*R*E by positivity)
  have he : (s*loss/(P*rho))*(width/rho)=s*loss*width/(P*rho^2) := by ring
  rw [he] at ht
  nlinarith

theorem comparison_broad_side_log_le {width cut L : ℝ}
    (hwidth : 0 < width) (hwidth1 : width ≤ 1) (hcut : 0 < cut)
    (hL : Real.log (1/cut) ≤ L) : Real.log (width/cut) ≤ L :=
  (Real.log_le_log (div_pos hwidth hcut)
    (div_le_div_of_nonneg_right hwidth1 hcut.le)).trans hL

theorem comparison_broad_weighted_trace_cost {N E U s P v rho width loss A K R W L : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hUeq : U=comparisonSmallMass N E)
    (hs : 0 < s) (hP : 0 < P) (hv : 0 < v) (hrho : 0 < rho)
    (hwidth : 0 ≤ width) (hloss0 : 0 ≤ loss)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hR : 0 ≤ R) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hstrength : N*s ≤ K*P) (hloss : loss ≤ A*v/U)
    (hratio : v ≤ R*rho) (hwidthBound : width ≤ W*v)
    {sideLog : ℝ} (hsideLog : sideLog ≤ L) :
    s*(48*(108*loss*(Real.log N)^2/(P*rho)*sideLog)+
      (66+64*L+65536*(1+L)^2)*(54*loss*(Real.log N)^2*width/(P*rho^2))) ≤
      (5184*A*K*R*(Real.log N)^2*L+
        (66+64*L+65536*(1+L)^2)*54*A*K*W*R^2*(Real.log N)^2)*E := by
  obtain ⟨hV,hT⟩ := comparison_broad_trace_normalization hN hE hUeq hs hP hv hrho
    hwidth hloss0 hA hK hR hW hstrength hloss hratio hwidthBound
  have hside := mul_le_mul_of_nonneg_left hsideLog
    (show 0 ≤ 5184*(Real.log N)^2*(s*loss/(P*rho)) by positivity)
  have hV' := mul_le_mul_of_nonneg_left hV (show 0 ≤ 5184*(Real.log N)^2*L by positivity)
  have hT' := mul_le_mul_of_nonneg_left hT
    (show 0 ≤ (66+64*L+65536*(1+L)^2)*54*(Real.log N)^2 by positivity)
  have heV : s*(48*(108*loss*(Real.log N)^2/(P*rho)*sideLog))=
      5184*(Real.log N)^2*(s*loss/(P*rho))*sideLog := by ring
  have heT : s*((66+64*L+65536*(1+L)^2)*(54*loss*(Real.log N)^2*width/(P*rho^2)))=
      (66+64*L+65536*(1+L)^2)*54*(Real.log N)^2*(s*loss*width/(P*rho^2)) := by ring
  rw [mul_add,heV,heT]
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
