module

public import MonitorIdentity
public import HistoryLocality
public import ProfilePropagation

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

/-- The monitor identity on one history, using the same errors and prefixes
as the actual stopped process. -/
theorem history_hazard_monitor_identity {Ω : Type*} (Valid : List Ω → Prop)
    (htail : ∀ a h, Valid (a::h) → Valid h) (D : List Ω → ℝ) (H : ℕ → ℝ)
    (E : List Ω → Ω → ℝ) (w : ℕ → ℝ) (hzero : D [] = 0)
    (hstep : ∀ a h, Valid (a::h) → D (a::h) = D h*(1-H h.length)-E h a)
    (h : List Ω) (hv : Valid h) :
    pathSum (fun g a => w g.length*(E g a+H g.length*D g)) h =
      pathSum (fun g a => hazardMonitor H w g.length h.length*E g a) h := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    have hfuture : pathSum (fun g a => hazardMonitor H w g.length (h.length+1)*E g a) h =
        pathSum (fun g a => hazardMonitor H w g.length h.length*E g a) h-
          (H h.length*w h.length)*pathSum (fun g a => propagationKernel H g.length h.length*E g a) h := by
      calc
        _ = pathSum (fun g a => hazardMonitor H w g.length h.length*E g a+
            (-(H h.length*w h.length))*(propagationKernel H g.length h.length*E g a)) h := by
          apply pathSum_congr_before _ _ h.length ?_ h le_rfl
          intro g hg b
          have hs : g.length+1 ≤ h.length := by omega
          have he : hazardMonitor H w g.length (h.length+1) = hazardMonitor H w g.length h.length-
              propagationKernel H g.length h.length*H h.length*w h.length := by
            simp only [hazardMonitor,sum_Ico_succ_top hs]
            ring
          rw [he]
          ring
        _ = _ := by rw [pathSum_add,pathSum_mul]; ring
    have hlast : hazardMonitor H w h.length (h.length+1) = w h.length := by simp [hazardMonitor]
    have hd := history_defect_at_horizon Valid htail D H E hzero hstep h (htail a h hv)
    change pathSum (fun g a => w g.length*(E g a+H g.length*D g)) h+
        w h.length*(E h a+H h.length*D h) =
      pathSum (fun g a => hazardMonitor H w g.length (h.length+1)*E g a) h+
        hazardMonitor H w h.length (h.length+1)*E h a
    rw [ih (htail a h hv),hfuture,hlast,hd]
    ring

theorem profile_cell_monitor_identity {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (w : ℕ → ℝ) (h : LatinHistory n) (hv : LatinHistoryValid h) (i j : Fin n) :
    pathSum (fun g sigma => w g.length*(profileCellError P Good m g sigma i j+
      profileHazard P g.length i j*profileCellDefect P Good g i j)) h =
      pathSum (fun g sigma => hazardMonitor (fun t => profileHazard P t i j) w g.length h.length*
        profileCellError P Good m g sigma i j) h := by
  apply history_hazard_monitor_identity LatinHistoryValid (fun _ _ hh => hh.1)
    (fun g => profileCellDefect P Good g i j) (fun t => profileHazard P t i j)
    (fun g sigma => profileCellError P Good m g sigma i j) w
    (profile_fluid_defect_initial P Good i j) ?_ h hv
  intro sigma g hg
  simpa only [profileCellDefect,profileCellError,List.length_cons,sub_add_eq_sub_sub]
    using actual_profile_fluid_defect_step P Good m g sigma hg i j

end LatinonEntropy

#print axioms LatinonEntropy.profile_cell_monitor_identity
