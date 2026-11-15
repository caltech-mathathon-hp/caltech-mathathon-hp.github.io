import ProteinFolding.Tetrahedral.BulkNearJointFrames

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

theorem bulkNearJointFrame_cases_3 (F : OctEdgeFrame) (hk : F.k = 3)
    (P : OctEdgeFrame → Prop)
    (h3012 : P bulkNearJointFrame3012)
    (h3021 : P bulkNearJointFrame3021)
    (h3102 : P bulkNearJointFrame3102)
    (h3120 : P bulkNearJointFrame3120)
    (h3201 : P bulkNearJointFrame3201)
    (h3210 : P bulkNearJointFrame3210)
    : P F := by
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  change k = 3 at hk
  subst k
  rcases j with ⟨j, hj⟩
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases j with
  | zero =>
    cases a with
    | zero =>
      exact (hja rfl).elim
    | succ a =>
      cases a with
      | zero =>
        cases b with
        | zero =>
          exact (hjb rfl).elim
        | succ b =>
          cases b with
          | zero =>
            exact (hab rfl).elim
          | succ b =>
            cases b with
            | zero =>
              exact h3012
            | succ b =>
              cases b with
              | zero =>
                exact (hkb rfl).elim
              | succ b =>
                omega
      | succ a =>
        cases a with
        | zero =>
          cases b with
          | zero =>
            exact (hjb rfl).elim
          | succ b =>
            cases b with
            | zero =>
              exact h3021
            | succ b =>
              cases b with
              | zero =>
                exact (hab rfl).elim
              | succ b =>
                cases b with
                | zero =>
                  exact (hkb rfl).elim
                | succ b =>
                  omega
        | succ a =>
          cases a with
          | zero =>
            exact (hka rfl).elim
          | succ a =>
            omega
  | succ j =>
    cases j with
    | zero =>
      cases a with
      | zero =>
        cases b with
        | zero =>
          exact (hab rfl).elim
        | succ b =>
          cases b with
          | zero =>
            exact (hjb rfl).elim
          | succ b =>
            cases b with
            | zero =>
              exact h3102
            | succ b =>
              cases b with
              | zero =>
                exact (hkb rfl).elim
              | succ b =>
                omega
      | succ a =>
        cases a with
        | zero =>
          exact (hja rfl).elim
        | succ a =>
          cases a with
          | zero =>
            cases b with
            | zero =>
              exact h3120
            | succ b =>
              cases b with
              | zero =>
                exact (hjb rfl).elim
              | succ b =>
                cases b with
                | zero =>
                  exact (hab rfl).elim
                | succ b =>
                  cases b with
                  | zero =>
                    exact (hkb rfl).elim
                  | succ b =>
                    omega
          | succ a =>
            cases a with
            | zero =>
              exact (hka rfl).elim
            | succ a =>
              omega
    | succ j =>
      cases j with
      | zero =>
        cases a with
        | zero =>
          cases b with
          | zero =>
            exact (hab rfl).elim
          | succ b =>
            cases b with
            | zero =>
              exact h3201
            | succ b =>
              cases b with
              | zero =>
                exact (hjb rfl).elim
              | succ b =>
                cases b with
                | zero =>
                  exact (hkb rfl).elim
                | succ b =>
                  omega
        | succ a =>
          cases a with
          | zero =>
            cases b with
            | zero =>
              exact h3210
            | succ b =>
              cases b with
              | zero =>
                exact (hab rfl).elim
              | succ b =>
                cases b with
                | zero =>
                  exact (hjb rfl).elim
                | succ b =>
                  cases b with
                  | zero =>
                    exact (hkb rfl).elim
                  | succ b =>
                    omega
          | succ a =>
            cases a with
            | zero =>
              exact (hja rfl).elim
            | succ a =>
              cases a with
              | zero =>
                exact (hka rfl).elim
              | succ a =>
                omega
      | succ j =>
        cases j with
        | zero =>
          exact (hkj rfl).elim
        | succ j =>
          omega

end ProteinFolding.Tetrahedral

