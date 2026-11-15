import ProteinFolding.Tetrahedral.BulkNearJointFrames

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

theorem bulkNearJointFrame_cases_2 (F : OctEdgeFrame) (hk : F.k = 2)
    (P : OctEdgeFrame → Prop)
    (h2013 : P bulkNearJointFrame2013)
    (h2031 : P bulkNearJointFrame2031)
    (h2103 : P bulkNearJointFrame2103)
    (h2130 : P bulkNearJointFrame2130)
    (h2301 : P bulkNearJointFrame2301)
    (h2310 : P bulkNearJointFrame2310)
    : P F := by
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  change k = 2 at hk
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
              exact (hkb rfl).elim
            | succ b =>
              cases b with
              | zero =>
                exact h2013
              | succ b =>
                omega
      | succ a =>
        cases a with
        | zero =>
          exact (hka rfl).elim
        | succ a =>
          cases a with
          | zero =>
            cases b with
            | zero =>
              exact (hjb rfl).elim
            | succ b =>
              cases b with
              | zero =>
                exact h2031
              | succ b =>
                cases b with
                | zero =>
                  exact (hkb rfl).elim
                | succ b =>
                  cases b with
                  | zero =>
                    exact (hab rfl).elim
                  | succ b =>
                    omega
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
              exact (hkb rfl).elim
            | succ b =>
              cases b with
              | zero =>
                exact h2103
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
            cases a with
            | zero =>
              cases b with
              | zero =>
                exact h2130
              | succ b =>
                cases b with
                | zero =>
                  exact (hjb rfl).elim
                | succ b =>
                  cases b with
                  | zero =>
                    exact (hkb rfl).elim
                  | succ b =>
                    cases b with
                    | zero =>
                      exact (hab rfl).elim
                    | succ b =>
                      omega
            | succ a =>
              omega
    | succ j =>
      cases j with
      | zero =>
        exact (hkj rfl).elim
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
                exact h2301
              | succ b =>
                cases b with
                | zero =>
                  exact (hkb rfl).elim
                | succ b =>
                  cases b with
                  | zero =>
                    exact (hjb rfl).elim
                  | succ b =>
                    omega
          | succ a =>
            cases a with
            | zero =>
              cases b with
              | zero =>
                exact h2310
              | succ b =>
                cases b with
                | zero =>
                  exact (hab rfl).elim
                | succ b =>
                  cases b with
                  | zero =>
                    exact (hkb rfl).elim
                  | succ b =>
                    cases b with
                    | zero =>
                      exact (hjb rfl).elim
                    | succ b =>
                      omega
            | succ a =>
              cases a with
              | zero =>
                exact (hka rfl).elim
              | succ a =>
                cases a with
                | zero =>
                  exact (hja rfl).elim
                | succ a =>
                  omega
        | succ j =>
          omega

end ProteinFolding.Tetrahedral

