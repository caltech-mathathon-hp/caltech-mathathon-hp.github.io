import ProteinFolding.Tetrahedral.BulkNearJointFrames

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

theorem bulkNearJointFrame_cases_1 (F : OctEdgeFrame) (hk : F.k = 1)
    (P : OctEdgeFrame → Prop)
    (h1023 : P bulkNearJointFrame1023)
    (h1032 : P bulkNearJointFrame1032)
    (h1203 : P bulkNearJointFrame1203)
    (h1230 : P bulkNearJointFrame1230)
    (h1302 : P bulkNearJointFrame1302)
    (h1320 : P bulkNearJointFrame1320)
    : P F := by
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  change k = 1 at hk
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
              exact (hkb rfl).elim
            | succ b =>
              cases b with
              | zero =>
                exact (hab rfl).elim
              | succ b =>
                cases b with
                | zero =>
                  exact h1023
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
                exact (hkb rfl).elim
              | succ b =>
                cases b with
                | zero =>
                  exact h1032
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
              exact (hkb rfl).elim
            | succ b =>
              cases b with
              | zero =>
                exact (hjb rfl).elim
              | succ b =>
                cases b with
                | zero =>
                  exact h1203
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
              cases a with
              | zero =>
                cases b with
                | zero =>
                  exact h1230
                | succ b =>
                  cases b with
                  | zero =>
                    exact (hkb rfl).elim
                  | succ b =>
                    cases b with
                    | zero =>
                      exact (hjb rfl).elim
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
                exact (hkb rfl).elim
              | succ b =>
                cases b with
                | zero =>
                  exact h1302
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
                cases b with
                | zero =>
                  exact h1320
                | succ b =>
                  cases b with
                  | zero =>
                    exact (hkb rfl).elim
                  | succ b =>
                    cases b with
                    | zero =>
                      exact (hab rfl).elim
                    | succ b =>
                      cases b with
                      | zero =>
                        exact (hjb rfl).elim
                      | succ b =>
                        omega
              | succ a =>
                cases a with
                | zero =>
                  exact (hja rfl).elim
                | succ a =>
                  omega
        | succ j =>
          omega

end ProteinFolding.Tetrahedral

