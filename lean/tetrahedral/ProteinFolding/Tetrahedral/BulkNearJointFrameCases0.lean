import ProteinFolding.Tetrahedral.BulkNearJointFrames

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

theorem bulkNearJointFrame_cases_0 (F : OctEdgeFrame) (hk : F.k = 0)
    (P : OctEdgeFrame → Prop)
    (h0123 : P bulkNearJointFrame0123)
    (h0132 : P bulkNearJointFrame0132)
    (h0213 : P bulkNearJointFrame0213)
    (h0231 : P bulkNearJointFrame0231)
    (h0312 : P bulkNearJointFrame0312)
    (h0321 : P bulkNearJointFrame0321)
    : P F := by
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  change k = 0 at hk
  subst k
  rcases j with ⟨j, hj⟩
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases j with
  | zero =>
    exact (hkj rfl).elim
  | succ j =>
    cases j with
    | zero =>
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
                  cases b with
                  | zero =>
                    exact h0123
                  | succ b =>
                    omega
          | succ a =>
            cases a with
            | zero =>
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
                    exact h0132
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
          exact (hka rfl).elim
        | succ a =>
          cases a with
          | zero =>
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
                  cases b with
                  | zero =>
                    exact h0213
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
                  exact (hkb rfl).elim
                | succ b =>
                  cases b with
                  | zero =>
                    exact h0231
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
            exact (hka rfl).elim
          | succ a =>
            cases a with
            | zero =>
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
                    exact h0312
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
                  exact (hkb rfl).elim
                | succ b =>
                  cases b with
                  | zero =>
                    exact h0321
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

