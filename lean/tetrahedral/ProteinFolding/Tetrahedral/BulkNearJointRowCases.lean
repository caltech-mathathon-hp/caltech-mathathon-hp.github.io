import ProteinFolding.Tetrahedral.BulkNearJointFrames

/-! Metadata-only elimination for the 80 joint rows. The predicate stays
abstract, so this proof never unfolds a geometric certificate. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

theorem bulkNearJointRow_cases (P : Fin 10 → Bool → Fin 4 → Prop)
    (h0f0 : P 0 false 0)
    (h0f1 : P 0 false 1)
    (h0f2 : P 0 false 2)
    (h0f3 : P 0 false 3)
    (h0t0 : P 0 true 0)
    (h0t1 : P 0 true 1)
    (h0t2 : P 0 true 2)
    (h0t3 : P 0 true 3)
    (h1f0 : P 1 false 0)
    (h1f1 : P 1 false 1)
    (h1f2 : P 1 false 2)
    (h1f3 : P 1 false 3)
    (h1t0 : P 1 true 0)
    (h1t1 : P 1 true 1)
    (h1t2 : P 1 true 2)
    (h1t3 : P 1 true 3)
    (h2f0 : P 2 false 0)
    (h2f1 : P 2 false 1)
    (h2f2 : P 2 false 2)
    (h2f3 : P 2 false 3)
    (h2t0 : P 2 true 0)
    (h2t1 : P 2 true 1)
    (h2t2 : P 2 true 2)
    (h2t3 : P 2 true 3)
    (h3f0 : P 3 false 0)
    (h3f1 : P 3 false 1)
    (h3f2 : P 3 false 2)
    (h3f3 : P 3 false 3)
    (h3t0 : P 3 true 0)
    (h3t1 : P 3 true 1)
    (h3t2 : P 3 true 2)
    (h3t3 : P 3 true 3)
    (h4f0 : P 4 false 0)
    (h4f1 : P 4 false 1)
    (h4f2 : P 4 false 2)
    (h4f3 : P 4 false 3)
    (h4t0 : P 4 true 0)
    (h4t1 : P 4 true 1)
    (h4t2 : P 4 true 2)
    (h4t3 : P 4 true 3)
    (h5f0 : P 5 false 0)
    (h5f1 : P 5 false 1)
    (h5f2 : P 5 false 2)
    (h5f3 : P 5 false 3)
    (h5t0 : P 5 true 0)
    (h5t1 : P 5 true 1)
    (h5t2 : P 5 true 2)
    (h5t3 : P 5 true 3)
    (h6f0 : P 6 false 0)
    (h6f1 : P 6 false 1)
    (h6f2 : P 6 false 2)
    (h6f3 : P 6 false 3)
    (h6t0 : P 6 true 0)
    (h6t1 : P 6 true 1)
    (h6t2 : P 6 true 2)
    (h6t3 : P 6 true 3)
    (h7f0 : P 7 false 0)
    (h7f1 : P 7 false 1)
    (h7f2 : P 7 false 2)
    (h7f3 : P 7 false 3)
    (h7t0 : P 7 true 0)
    (h7t1 : P 7 true 1)
    (h7t2 : P 7 true 2)
    (h7t3 : P 7 true 3)
    (h8f0 : P 8 false 0)
    (h8f1 : P 8 false 1)
    (h8f2 : P 8 false 2)
    (h8f3 : P 8 false 3)
    (h8t0 : P 8 true 0)
    (h8t1 : P 8 true 1)
    (h8t2 : P 8 true 2)
    (h8t3 : P 8 true 3)
    (h9f0 : P 9 false 0)
    (h9f1 : P 9 false 1)
    (h9f2 : P 9 false 2)
    (h9f3 : P 9 false 3)
    (h9t0 : P 9 true 0)
    (h9t1 : P 9 true 1)
    (h9t2 : P 9 true 2)
    (h9t3 : P 9 true 3)
    (t : Fin 10) (odd : Bool) (d : Fin 4) : P t odd d := by
  rcases t with ⟨t, ht⟩
  rcases d with ⟨d, hd⟩
  cases t with
  | zero =>
    cases odd
    ·
      cases d with
      | zero =>
        exact h0f0
      | succ d =>
        cases d with
        | zero =>
          exact h0f1
        | succ d =>
          cases d with
          | zero =>
            exact h0f2
          | succ d =>
            cases d with
            | zero =>
              exact h0f3
            | succ d =>
              omega
    ·
      cases d with
      | zero =>
        exact h0t0
      | succ d =>
        cases d with
        | zero =>
          exact h0t1
        | succ d =>
          cases d with
          | zero =>
            exact h0t2
          | succ d =>
            cases d with
            | zero =>
              exact h0t3
            | succ d =>
              omega
  | succ t =>
    cases t with
    | zero =>
      cases odd
      ·
        cases d with
        | zero =>
          exact h1f0
        | succ d =>
          cases d with
          | zero =>
            exact h1f1
          | succ d =>
            cases d with
            | zero =>
              exact h1f2
            | succ d =>
              cases d with
              | zero =>
                exact h1f3
              | succ d =>
                omega
      ·
        cases d with
        | zero =>
          exact h1t0
        | succ d =>
          cases d with
          | zero =>
            exact h1t1
          | succ d =>
            cases d with
            | zero =>
              exact h1t2
            | succ d =>
              cases d with
              | zero =>
                exact h1t3
              | succ d =>
                omega
    | succ t =>
      cases t with
      | zero =>
        cases odd
        ·
          cases d with
          | zero =>
            exact h2f0
          | succ d =>
            cases d with
            | zero =>
              exact h2f1
            | succ d =>
              cases d with
              | zero =>
                exact h2f2
              | succ d =>
                cases d with
                | zero =>
                  exact h2f3
                | succ d =>
                  omega
        ·
          cases d with
          | zero =>
            exact h2t0
          | succ d =>
            cases d with
            | zero =>
              exact h2t1
            | succ d =>
              cases d with
              | zero =>
                exact h2t2
              | succ d =>
                cases d with
                | zero =>
                  exact h2t3
                | succ d =>
                  omega
      | succ t =>
        cases t with
        | zero =>
          cases odd
          ·
            cases d with
            | zero =>
              exact h3f0
            | succ d =>
              cases d with
              | zero =>
                exact h3f1
              | succ d =>
                cases d with
                | zero =>
                  exact h3f2
                | succ d =>
                  cases d with
                  | zero =>
                    exact h3f3
                  | succ d =>
                    omega
          ·
            cases d with
            | zero =>
              exact h3t0
            | succ d =>
              cases d with
              | zero =>
                exact h3t1
              | succ d =>
                cases d with
                | zero =>
                  exact h3t2
                | succ d =>
                  cases d with
                  | zero =>
                    exact h3t3
                  | succ d =>
                    omega
        | succ t =>
          cases t with
          | zero =>
            cases odd
            ·
              cases d with
              | zero =>
                exact h4f0
              | succ d =>
                cases d with
                | zero =>
                  exact h4f1
                | succ d =>
                  cases d with
                  | zero =>
                    exact h4f2
                  | succ d =>
                    cases d with
                    | zero =>
                      exact h4f3
                    | succ d =>
                      omega
            ·
              cases d with
              | zero =>
                exact h4t0
              | succ d =>
                cases d with
                | zero =>
                  exact h4t1
                | succ d =>
                  cases d with
                  | zero =>
                    exact h4t2
                  | succ d =>
                    cases d with
                    | zero =>
                      exact h4t3
                    | succ d =>
                      omega
          | succ t =>
            cases t with
            | zero =>
              cases odd
              ·
                cases d with
                | zero =>
                  exact h5f0
                | succ d =>
                  cases d with
                  | zero =>
                    exact h5f1
                  | succ d =>
                    cases d with
                    | zero =>
                      exact h5f2
                    | succ d =>
                      cases d with
                      | zero =>
                        exact h5f3
                      | succ d =>
                        omega
              ·
                cases d with
                | zero =>
                  exact h5t0
                | succ d =>
                  cases d with
                  | zero =>
                    exact h5t1
                  | succ d =>
                    cases d with
                    | zero =>
                      exact h5t2
                    | succ d =>
                      cases d with
                      | zero =>
                        exact h5t3
                      | succ d =>
                        omega
            | succ t =>
              cases t with
              | zero =>
                cases odd
                ·
                  cases d with
                  | zero =>
                    exact h6f0
                  | succ d =>
                    cases d with
                    | zero =>
                      exact h6f1
                    | succ d =>
                      cases d with
                      | zero =>
                        exact h6f2
                      | succ d =>
                        cases d with
                        | zero =>
                          exact h6f3
                        | succ d =>
                          omega
                ·
                  cases d with
                  | zero =>
                    exact h6t0
                  | succ d =>
                    cases d with
                    | zero =>
                      exact h6t1
                    | succ d =>
                      cases d with
                      | zero =>
                        exact h6t2
                      | succ d =>
                        cases d with
                        | zero =>
                          exact h6t3
                        | succ d =>
                          omega
              | succ t =>
                cases t with
                | zero =>
                  cases odd
                  ·
                    cases d with
                    | zero =>
                      exact h7f0
                    | succ d =>
                      cases d with
                      | zero =>
                        exact h7f1
                      | succ d =>
                        cases d with
                        | zero =>
                          exact h7f2
                        | succ d =>
                          cases d with
                          | zero =>
                            exact h7f3
                          | succ d =>
                            omega
                  ·
                    cases d with
                    | zero =>
                      exact h7t0
                    | succ d =>
                      cases d with
                      | zero =>
                        exact h7t1
                      | succ d =>
                        cases d with
                        | zero =>
                          exact h7t2
                        | succ d =>
                          cases d with
                          | zero =>
                            exact h7t3
                          | succ d =>
                            omega
                | succ t =>
                  cases t with
                  | zero =>
                    cases odd
                    ·
                      cases d with
                      | zero =>
                        exact h8f0
                      | succ d =>
                        cases d with
                        | zero =>
                          exact h8f1
                        | succ d =>
                          cases d with
                          | zero =>
                            exact h8f2
                          | succ d =>
                            cases d with
                            | zero =>
                              exact h8f3
                            | succ d =>
                              omega
                    ·
                      cases d with
                      | zero =>
                        exact h8t0
                      | succ d =>
                        cases d with
                        | zero =>
                          exact h8t1
                        | succ d =>
                          cases d with
                          | zero =>
                            exact h8t2
                          | succ d =>
                            cases d with
                            | zero =>
                              exact h8t3
                            | succ d =>
                              omega
                  | succ t =>
                    cases t with
                    | zero =>
                      cases odd
                      ·
                        cases d with
                        | zero =>
                          exact h9f0
                        | succ d =>
                          cases d with
                          | zero =>
                            exact h9f1
                          | succ d =>
                            cases d with
                            | zero =>
                              exact h9f2
                            | succ d =>
                              cases d with
                              | zero =>
                                exact h9f3
                              | succ d =>
                                omega
                      ·
                        cases d with
                        | zero =>
                          exact h9t0
                        | succ d =>
                          cases d with
                          | zero =>
                            exact h9t1
                          | succ d =>
                            cases d with
                            | zero =>
                              exact h9t2
                            | succ d =>
                              cases d with
                              | zero =>
                                exact h9t3
                              | succ d =>
                                omega
                    | succ t =>
                      omega

end ProteinFolding.Tetrahedral

