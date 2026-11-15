import ProteinFolding.Tetrahedral.OctahedralZigzags

/-! The 24 literal edge frames and proof-only elimination by their finite metadata.
No frame Fintype or filtered tuple enumeration enters a joint certificate. -/

namespace ProteinFolding.Tetrahedral

def bulkNearJointFrame0123 : OctEdgeFrame :=
  ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame0132 : OctEdgeFrame :=
  ⟨0, 1, 3, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame0213 : OctEdgeFrame :=
  ⟨0, 2, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame0231 : OctEdgeFrame :=
  ⟨0, 2, 3, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame0312 : OctEdgeFrame :=
  ⟨0, 3, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame0321 : OctEdgeFrame :=
  ⟨0, 3, 2, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame1023 : OctEdgeFrame :=
  ⟨1, 0, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame1032 : OctEdgeFrame :=
  ⟨1, 0, 3, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame1203 : OctEdgeFrame :=
  ⟨1, 2, 0, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame1230 : OctEdgeFrame :=
  ⟨1, 2, 3, 0, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame1302 : OctEdgeFrame :=
  ⟨1, 3, 0, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame1320 : OctEdgeFrame :=
  ⟨1, 3, 2, 0, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame2013 : OctEdgeFrame :=
  ⟨2, 0, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame2031 : OctEdgeFrame :=
  ⟨2, 0, 3, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame2103 : OctEdgeFrame :=
  ⟨2, 1, 0, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame2130 : OctEdgeFrame :=
  ⟨2, 1, 3, 0, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame2301 : OctEdgeFrame :=
  ⟨2, 3, 0, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame2310 : OctEdgeFrame :=
  ⟨2, 3, 1, 0, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame3012 : OctEdgeFrame :=
  ⟨3, 0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame3021 : OctEdgeFrame :=
  ⟨3, 0, 2, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame3102 : OctEdgeFrame :=
  ⟨3, 1, 0, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame3120 : OctEdgeFrame :=
  ⟨3, 1, 2, 0, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame3201 : OctEdgeFrame :=
  ⟨3, 2, 0, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

def bulkNearJointFrame3210 : OctEdgeFrame :=
  ⟨3, 2, 1, 0, by decide, by decide, by decide, by decide, by decide, by decide⟩





end ProteinFolding.Tetrahedral

