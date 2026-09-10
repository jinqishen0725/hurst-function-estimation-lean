import Mathlib.Data.List.Basic
/-! Coverage metadata only. An entry is not a proof of its paper claim. -/
namespace Hurst.Index
inductive ResultId where
  | r3_1
  | r3_2
  | r3_3
  | r3_4
  | r3_5
  | r4_1
  | r4_2
  | r4_3
  | r8_1
  | r8_2
  | r8_3
  | r8_4
  | r8_5
  | rS_1_1
  | rS_1_2
  | rS_2_1
  | rS_2_2
  | rS_2_3
  | rS_3_1
  | rS_3_2
  | rS_3_3
  | rS_3_4
  | rS_5_1
  | rS_5_2
  | rS_6_1
  | rS_7_1
  | rS_7_2
  deriving DecidableEq, Repr

def allResults : List ResultId := [
  .r3_1,
  .r3_2,
  .r3_3,
  .r3_4,
  .r3_5,
  .r4_1,
  .r4_2,
  .r4_3,
  .r8_1,
  .r8_2,
  .r8_3,
  .r8_4,
  .r8_5,
  .rS_1_1,
  .rS_1_2,
  .rS_2_1,
  .rS_2_2,
  .rS_2_3,
  .rS_3_1,
  .rS_3_2,
  .rS_3_3,
  .rS_3_4,
  .rS_5_1,
  .rS_5_2,
  .rS_6_1,
  .rS_7_1,
  .rS_7_2
]

theorem indexed_count : allResults.length = 27 := by decide
theorem indexed_unique : allResults.Nodup := by decide
theorem indexed_complete (r : ResultId) : r ∈ allResults := by cases r <;> decide
end Hurst.Index
