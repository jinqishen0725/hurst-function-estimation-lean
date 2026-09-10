import Hurst.ActiveSetReindex
open Set
#check Finset.card_Icc
#check Nat.card_Icc
#check Fin.card_Icc
#check Finset.card_map
#check Finset.card_le_card
#check Finset.map_subset_iff
#check Finset.coe_sort_coe
example {m : ℕ} (i j : Fin m) : (Finset.Icc i j).card = j.val + 1 - i.val := by simp
example (i j : ℕ) : (Finset.Icc i j).card = j + 1 - i := by simp
