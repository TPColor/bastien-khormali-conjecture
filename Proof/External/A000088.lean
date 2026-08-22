import Proof.Definitions

/-!
# OEIS A000088

The values below are imported as an external computational result from OEIS A000088,
"Number of simple graphs on n unlabeled nodes."
-/

namespace BastienKhormali

/-- The values of `g n` from OEIS A000088 that are used in the informal proof. -/
axiom a000088_values :
    g 0 = 1 ∧
    g 1 = 1 ∧
    g 2 = 2 ∧
    g 3 = 4 ∧
    g 4 = 11 ∧
    g 5 = 34 ∧
    g 6 = 156 ∧
    g 7 = 1_044 ∧
    g 8 = 12_346 ∧
    g 9 = 274_668 ∧
    g 10 = 12_005_168 ∧
    g 11 = 1_018_997_864 ∧
    g 12 = 165_091_172_592 ∧
    g 13 = 50_502_031_367_952 ∧
    g 14 = 29_054_155_657_235_488 ∧
    g 15 = 31_426_485_969_804_308_768 ∧
    g 16 = 64_001_015_704_527_557_894_928 ∧
    g 17 = 245_935_864_153_532_932_683_719_776 ∧
    g 18 = 1_787_577_725_145_611_700_547_878_190_848

end BastienKhormali
