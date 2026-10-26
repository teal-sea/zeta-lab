module

public import RHHeight.Assembly

/-! Pins the assembly point of hunt #137 and prints its axioms. `rhHeight50_of_four` is the
target conditional on the four pieces of `RHHeight/Skeleton.lean`; it is not the target. -/

open Complex

-- Hunt #133's theorem has exactly the type the skeleton consumes.
example : RHHeight.TenZerosOnLine := HardyTenZeros.ten_zeros_on_line_below_fifty

#check @RHHeight.rhHeight50_of_four
#print axioms RHHeight.tenZerosOnLine
#print axioms RHHeight.rhHeight50_of_four
#print axioms RHHeight.zeroCount50_of_four
