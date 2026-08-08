; target: the same, with the multiply strength-reduced to a shift
define i8 @f(i8 %x, i8 %y) {
entry:
  %m = shl i8 %x, 1
  %r = add i8 %m, %y
  ret i8 %r
}
