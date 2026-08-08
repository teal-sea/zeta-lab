; target: arithmetic shift right -- rounds toward negative infinity, not zero
define i8 @f(i8 %x, i8 %y) {
entry:
  %m = ashr i8 %x, 1
  %r = add i8 %m, %y
  ret i8 %r
}
