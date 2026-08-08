; source: r = (x sdiv 2) + y  -- signed division truncates toward zero
define i8 @f(i8 %x, i8 %y) {
entry:
  %m = sdiv i8 %x, 2
  %r = add i8 %m, %y
  ret i8 %r
}
