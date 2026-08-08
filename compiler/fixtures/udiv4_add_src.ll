; source: r = (x udiv 4) + y  -- unsigned division
define i8 @f(i8 %x, i8 %y) {
entry:
  %m = udiv i8 %x, 4
  %r = add i8 %m, %y
  ret i8 %r
}
