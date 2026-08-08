; source: r = (x * 2) + y, all arithmetic wrapping i8
define i8 @f(i8 %x, i8 %y) {
entry:
  %m = mul i8 %x, 2
  %r = add i8 %m, %y
  ret i8 %r
}
