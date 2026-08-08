; source: r = (x * 2) + (x < y ? 1 : 0), all arithmetic wrapping i8
define i8 @f(i8 %x, i8 %y) {
entry:
  %c = icmp slt i8 %x, %y
  %z = zext i1 %c to i8
  %m = mul i8 %x, 2
  %r = add i8 %m, %z
  ret i8 %r
}
