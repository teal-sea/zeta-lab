; source: r = 1 if x < y (signed) else 0
define i8 @f(i8 %x, i8 %y) {
entry:
  %c = icmp slt i8 %x, %y
  %r = zext i1 %c to i8
  ret i8 %r
}
