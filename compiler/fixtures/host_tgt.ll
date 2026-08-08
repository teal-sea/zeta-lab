; target: the predicate mirrored (slt x,y is sgt y,x) and the multiply
; strength-reduced to a shift. Both edits are genuine identities on i8.
define i8 @f(i8 %x, i8 %y) {
entry:
  %c = icmp sgt i8 %y, %x
  %z = zext i1 %c to i8
  %m = shl i8 %x, 1
  %r = add i8 %m, %z
  ret i8 %r
}
