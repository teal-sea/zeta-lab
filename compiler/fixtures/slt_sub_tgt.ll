; target: sign bit of (x - y) -- the classic trick, wrong when the subtract overflows
define i8 @f(i8 %x, i8 %y) {
entry:
  %d = sub i8 %x, %y
  %s = lshr i8 %d, 7
  ret i8 %s
}
