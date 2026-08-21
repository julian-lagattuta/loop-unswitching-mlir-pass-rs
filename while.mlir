
func.func @sort(){
    %init1 = arith.constant 1 : i1
   %res = scf.while (%arg1 = %init1) : (i1) -> i1 {
  // "Before" region.
  // In a "do-while" loop, this region contains the loop body.
  %next = arith.constant 1 : i1

  // And also evaluates the condition.

  // Loop through the "after" region.
  scf.condition(%next) %next : i1

} do {
^bb0(%arg2: i1):
  // "After" region.
  // Forwards the values back to "before" region unmodified.
  scf.if %arg2{

  }else{

  }
  scf.yield %arg2 : i1
}
return
}

