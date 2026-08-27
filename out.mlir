module {
  func.func @read_2d(%arg0: memref<100xi32>) {
    %c0 = arith.constant 0 : index
    %c1 = arith.constant 1 : index
    %c10 = arith.constant 10 : index
    scf.for %arg1 = %c0 to %c10 step %c1 {
      scf.for %arg2 = %c0 to %c10 step %c1 {
        %c10_0 = arith.constant 10 : index
        %0 = arith.muli %arg1, %c10_0 : index
        %1 = arith.addi %0, %arg2 : index
        %2 = memref.load %arg0[%1] : memref<100xi32>
      }
    }
    return
  }
}
