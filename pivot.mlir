

module {

func.func @pivot(%a.0: memref<16xi32>) {
  %a = memref.distinct_objects %a.0 : memref<16xi32>

  %c0 = arith.constant 0 : index
  %c1 = arith.constant 1 : index
  %c3 = arith.constant 3 : index
  %c4 = arith.constant 4 : index

  scf.for %k = %c0 to %c3 step %c1 {

    // if p <= k
    %ok = arith.cmpi ule, %p, %k : index
    scf.if %ok {
          %krow = arith.muli %k, %c4 : index

    // p = k
      %p = arith.addi %k, %c0 : index

      %prow = arith.muli %p, %c4 : index
      %dstrow = arith.addi %krow, %c4 : index
      scf.for %j = %c0 to %c4 step %c1 {
        %src_k = arith.addi %krow, %j : index
        %src_p = arith.addi %prow, %j : index
        %dst = arith.addi %dstrow, %j : index
        %vk = memref.load %a[%src_k] : memref<16xi32>
        %vp = memref.load %a[%src_p] : memref<16xi32>
        %s = arith.addi %vk, %vp : i32
        memref.store %s, %a[%dst] : memref<16xi32>
      }
    }
  }
  func.return
}

}
