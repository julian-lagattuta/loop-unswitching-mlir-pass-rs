module {
  func.func @sort(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: index) {
    %0:2 = memref.distinct_objects %arg0, %arg1 : memref<100xi32>, memref<100xi32>
    %c0 = arith.constant 0 : index
    %c1 = arith.constant 1 : index
    %c32 = arith.constant 32 : index
    %false = arith.constant false
    %c1_i32 = arith.constant 1 : i32
    %true = arith.constant true
    %1:2 = scf.for %arg3 = %c0 to %c32 step %c1 iter_args(%arg4 = %false, %arg5 = %c1_i32) -> (i1, i32) {
      %c100 = arith.constant 100 : index
      %2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0) -> (index) {
        %6 = memref.load %0#0[%arg6] : memref<100xi32>
        %7 = arith.andi %6, %arg5 : i32
        %c0_i32 = arith.constant 0 : i32
        %8 = arith.cmpi sgt, %7, %c0_i32 : i32
        %9 = scf.if %8 -> (index) {
          scf.yield %arg7 : index
        } else {
          %10 = arith.addi %arg7, %c1 : index
          scf.yield %10 : index
        }
        scf.yield %9 : index
      }
      %3:2 = scf.if %arg4 -> (index, index) {
        %6:2 = scf.if %arg4 -> (index, index) {
          %7:2 = scf.if %arg4 -> (index, index) {
            %8:2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0, %arg8 = %2) -> (index, index) {
              %9 = memref.load %0#1[%arg6] : memref<100xi32>
              %10 = arith.andi %9, %arg5 : i32
              %c0_i32 = arith.constant 0 : i32
              %11 = arith.cmpi sgt, %10, %c0_i32 : i32
              %12:2 = scf.if %11 -> (index, index) {
                memref.store %9, %0#0[%arg8] : memref<100xi32>
                %13 = arith.addi %c1, %arg8 : index
                scf.yield %arg7, %13 : index, index
              } else {
                memref.store %9, %0#0[%arg7] : memref<100xi32>
                %13 = arith.addi %c1, %arg7 : index
                scf.yield %13, %arg8 : index, index
              }
              scf.yield %12#0, %12#1 : index, index
            }
            scf.yield %8#0, %8#1 : index, index
          } else {
            %8:2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0, %arg8 = %2) -> (index, index) {
              %9 = memref.load %0#1[%arg6] : memref<100xi32>
              %10 = arith.andi %9, %arg5 : i32
              %c0_i32 = arith.constant 0 : i32
              %11 = arith.cmpi sgt, %10, %c0_i32 : i32
              %12:2 = scf.if %11 -> (index, index) {
                memref.store %9, %0#0[%arg8] : memref<100xi32>
                %13 = arith.addi %c1, %arg8 : index
                scf.yield %arg7, %13 : index, index
              } else {
                memref.store %9, %0#1[%arg7] : memref<100xi32>
                %13 = arith.addi %c1, %arg7 : index
                scf.yield %13, %arg8 : index, index
              }
              scf.yield %12#0, %12#1 : index, index
            }
            scf.yield %8#0, %8#1 : index, index
          }
          scf.yield %7#0, %7#1 : index, index
        } else {
          %7:2 = scf.if %arg4 -> (index, index) {
            %8:2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0, %arg8 = %2) -> (index, index) {
              %9 = memref.load %0#1[%arg6] : memref<100xi32>
              %10 = arith.andi %9, %arg5 : i32
              %c0_i32 = arith.constant 0 : i32
              %11 = arith.cmpi sgt, %10, %c0_i32 : i32
              %12:2 = scf.if %11 -> (index, index) {
                memref.store %9, %0#1[%arg8] : memref<100xi32>
                %13 = arith.addi %c1, %arg8 : index
                scf.yield %arg7, %13 : index, index
              } else {
                memref.store %9, %0#0[%arg7] : memref<100xi32>
                %13 = arith.addi %c1, %arg7 : index
                scf.yield %13, %arg8 : index, index
              }
              scf.yield %12#0, %12#1 : index, index
            }
            scf.yield %8#0, %8#1 : index, index
          } else {
            %8:2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0, %arg8 = %2) -> (index, index) {
              %9 = memref.load %0#1[%arg6] : memref<100xi32>
              %10 = arith.andi %9, %arg5 : i32
              %c0_i32 = arith.constant 0 : i32
              %11 = arith.cmpi sgt, %10, %c0_i32 : i32
              %12:2 = scf.if %11 -> (index, index) {
                memref.store %9, %0#1[%arg8] : memref<100xi32>
                %13 = arith.addi %c1, %arg8 : index
                scf.yield %arg7, %13 : index, index
              } else {
                memref.store %9, %0#1[%arg7] : memref<100xi32>
                %13 = arith.addi %c1, %arg7 : index
                scf.yield %13, %arg8 : index, index
              }
              scf.yield %12#0, %12#1 : index, index
            }
            scf.yield %8#0, %8#1 : index, index
          }
          scf.yield %7#0, %7#1 : index, index
        }
        scf.yield %6#0, %6#1 : index, index
      } else {
        %6:2 = scf.if %arg4 -> (index, index) {
          %7:2 = scf.if %arg4 -> (index, index) {
            %8:2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0, %arg8 = %2) -> (index, index) {
              %9 = memref.load %0#0[%arg6] : memref<100xi32>
              %10 = arith.andi %9, %arg5 : i32
              %c0_i32 = arith.constant 0 : i32
              %11 = arith.cmpi sgt, %10, %c0_i32 : i32
              %12:2 = scf.if %11 -> (index, index) {
                memref.store %9, %0#0[%arg8] : memref<100xi32>
                %13 = arith.addi %c1, %arg8 : index
                scf.yield %arg7, %13 : index, index
              } else {
                memref.store %9, %0#0[%arg7] : memref<100xi32>
                %13 = arith.addi %c1, %arg7 : index
                scf.yield %13, %arg8 : index, index
              }
              scf.yield %12#0, %12#1 : index, index
            }
            scf.yield %8#0, %8#1 : index, index
          } else {
            %8:2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0, %arg8 = %2) -> (index, index) {
              %9 = memref.load %0#0[%arg6] : memref<100xi32>
              %10 = arith.andi %9, %arg5 : i32
              %c0_i32 = arith.constant 0 : i32
              %11 = arith.cmpi sgt, %10, %c0_i32 : i32
              %12:2 = scf.if %11 -> (index, index) {
                memref.store %9, %0#0[%arg8] : memref<100xi32>
                %13 = arith.addi %c1, %arg8 : index
                scf.yield %arg7, %13 : index, index
              } else {
                memref.store %9, %0#1[%arg7] : memref<100xi32>
                %13 = arith.addi %c1, %arg7 : index
                scf.yield %13, %arg8 : index, index
              }
              scf.yield %12#0, %12#1 : index, index
            }
            scf.yield %8#0, %8#1 : index, index
          }
          scf.yield %7#0, %7#1 : index, index
        } else {
          %7:2 = scf.if %arg4 -> (index, index) {
            %8:2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0, %arg8 = %2) -> (index, index) {
              %9 = memref.load %0#0[%arg6] : memref<100xi32>
              %10 = arith.andi %9, %arg5 : i32
              %c0_i32 = arith.constant 0 : i32
              %11 = arith.cmpi sgt, %10, %c0_i32 : i32
              %12:2 = scf.if %11 -> (index, index) {
                memref.store %9, %0#1[%arg8] : memref<100xi32>
                %13 = arith.addi %c1, %arg8 : index
                scf.yield %arg7, %13 : index, index
              } else {
                memref.store %9, %0#0[%arg7] : memref<100xi32>
                %13 = arith.addi %c1, %arg7 : index
                scf.yield %13, %arg8 : index, index
              }
              scf.yield %12#0, %12#1 : index, index
            }
            scf.yield %8#0, %8#1 : index, index
          } else {
            %8:2 = scf.for %arg6 = %c0 to %c100 step %c1 iter_args(%arg7 = %c0, %arg8 = %2) -> (index, index) {
              %9 = memref.load %0#0[%arg6] : memref<100xi32>
              %10 = arith.andi %9, %arg5 : i32
              %c0_i32 = arith.constant 0 : i32
              %11 = arith.cmpi sgt, %10, %c0_i32 : i32
              %12:2 = scf.if %11 -> (index, index) {
                memref.store %9, %0#1[%arg8] : memref<100xi32>
                %13 = arith.addi %c1, %arg8 : index
                scf.yield %arg7, %13 : index, index
              } else {
                memref.store %9, %0#1[%arg7] : memref<100xi32>
                %13 = arith.addi %c1, %arg7 : index
                scf.yield %13, %arg8 : index, index
              }
              scf.yield %12#0, %12#1 : index, index
            }
            scf.yield %8#0, %8#1 : index, index
          }
          scf.yield %7#0, %7#1 : index, index
        }
        scf.yield %6#0, %6#1 : index, index
      }
      %4 = arith.xori %true, %arg4 : i1
      %5 = arith.shli %arg5, %c1_i32 : i32
      scf.yield %4, %5 : i1, i32
    }
    return
  }
}
