func.func @sum(%a.0: memref<100xi32>, %b.0: memref<100xi32>, %c.0: memref<100xi32>){
    %a, %b, %c = memref.distinct_objects %a.0, %b.0, %c.0: memref<100xi32>,memref<100xi32>,memref<100xi32>
    %lb = arith.constant 0 : index 
    %step = arith.constant 1 : index
    %size = arith.constant 100 : index
    %t = arith.constant 1: i1
    %k = scf.for %iv = %lb to %size step %step iter_args(%m = %t) -> i1 {
        %b2 = scf.if %t -> i32 {
            %p = arith.constant 100: i32
            scf.yield %p : i32
        }else{
            %p = arith.constant 200: i32
            scf.yield %p : i32
        }
        %y = memref.load %b[%iv] : memref<100xi32>
        %z = arith.addi %b2, %y : i32
        memref.store %z, %c[%iv] : memref<100xi32>
        scf.yield %m : i1
    }
    %ab = arith.addi %k, %k : i1
    return
}


