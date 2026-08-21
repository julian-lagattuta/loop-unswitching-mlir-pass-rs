func.func @sum(%a.0: memref<100xi32>, %b.0: memref<100xi32>, %c.0: memref<100xi32>){
    %a, %b, %c = memref.distinct_objects %a.0, %b.0, %c.0: memref<100xi32>,memref<100xi32>,memref<100xi32>
    %lb = arith.constant 0 : index 
    %step = arith.constant 1 : index
    %size = arith.constant 100 : index
    scf.for %iv = %lb to %size step %step {
        %x = memref.load %a[%iv] : memref<100xi32>
        %y = memref.load %b[%iv] : memref<100xi32>
        %z = arith.addi %x, %y : i32
        memref.store %z, %c[%iv] : memref<100xi32>
    }
    return
}


