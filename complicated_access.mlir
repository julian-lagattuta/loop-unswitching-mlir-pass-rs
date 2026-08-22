module {
    func.func @complicated_access(%array: memref<233xi32>) {
        %c0 = arith.constant 0 : index
        %c1 = arith.constant 1 : index
        %c2 = arith.constant 2 : index
        %c3 = arith.constant 3 : index
        %c4 = arith.constant 4 : index
        %c5 = arith.constant 5 : index
        %c7 = arith.constant 7 : index
        %c20 = arith.constant 20 : index
        %value = arith.constant 42 : i32

        scf.for %i = %c0 to %c4 step %c1 {
            %i_squared = arith.muli %i, %i : index
            %outer_quadratic = arith.muli %c20, %i_squared : index
            %outer_linear = arith.muli %c3, %i : index
            %outer = arith.addi %outer_quadratic, %outer_linear : index
            scf.for %j = %c0 to %c5 step %c1 {
                %j_squared = arith.muli %j, %j : index
                %inner_quadratic = arith.muli %c2, %j_squared : index
                %inner = arith.addi %inner_quadratic, %j : index
                %partial = arith.addi %outer, %inner : index
                %index = arith.addi %partial, %c7 : index
                memref.store %value, %array[%index] : memref<233xi32>
                scf.yield
            }
            scf.yield
        }
        return
    }
}
