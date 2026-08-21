func.func @sort(%a.0: memref<100xi32>, %z.0: memref<100xi32>, %event_count: index){
    %a, %z = memref.distinct_objects %a.0, %z.0:  memref<100xi32>,memref<100xi32>
    
    %lb = arith.constant 0 : index 
    %step = arith.constant 1 : index
    %bits = arith.constant 32 : index
    %ze = arith.constant 0 : i1

    %o = arith.constant 1 : i32

    %b = arith.constant 1: i1
    scf.for %iv = %lb to %bits step %step iter_args (%odd = %ze, %bit_mask=%o) -> (i1, i32){ 
        
        %size = arith.constant 100: index
        // get even count
        %even_count = scf.for %iv2 = %lb to %size step %step iter_args (%count=%lb) -> index{ 
            %x = memref.load %a[%iv2] : memref<100xi32>
            %anded = arith.andi %x, %bit_mask: i32
            %zero = arith.constant 0: i32
            %cond = arith.cmpi sgt, %anded, %zero: i32
            %new_count = scf.if %cond -> index{
                scf.yield %count : index
            }else{
                %p = arith.addi %count, %step : index
                scf.yield %p : index
            }
            scf.yield %new_count : index

        }

        scf.for %q = %lb to %size step %step iter_args (%idx0 = %lb, %idx1 = %even_count)-> (index, index){
            
            %x = scf.if %odd -> i32{
                %x = memref.load %z[%q] : memref<100xi32>
                scf.yield %x : i32
            }else{
                %x = memref.load %a[%q] : memref<100xi32>
                scf.yield %x : i32
            }
                        %anded = arith.andi %x, %bit_mask: i32
            %zero = arith.constant 0: i32
            %is_odd = arith.cmpi sgt, %anded, %zero: i32
            %new_idx0, %new_idx1 = scf.if %is_odd -> (index, index){
                scf.if %odd{
                    memref.store %x, %a[%idx1] : memref<100xi32>
                }else{
                    memref.store %x, %z[%idx1] : memref<100xi32>
                }
                %new_idx1 = arith.addi %step, %idx1 : index
                scf.yield %idx0, %new_idx1: index, index
            }else{
                scf.if %odd{
                    memref.store %x, %a[%idx0] : memref<100xi32>
                }else{
                    memref.store %x, %z[%idx0] : memref<100xi32>
                }
                %new_idx0 = arith.addi %step, %idx0 : index
                scf.yield %new_idx0, %idx1: index, index
            }

            scf.yield %new_idx0, %new_idx1: index, index
        }

        %new_odd = arith.xori %b, %odd : i1
        %new_mask = arith.shli %bit_mask,%o: i32
        scf.yield %new_odd, %new_mask  : i1, i32
        
    }
    return
}


