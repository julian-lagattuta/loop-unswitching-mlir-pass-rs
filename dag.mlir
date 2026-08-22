module {
  func.func @dag(%x: i64, %y: i64) -> i64 {
    %c5 = arith.constant 5 : i64
    %sum = arith.addi %x, %c5 : i64
    %difference = arith.subi %y, %c5 : i64
    %product = arith.muli %sum, %difference : i64
    func.return %product : i64
  }
}
