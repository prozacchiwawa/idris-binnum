# idris-binnum

idris2 binary number representation with proofs that allow bin and nat to fully interoperate in proofs

The main exported type from Data.Bin here is

    public export data Bin = O Nat Bin | BNil

It's analogous to Nat in some ways, but is made so that each value can be represented in only one way.
You can't have unnecessary leading or trailing zeros, which makes equality and some proofs easier.

BNil terminates the number (like Z)
O (count) (bin) represents (count) zeroes followed by a 1 bit and v counting from LSB to MSB.
Here are the Nat values 0-8 in Bin:

    nat2Bin 0 => BNil           -- 0
    nat2Bin 1 => O 0 BNil       -- 0b1
    nat2Bin 2 => O 1 BNil       -- 0b10
    nat2Bin 3 => O 0 (O 0 BNil) -- 0b11
    nat2Bin 4 => O 2 BNil       -- 0b100
    nat2Bin 5 => O 0 (O 1 BNil) -- 0b101
    nat2Bin 6 => O 1 (O 0 BNil) -- 0b110
    nat2Bin 7 => O 0 (O 0 (O 0 BNil)) -- 0b111
    nat2Bin 8 => O 3 BNil       -- 0b1000
    
There is a bin2Nat that converts back:

    bin2Nat (O 3 BNil) => 8
    
There are some functions that do arithmetic on nat and more can be made:

    binAdd (O 3 BNil) (O 0 (O 0 (O 0 (O 0 BNil)))) => (O 0 (O 0 (O 0 (O 1 BNil))))
    bin2Nat (O 3 BNil) => 8
    bin2Nat (O 0 (O 0 (O 0 (O 0 BNil)))) => 15
    bin2Nat (O 0 (O 0 (O 0 (O 1 BNil)))) => 23

If idris understands the value of a nat converted to bin, it's possible to follow the value back to nat.

    testBinAddProof : (a : Bin) -> (b : Bin) -> bin2Nat (binAdd a b) = (bin2Nat a) + (bin2Nat b)
    testBinAddProof a b =
      rewrite sym (bin2NatIsReflexiveWithNat2Bin ((bin2Nat a) + (bin2Nat b))) in
      ?x
    ---
    Data.Bin.x : plus (bin2Nat a) (bin2Nat b) = plus (bin2Nat a) (bin2Nat b)
    
This and a few other proofs can do a lot of heavy lifting, allowing you to write proof code as though
bin interoperates with nat, because bins do arithmetic in ways that are friendly to nat.
