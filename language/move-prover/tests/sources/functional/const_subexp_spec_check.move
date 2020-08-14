module TestConstantSubexpressionSpecCheck {
    spec module {
        pragma verify = false;
        pragma const_sub_exp = true;
    }

    resource struct T {
        x: u64,
    }

    /// Should catch the true expressions.
    public fun f1_incorrect(x: u64): u64 {
        x
    }
    spec fun f1_incorrect {
        requires x < 5;
        requires true;
        requires true ==> x < 5;
    }

    /// Should catch contradictory expression.
    public fun f2_incorrect(x: u64): u64 {
        x
    }
    spec fun f2_incorrect {
        ensures (x < 5 && x > 5) ==> x < 5;
    }

    /// Should catch redundant x < 3 conditions.
    public fun f3_incorrect(x: u64): u64 {
        x + x
    }
    spec fun f3_incorrect {
        requires x < 5;
        ensures result < 10;
        ensures x < 3 ==> result < 6;
        ensures x < 3 ==> result < 0;
    }

    /// Should assume false at the third requires and the
    /// specification check should catch that.
    public fun f4_incorrect(x: u64): u64 {
        x + x
    }
    spec fun f4_incorrect {
        requires x < 5;
        requires x > 3;
        requires x != 4;    // assume false
        requires x == 4;    // asserts true
        // ensures result == x + x;
    }

    /// No errors should occur.
    /// Preconditions aren't contradictory.
    public fun f5(x: u64): u64 {
        x
    }
    spec fun f5 {
        requires x < 5;
        requires x > 3;
    }

}
