entity saturating_adder(a: int<8>, b: int<8>, max: int<8>) -> int<8> {
    if a+b > max {
        max
    }
    else {
        a+b
    }
}
