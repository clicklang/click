function imported_twice(f: fn(Integer) -> Integer, x: Integer) -> Integer {
    f(f(x))
}

function imported_every(predicate: fn(int32) -> Prop, lo: int32, hi: int32) -> Prop {
    (lo..hi).all(predicate)
}
