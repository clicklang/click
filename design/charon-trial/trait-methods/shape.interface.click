// A call through `Shape` may assume this contract of any implementation.
// The receiver's type is unknown, so the contract reads no fields of `self`.
trait trait_methods::Shape {
    fn area(&self, scale: i32) -> i32 {
        requires 0 <= scale and scale <= 1000;
        ensures scale < result and result <= 3001;
    }
}
