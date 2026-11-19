int Shape::area(int scale) const {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result and result <= 2000;
}
