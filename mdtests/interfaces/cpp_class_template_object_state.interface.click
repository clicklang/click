template<class T> class Holder<T> {
    function held(this) -> T;
}
template<class T> void Holder<T>::put(T x) {
    ensures held(this) == x;
}
template<class T> T Holder<T>::get() const {
    ensures result == held(this);
}
