class FeeRateState {
private:
    long long fee;
    int size;

public:
    bool IsEmpty() const noexcept { return size == 0; }
    long long ReadFee() const noexcept { return fee; }
    void SetFee(long long next) noexcept { fee = next; }
};
