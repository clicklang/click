// One variable argument of a C call, as a variadic function's contract reads
// it: the argument's value after the default argument promotions (C11
// 6.5.2.2p6-7), so a `char` or `short` argument is an `Int`. A call passes
// its variable arguments as the contract's last parameter, `...args`, one
// `List<VarArg>` with the first argument first
// (docs/reference/language/c.md#variadic-calls).
spec enum VarArg {
    Int(int32),
    UInt(uint32),
    Long(int64),
    ULong(uint64),
}
