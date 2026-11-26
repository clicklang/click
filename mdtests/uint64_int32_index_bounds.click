theorem exact_signed_index(wide: uint64, index: int32) {
    requires to_integer(wide) == to_integer(index);
    ensures wide <= 2147483647u64 and (wide as int32) == index by {
        have to_integer(wide) <= 2147483647 by {
            rewrite(to_integer(wide), to_integer(index));
            close();
        }
        have -2147483648 <= to_integer(wide) by {
            rewrite(to_integer(wide), to_integer(index));
            close();
        }
        have wide <= 2147483647u64 by close();
        have to_integer(wide as int32) == to_integer(wide) by close();
        have (wide as int32) == index by close();
        close();
    }
}
