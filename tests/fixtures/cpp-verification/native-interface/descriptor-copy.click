verifying "copy.cpp";
int32 change(struct View value) {
 owns value.data[0..1];
 ensures result == 7;
 ensures load_int32(old(value.data)) == 9;
}
int32 probe(struct View& input) {
 views input.data; views input.size;
 owns input.data[0..1];
 requires input.size <= 2147483631;
 ensures result == old(input.size) + 16;
 ensures input.size == old(input.size);
 ensures input.data == old(input.data);
 ensures input.data[0] == 9;
} by {
    step_until(call(change, 0));
    step();
    have input.size == old(input.size) by { known(); }
    have input.data == old(input.data) by { known(); }
    have input.data[0] == 9 by { known(); }
    step_until(function.exit);
    solve();
}
