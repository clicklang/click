resource Dirty(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
resource Ready(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
contract int32 Repair(int32* p) {
    consumes input: Dirty(p);
    produces output: Ready(p);
    ensures output.value == 1;
    ensures result == 0;
}
