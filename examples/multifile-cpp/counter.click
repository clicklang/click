verifying "client.cpp";
verifying "counter.cpp";

int counter_add(int& counter, int amount) {
    requires 0 <= counter and counter <= 100;
    requires 0 <= amount and amount <= 100;
    owns counter;
    ensures counter == old(counter) + amount;
    ensures result == counter;
}

int counter_double(int& counter) {
    requires 0 <= counter and counter <= 200;
    owns counter;
    ensures counter == old(counter) + old(counter);
    ensures result == counter;
}

int counter_limit() {
    ensures result == 1000;
}

int bump_then_double(int& counter) {
    requires 0 <= counter and counter <= 50;
    owns counter;
    ensures counter == (old(counter) + 1) + (old(counter) + 1);
    ensures result == counter + 1000;
}
